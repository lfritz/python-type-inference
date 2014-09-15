-- | The actual analysis: inferring types using monotone frameworks and a
-- worklist algorithm.
module Language.Python.TypeInference.Analysis.Analysis (
    TypeInferenceResult (..),
    showResult,
    showResultWithContext,
    showEdges,
    analyze,
    Edge' -- re-exported from WorklistAlgorithm
) where

import Control.DeepSeq
import Control.Monad (when, zipWithM_)
import Data.List (find, partition)
import Data.Map (Map)
import Data.Maybe (fromMaybe, isNothing, mapMaybe)
import Data.Monoid
import Data.Set (Set)
import Language.Analysis.DFA.Lattice
import Language.Analysis.DFA.MonotoneFramework hiding (Label)
import Language.Analysis.DFA.WorklistAlgorithm
import Language.Python.TypeInference.Analysis.MapLattice
import Language.Python.TypeInference.Analysis.TFMonad
import Language.Python.TypeInference.Analysis.TypeLattice
import Language.Python.TypeInference.CFG.CFG
import Language.Python.TypeInference.Common
import Language.Python.TypeInference.Configuration
import Language.Python.TypeInference.Error
import Prelude hiding (div)
import qualified Data.Map as Map
import qualified Data.Set as Set

-- | Result of type inference: context and effect values and global lattice
-- value (if flow-insensitive analysis was used).
data TypeInferenceResult =
    TypeInferenceResult {
        tirCtxWithContext :: Map Label (LHat L),
        tirEffWithContext :: Map Label (LHat L),
        tirCtx            :: Map Label L,
        tirEff            :: Map Label L,
        tirGlobal         :: L
    }

instance NFData TypeInferenceResult where
    rnf (TypeInferenceResult a b c d e) =
        let f = Map.toList
            g = Map.toList . Map.map f
            h = Map.toList . Map.map (\(LHat x) -> g x)
        in rnf (h a, h b, g c, g d, f e)

-- | Like 'showResult', but show context and effect values separately for
-- different context values (callstrings).
showResultWithContext :: TypeInferenceResult -> String
showResultWithContext r =
    "Context values:\n"
    ++ showMap (tirCtxWithContext r) showLHat
    ++ "Effect values:\n"
    ++ showMap (tirEffWithContext r) showLHat
    ++ "Global lattice value:\n"
    ++ showL (tirGlobal r)
    where showLHat :: LHat L -> String
          showLHat (LHat m) = '\n' : showMap m showL

-- | Show context and effect values and, if flow-insensitive analysis is used,
-- the global lattice value.
showResult :: TypeInferenceResult -> String
showResult r = "Context values:\n"
            ++ showMap (tirCtx r) showL
            ++ "Effect values:\n"
            ++ showMap (tirEff r) showL
            ++ "Global lattice value:\n"
            ++ let m = tirGlobal r
               in if Map.null m
                  then "  - none -"
                  else showL m
            ++ "\n"

showMap :: Show k => Map k v -> (v -> String) -> String
showMap m showV = unlines [ show k ++ ": " ++ showV v
                          | (k, v) <- Map.toAscList m ]

-- | Show edges in human-readable multi-line format.
showEdges :: Set Edge' -> String
showEdges edges =
    let edgeList = Set.toAscList edges
        isRegular (RegularEdge _) = True
        isRegular _               = False
        isCall (CallEdge _) = True
        isCall _            = False
        isReturn (ReturnEdge _ _) = True
        isReturn _                = False
        regular  = [e | RegularEdge e  <- filter isRegular edgeList]
        call     = [e | CallEdge e     <- filter isCall edgeList]
        return   = [e | ReturnEdge _ e <- filter isReturn edgeList]
    in "Regular edges: " ++ unwords (map showEdge regular)
       ++ "\nCall edges:    " ++ unwords (map showEdge call)
       ++ "\nReturn edges:  " ++ unwords (map showEdge return)

-- | Run the analysis. Returns inferred types, the edges added during analysis
-- and the number of iterations of the worklist algorithm.
analyze :: Configuration -> CFG -> Map Identifier UnionType
        -> TypeInferenceMonad (TypeInferenceResult, Set Edge', Int)
analyze configuration cfg userSuppliedTypes =
    do mf <- createMF configuration cfg userSuppliedTypes
       let (n, m, o) = cfgWideningParameters configuration
           k         = cfgContext configuration
           justNabla = Just $ Map.unionWith $ nabla n m o
           (ctx, eff, global, addedEdges, count) =
                                  solveWithContext mf justNabla k
           ctxJoined = Map.map joinResults ctx
           effJoined = Map.map joinResults eff
       return ( TypeInferenceResult ctx eff ctxJoined effJoined global
              , addedEdges
              , count
              )

-- | Given control flow graphs for Python modules, create a monotone framework
-- for type inference.
createMF :: Configuration -> CFG -> Map Identifier UnionType
         -> TypeInferenceMonad (MonotoneFramework L)
createMF c cfg userSuppliedTypes =
    let nodes         = cfgNodes cfg
        programPoints = map fst (Map.elems nodes)
        bindings      = Set.toList $ cfgBindings cfg
        (fi, fs)      = partition (goFlowInsensitive $ cfgFiModuleScope c)
                                  bindings
        classIds      = mapMaybe f programPoints
                        where f (ClassEntry _ classId _) = Just classId
                              f _                        = Nothing
        globalCls     = map ClassIdentifier classIds
        globalInsts   = map InstanceIdentifier classIds
        globalIds     = fi
                     ++ (if cfgFiClasses c then globalCls else [])
                     ++ (if cfgFiInstances c then globalInsts else [])
        initialGlobal = Map.fromList [(i, bot) | i <- globalIds]
                        `Map.union`
                        userSuppliedTypes
        iota          = Map.fromList [(i, bot) | i <- fs]
        zeroLabel     = head (Map.keys nodes) - 1
        zeroTF        = identityTransferFunction
        zeroEdges     = Set.fromList [ (zeroLabel, i)
                                     | i <- Set.toList (cfgInitial cfg) ]
    in do tfs <- mapMapM (uncurry $ tf c) nodes
          return MonotoneFramework {
                     mfNodes = Set.insert zeroLabel (Map.keysSet nodes),
                     mfEdges = zeroEdges `Set.union` cfgEdges cfg,
                     mfExtremalNodes = Set.singleton zeroLabel,
                     mfExtremalValue = iota,
                     mfInitialGlobalValue = initialGlobal,
                     mfTransferFunctions = Map.insert zeroLabel zeroTF tfs,
                     mfFunctionTable = cfgFunctionTable cfg
                 }


-- | Create the transfer function for a node in the control flow graph.
tf :: Configuration -> ProgramPoint -> Position
   -> TypeInferenceMonad (TransferFunction L)

-- Program points that don't change the lattice.
tf _ (Expression _) _ = identity
tf _ Assert         _ = identity
tf _ Pass           _ = identity
tf _ Break          _ = identity
tf _ Continue       _ = identity
tf _ ImportCall     _ = identity

-- Simple import statement.
tf _ (ImportReturn (ModuleImport _ _ Nothing)) _ = identity

-- Import statement of the form @import ... as ...@.
tf c (ImportReturn (ModuleImport fromModule toModule (Just importAs))) _ =
    simple c $ do let ext = fromModule `Set.member` cfgExternalModules c
                      scope = (if ext then ExternalScope else ModuleScope)
                              fromModule
                      im (Name s _) | s == scope = True
                      im _                       = False
                      rename (Name _ n) = Name (ModuleScope importAs) n
                  imported <- (if ext then getGlobalTypes else extractFromL) im
                  let newEntries = [ (rename k, v)
                                   | (k, v) <- Map.toList imported ]
                  mapM_ (uncurry setType) newEntries

-- Import statement of the form @from ... import ...@.
tf c (ImportReturn (FromImport fromModule toModule names)) _ =
    simple c $ do let ext = fromModule `Set.member` cfgExternalModules c
                      scope = (if ext then ExternalScope else ModuleScope)
                              fromModule
                      importName :: String -> Maybe String -> TF ()
                      importName n as =
                          let i = Name scope n
                              i' = Name (ModuleScope toModule) (fromMaybe n as)
                          in mvType i i'
                  mapM_ (uncurry importName) names

-- Assignment.
tf c (Assignment targets exp) _ =
    simple c $ do t <- expressionType c exp
                  assignToTargets targets t

-- Augmented assignment to identifier.
tf c (AugmentedAssignment (AugTargetIdentifier i) op exp) _ =
    simple c $ do t <- expressionType c exp
                  let f a = augAssignmentResult a op t
                  modifyType i f

-- Augmented assignment to attribute reference.
tf c (AugmentedAssignment
          (AugTargetAttributeRef
               (AttributeRef (Identifier i) attr)) op exp) _ =
    simple c $ do t <- expressionType c exp
                  modifyAttribute i attr (\a -> augAssignmentResult a op t)

-- Augmented assignment to subscription.
tf c (AugmentedAssignment
          (AugTargetSubscription
               (Subscription (Identifier i))) op exp) _ =
    -- augmented assignment to subscription works for lists, dicts and
    -- potentially user-defined classes
    simple c $ do rhs <- expressionType c exp
                  let f :: ValueType -> UnionType
                      f (BuiltinType ListType)     = oneType ListType
                      f (BuiltinType DictType)     = oneType DictType
                      f (BuiltinType (ListOf t))   =
                        oneType $ ListOf $ t `join` augAssignmentResult t op rhs
                      f (BuiltinType (DictOf k v)) =
                        oneType $
                            DictOf k (v `join` augAssignmentResult v op rhs)
                      f t | isInstance t           = oneType t
                          | otherwise              = bot
                  modifyType i (updateType f)

-- Augmented assignment to slicing.
tf c (AugmentedAssignment
          (AugTargetSlicing
               (Slicing (Identifier i))) op exp) _ =
    -- augmented assignment to subscription only makes sense for lists, and
    -- potentially for user-defined classes
    simple c $ do rhs <- expressionType c exp
                  let f :: ValueType -> UnionType
                      f (BuiltinType ListType)     = oneType ListType
                      f t@(BuiltinType (ListOf _)) =
                        oneType t `join` augAssignmentResult (oneType t) op rhs
                      f t | isInstance t           = oneType t
                          | otherwise              = bot
                  modifyType i (updateType f)

-- Augmented assignment: remaining cases, which we can't use.
tf _ (AugmentedAssignment _ op exp) _ = identity

-- Delete statement.
tf c (Del targets) _ =
    simple c $ mapM_ del targets
    where del :: Target -> TF ()
          del (TargetIdentifier i) = setType i bot
          del (TargetList targets) = mapM_ del targets
          del (TargetAttributeRef (AttributeRef (Identifier i) attr)) =
              modifyType i (updateType f)
              where -- class and instance types: remove attribute
                    f (ClassType (ClsTy classId sup env)) =
                        oneType $
                            ClsTy classId sup (Map.adjust (const bot) attr env)
                    f (InstanceType (InstTy cls env)) =
                        oneType $ InstTy cls (Map.adjust (const bot) attr env)
                    -- other types, including class and instance reference
                    -- types: no changes
                    f x = oneType x
          del _ = return ()


-- Function definition (fd).
tf c (Def i functionId) _ =
    simple c $ setType i (oneType $ FunId functionId)

-- Function call (fc).
tf c (FunctionCall exp args lr) _ =
    call c lr $
        do typeOfCall <- getTypeOfCall c exp
           case typeOfCall of
               AFunctionCall         -> functionCallFc c exp args
               AMethodCall e s clsTy -> methodCallFc c e s args clsTy
               AnInstantiation clsTy -> instantiationFc c args clsTy

-- Function return (fr).
tf c (FunctionReturn exp i l) _ =
    simple c $ do typeOfCall <- getTypeOfCall c exp
                  case typeOfCall of
                      AFunctionCall         -> functionCallFr i
                      AMethodCall e s clsTy -> methodCallFr e s i clsTy
                      AnInstantiation clsTy -> instantiationFr exp i clsTy

-- Function entry (fe).
tf c (FunctionEntry parameters) _ =
    simple c $ getArguments c parameters

-- Function exit (fx).
tf c (FunctionExit parameters) _ =
    simple c $ do -- set first argument, if any
                  case parameters of
                      (Parameter i _ : _) -> cpType i (PositionalAI 0)
                      _                   -> return ()
                  -- set return value, if necessary
                  r <- getType ReturnValue
                  when (isNothing r)
                       (setType ReturnValue (oneType NoneType))

-- Return statement.
tf c (Return Nothing) _ =
    simple c $ setType ReturnValue (oneType NoneType)
tf c (Return (Just exp)) _ =
    simple c $ do t <- expressionType c exp
                  setType ReturnValue t

-- Conditions (in for and if statements).
tf _ (LoopCondition exp) _ = identity
tf _ (Condition exp) _ = identity

-- Assignment in a for loop.
tf c (ForAssign target i) _ =
    simple c $ do mt <- getType i
                  let t = fromMaybe UTyTop mt
                  assignToTarget target t

-- | With statement. Not really supported.
tf c (With targets) _ =
    simple c (assignToTargets targets UTyTop)

-- Class declarations.
tf _ (ClassEntry i classId arguments) _ =
    identity -- no need to do anything here
tf c (ClassExit i classId arguments) _ =
    simple c $ do let inClass (Name (ClassScope s) _) | s == classId = True
                      inClass _                                      = False
                  attrs <- extractFromL inClass
                  let toExp (PositionalArgument exp) = [exp]
                      toExp _                        = []
                  supTypes <- mapM (expressionType c)
                                   (concatMap toExp arguments)
                  let sup = concatMap getClassType supTypes
                  let attrMap = Map.fromList
                                    [(n, t) | (Name _ n, t) <- Map.toList attrs]
                      classType = oneType $ ClsTy classId sup attrMap
                  if cfgFiClasses c
                      then do setType (ClassIdentifier classId) classType
                              setType i (oneType $ ClsRef classId)
                      else setType i classType

-- List, set and dictionary comprehensions.
tf c (ListComprehension i exp) _ =
    let f = do te <- expressionType c exp
               return $ oneType $ ListOf te
    in comprehensionTf c i ListType f
tf c (SetComprehension i exp) _ =
    let f = do te <- expressionType c exp
               return $ oneType $ SetOf te
    in comprehensionTf c i SetType f
tf c (DictComprehension i (a, b)) _ =
    let f = do k <- expressionType c a
               v <- expressionType c b
               return $ oneType $ DictOf k v
    in comprehensionTf c i DictType f

-- Scope entry: add identifiers coming into scope, store shadowed ones in
-- 'Shadowed' entries.
tf c (ScopeEntry identifiers) _ =
    let f :: Identifier -> TF ()
        f i = do mt <- getType i
                 case mt of
                     Nothing -> return ()
                     Just v  -> do let shadowed = Shadowed i
                                   ms <- getType shadowed
                                   let sv = case ms of Nothing -> v
                                                       Just v' -> v `join` v'
                                   setType shadowed sv
                 setType i bot
    in simple c $ mapM_ f identifiers

-- Scope exit: remove identifiers going out of scope, reconstitute identifiers
-- stored in 'Shadowed' entries.
tf c (ScopeExit identifiers) _ =
    let f :: Identifier -> TF ()
        f i = do let shadowed = Shadowed i
                 mt <- getType shadowed
                 case mt of Nothing -> removeType i
                            Just sv -> setType i sv
    in simple c $ mapM_ f identifiers


-- | Transfer function for list/set/dictionary comprehension.
comprehensionTf :: Configuration -> Identifier
                -> BuiltinType -> TF UnionType
                -> TypeInferenceMonad (TransferFunction L)
comprehensionTf c i nonParameterizedType f =
    simple c $ if cfgParameterizedDatatypes c
               then do parameterizedType <- f
                       oldType <- getTypeWithDefault bot i
                       setType i $ oldType `join` parameterizedType
               else setType i (oneType nonParameterizedType)

-- | Create mappings for the arguments of a function call.
setArguments :: Configuration -> [Argument] -> Int
             -> TF ()
setArguments c arguments startNumber =
    zipWithM_ ai [startNumber..] arguments
    where ai n (PositionalArgument e) = do t <- expressionType c e
                                           setType (PositionalAI n) t
          ai _ (KeywordArgument s e)  = do t <- expressionType c e
                                           setType (KeywordAI s) t
          ai _ (StarArgument e)       = do t <- expressionType c e
                                           setType StarAI t
          ai _ (StarStarArgument e)   = do t <- expressionType c e
                                           setType StarStarAI t

-- | Retrieve argument types and map them to formal parameters. See the
-- language reference, section 5.3.4.
getArguments :: Configuration -> [Parameter] -> TF ()
getArguments c params =
    do let ps = filter isRegularParameter params
           paramIdentifiers = map getParamIdentifier ps
           n = length ps
           sp = find isStarParameter params
           ssp = find isStarStarParameter params
           nameMap = Map.fromList $ zip [n | Parameter (Name _ n) _ <- ps] [0..]
           getDefault :: Parameter -> TF (Maybe UnionType)
           getDefault (Parameter _ Nothing)  = return Nothing
           getDefault (Parameter _ (Just e)) = do t <- expressionType c e
                                                  return $ Just t
       defaults <- mapM getDefault ps
       args <- getAllFromL isArgumentIdentifier
       removeFromL isArgumentIdentifier
       let (pa, ka, sa, ssa) = splitArgs args
           f = do let v = Map.fromList $ zip [0..n-1] (repeat Nothing)
                      (pa', extraPositional) =
                          partition (\(PositionalAI i, _) -> i < n) pa
                      v' = Map.fromList [ (i, Just t)
                                        | (PositionalAI i, t) <- pa' ]
                           `Map.union`
                           v
                  when (not (null extraPositional) && isNothing sp)
                       Nothing
                  let (ka', extraKw) =
                          partition (\(KeywordAI kw, _) ->
                                          kw `Map.member` nameMap)
                                    ka
                      v'' = Map.fromList [ (nameMap Map.! kw, Just t)
                                         | (KeywordAI kw, t) <- ka']
                           `Map.union` v'
                  when (not (null extraKw) && isNothing ssp)
                       Nothing
                  let useDefault _  (Just v) = Just v
                      useDefault k  _        = defaults !! k
                      v''' = Map.mapWithKey useDefault v''
                  when (any isNothing (Map.elems v''') && null sa && null ssa)
                       Nothing
                  let values = map (fromMaybe UTyTop . snd) (Map.toAscList v''')
                      entries = zip paramIdentifiers values
                             ++ case sp of Nothing -> []
                                           Just p  -> [(getParamIdentifier p,
                                                        oneType TupleType)]
                             ++ case ssp of Nothing -> []
                                            Just p  -> [(getParamIdentifier p,
                                                         oneType DictType)]
                  return $ Map.fromList entries
           allTop = Map.fromList (zip paramIdentifiers (repeat UTyTop))
           newEntries = fromMaybe allTop f
       mapM_ (uncurry setType) (Map.toList newEntries)

data TypeOfCall = AFunctionCall
                | AMethodCall Expression String ClassType
                | AnInstantiation ClassType

-- | Given an expression which is called in the Python code, apply heuristics
-- to find out if it is a function call, method call or instantiation.
getTypeOfCall :: Configuration -> Expression -> TF TypeOfCall
getTypeOfCall c exp =
    do t <- expressionType c exp
       if allTypes isClass t
           then return $ let UTy s = t
                         in case Set.toList s of
                                (ClassType ct : _) -> AnInstantiation ct
                                _                  -> AFunctionCall
           else case exp of
                    AttributeReference (AttributeRef exp' attr) ->
                        do t' <- expressionType c exp'
                           if allTypes isInstance t'
                               then do let UTy s = t'
                                           (InstanceType it : _) = Set.toList s
                                       clsTy <- classOfInstance it
                                       mt <- clsAttr attr clsTy
                                       case mt of
                                           Just t'' | allTypes isFunction t'' ->
                                               return $ AMethodCall exp'
                                                                    attr
                                                                    clsTy
                                           _ -> return AFunctionCall
                               else return AFunctionCall
                    _ -> return AFunctionCall

-- | Transfer function for the FunctionCall (fc) node for an instantiation.
instantiationFc :: Configuration -> [Argument] -> ClassType
                -> TF ([Label], Bool)
instantiationFc c arguments clsTy =
    do init <- clsAttr "__init__" clsTy
       let classId = getClassId clsTy
           t = fromMaybe bot init
           functionTypes = getFunctionTypes t
           anyFunctionTypes = not (null functionTypes)
           arg0 = PositionalAI 0
       if anyFunctionTypes
           then do -- handle function types
                   setType arg0 (oneType $ InstRef classId)
                   return ([], True)
           else do -- handle function ids
                   let functionIds = getFunctionIds t
                       instTy = oneType $ InstTy clsTy Map.empty
                   setArguments c arguments 1
                   if cfgFiInstances c
                       then do setType (InstanceIdentifier classId) instTy
                               setType arg0 (oneType $ InstRef classId)
                       else setType arg0 instTy
                   return (functionIds, null functionIds)

-- | Transfer function for the FunctionCall (fc) node for a method call.
methodCallFc :: Configuration -> Expression -> String -> [Argument]
             -> ClassType -> TF ([Label], Bool)
methodCallFc c exp attr arguments clsTy =
    do method <- clsAttr attr clsTy
       let t = fromMaybe bot method
       anyFunctionTypes <- handleFunctionTypes c t arguments
       let functionIds = getFunctionIds t
       setArguments c (PositionalArgument exp : arguments) 0
       return (functionIds, anyFunctionTypes || null functionIds)

-- | Transfer function for the FunctionCall (fc) node for a function call.
functionCallFc :: Configuration -> Expression -> [Argument]
               -> TF ([Label], Bool)
functionCallFc c exp arguments =
    do t <- expressionType c exp
       anyFunctionTypes <- handleFunctionTypes c t arguments
       let functionIds = getFunctionIds t
       setArguments c arguments 0
       return (functionIds, anyFunctionTypes || null functionIds)

handleFunctionTypes :: Configuration -> UnionType -> [Argument] -> TF Bool
handleFunctionTypes c t arguments =
    do let functionTypes = getFunctionTypes t
           anyFunctionTypes = not (null functionTypes)
       when anyFunctionTypes
           $ do let argExprs = getPositionalArguments arguments
                argTypes <- mapM (expressionType c) argExprs
                let apply (a, r) = applyFunctionType a r argTypes
                    returnType = joinAll $ map apply functionTypes
                setType ReturnValue returnType
       return anyFunctionTypes

getPositionalArguments :: [Argument] -> [Expression]
getPositionalArguments =
    let f (PositionalArgument e) = Just e
        f _                      = Nothing
    in mapMaybe f

getFunctionIds :: UnionType -> [FunctionId]
getFunctionIds UTyTop  = []
getFunctionIds (UTy s) =
    let f (FunctionType (FunId i))   = [i]
        f (FunctionType (FunTy _ _)) = []
    in concatMap f (filter isFunction (Set.toList s))

getFunctionTypes :: UnionType -> [([UnionType], UnionType)]
getFunctionTypes UTyTop  = []
getFunctionTypes (UTy s) =
    let f (FunctionType (FunId _))   = []
        f (FunctionType (FunTy a r)) = [(a, r)]
    in concatMap f (filter isFunction (Set.toList s))

-- | Transfer function for the FunctionReturn (fr) node for an instantiation.
instantiationFr :: Expression -> Identifier -> ClassType -> TF ()
instantiationFr exp i _ =
    do cpType (PositionalAI 0) i
       removeFromL isPositionalAI
       removeType ReturnValue

-- | Transfer function for the FunctionReturn (fr) node for a method call.
methodCallFr :: Expression -> String -> Identifier -> ClassType -> TF ()
methodCallFr exp attr i clsTy =
    do cpType ReturnValue i
       case exp of Identifier i -> cpType (PositionalAI 0) i
                   _            -> return ()
       removeFromL isPositionalAI
       removeType ReturnValue

-- | Transfer function for the FunctionReturn (fr) node for a function call.
functionCallFr :: Identifier -> TF ()
functionCallFr i =
    do cpType ReturnValue i
       removeFromL isPositionalAI
       removeType ReturnValue

splitArgs args = ( filter (isPositionalAI . fst) args,
                   filter (isKeywordAI    . fst) args,
                   filter (isStarAI       . fst) args,
                   filter (isStarStarAI   . fst) args)

-- | Create transfer function for an assignment to a list of targets.
assignToTargets :: [Target] -> UnionType -> TF ()
assignToTargets targets t = mapM_ (`assignToTarget` t) targets

-- | Create transfer function for an assignment to a target.
assignToTarget :: Target -> UnionType -> TF ()
assignToTarget (TargetIdentifier i) t = setType i t
assignToTarget (TargetList list) t =
    let g :: Target -> TF ()
        g (StarTarget (TargetIdentifier i)) =
            setType i (filterType (orInstance isSequence) t)
        g target = assignToTarget target (iterableElementType t)
    in mapM_ g list
assignToTarget (TargetAttributeRef (AttributeRef (Identifier i) attr)) t =
    modifyAttribute i attr (const t)
assignToTarget (TargetSubscription (Subscription (Identifier i))) t =
    -- assignment to subscript works for lists, dicts and potentially
    -- user-defined classes
    let f :: ValueType -> UnionType
        f (BuiltinType ListType)      = oneType ListType
        f (BuiltinType DictType)      = oneType DictType
        f (BuiltinType (ListOf t'))   = oneType $ ListOf (t' `join` t)
        f (BuiltinType (DictOf k v))  = oneType $ DictOf k (v `join` t)
        f t' | isInstance t'          = oneType t'
             | otherwise              = bot
    in modifyType i (updateType f)
assignToTarget (TargetSlicing (Slicing (Identifier i))) t =
    -- assignment to slicing only works for lists and potentially user-defined
    -- classes
    let f :: ValueType -> UnionType
        f (BuiltinType ListType) = oneType ListType
        f (BuiltinType (ListOf t')) =
            oneType $ ListOf $ t' `join` iterableElementType t
        f t' | isInstance t' = oneType t'
             | otherwise     = bot
    in modifyType i (updateType f)
assignToTarget _ _ = return ()

getClassType :: UnionType -> [ClassType]
getClassType UTyTop  = []
getClassType (UTy s) = let list = filter isClass (Set.toList s)
                       in if null list
                          then []
                          else take 1 [c | ClassType c <- list]

-- | Given the type of the lhs, the operator and the type of the rhs of an
-- augmented assignment, determine the resulting type of the lhs.
augAssignmentResult :: UnionType -> AssignmentOperator -> UnionType -> UnionType
augAssignmentResult a op b =
    case op of
        PlusGets       -> eachCombination a b plus
        MinusGets      -> eachCombination a b justArithmetic
        TimesGets      -> eachCombination a b mult
        DivGets        -> eachCombination a b div
        DivDivGets     -> eachCombination a b justArithmetic
        ModGets        -> eachCombination a b modulo
        ExpGets        -> eachCombination a b pow
        RightShiftGets -> eachCombination a b shift
        LeftShiftGets  -> eachCombination a b shift
        AndGets        -> eachCombination a b bitwise
        XorGets        -> eachCombination a b bitwise
        OrGets         -> eachCombination a b bitwise
        _              -> b

-- | Function composition for a list of functions.
compose :: [c -> c] -> c -> c
compose = foldl (.) id

-- | Find the type for an expression, given the current environment.
expressionType :: Configuration -> Expression -> TF UnionType
expressionType _ (Identifier i) =
    do mt <- getType i
       return $ fromMaybe UTyTop mt
expressionType _ (Literal l) = return $ oneType $ literalType l
expressionType c (TupleExpression es) =
    if cfgParameterizedDatatypes c
    then do types <- mapExpressionType c es
            return $ oneType $ TupleOf types
    else return $ oneType TupleType
expressionType c (ListExpression es) =
    if cfgParameterizedDatatypes c
    then do types <- mapExpressionType c es
            return $ oneType $ ListOf $ joinAll types
    else return $ oneType ListType
expressionType c (SetExpression es) =
    if cfgParameterizedDatatypes c
    then do types <- mapExpressionType c es
            return $ oneType $ SetOf $ joinAll types
    else return $ oneType SetType
expressionType c (DictionaryExpression pairs) =
    if cfgParameterizedDatatypes c
    then do keyTypes <- mapExpressionType c (map fst pairs)
            valTypes <- mapExpressionType c (map snd pairs)
            return $ oneType $ DictOf (joinAll keyTypes) (joinAll valTypes)
    else return $ oneType DictType
expressionType c (AttributeReference (AttributeRef exp name)) =
    do t <- expressionType c exp
       case t of
           UTyTop -> return UTyTop
           UTy a  -> do let f (ClassType t)    = do mt <- clsAttr name t
                                                    return $ fromMaybe bot mt
                            f (InstanceType t) = do mt <- instAttr name t
                                                    return $ fromMaybe bot mt
                            f _                = return UTyTop
                        types <- mapM f (Set.toList a)
                        return $ joinAll types
expressionType c (SubscriptionExpression (Subscription e)) =
    if cfgParameterizedDatatypes c
    then do t <- expressionType c e
            return $ indexingElementType t
    else return UTyTop
expressionType c (SlicingExpression (Slicing e)) =
    -- slicing only works for tuples, lists and potentially user-defined classes
    do let f t = case t of BuiltinType (TupleOf _) -> oneType TupleType
                           BuiltinType (ListOf _)  -> oneType t
                           BuiltinType TupleType   -> oneType t
                           BuiltinType ListType    -> oneType t
                           InstanceType _          -> UTyTop
                           _                       -> bot
       t <- expressionType c e
       return $ updateType f t
expressionType c (UnaryOperation op exp) =
    do t <- expressionType c exp
       return $ case op of Invert     -> filterType (orInstance isIntegral) t
                           BooleanNot -> oneType BoolType
                           _          -> filterType (orInstance isNum) t
expressionType c (BinaryOperation a op b)
    | isComparisonOperator op = return $ oneType BoolType
    | isBooleanOperator op    =
          do ta <- expressionType c a
             tb <- expressionType c b
             return $ ta `join` tb
    | otherwise               =
          do ta <- expressionType c a
             tb <- expressionType c b
             return $ case op of
                          Exponent   -> eachCombination ta tb pow
                          Times      -> eachCombination ta tb mult
                          Div        -> eachCombination ta tb div
                          DivDiv     -> eachCombination ta tb justArithmetic
                          Modulo     -> eachCombination ta tb modulo
                          Minus      -> eachCombination ta tb justArithmetic
                          Plus       -> eachCombination ta tb plus
                          BitwiseAnd -> eachCombination ta tb bitwise
                          BitwiseXor -> eachCombination ta tb bitwise
                          BitwiseOr  -> eachCombination ta tb bitwise
                          RightShift -> eachCombination ta tb shift
                          LeftShift  -> eachCombination ta tb shift
expressionType _ Generator = return UTyTop -- not supported
expressionType _ (Yield _) = return UTyTop -- not supported

mapExpressionType :: Configuration -> [Expression] -> TF [UnionType]
mapExpressionType c = mapM (expressionType c)

-- | Type of elements that can be extracted by iteration or assignment to a
-- list of targets.
iterableElementType :: UnionType -> UnionType
iterableElementType = let f (BuiltinType (DictOf k _)) = k
                          f t                          = elementType t
                      in updateType f

-- | Type of elements that can be extracted by indexing.
indexingElementType :: UnionType -> UnionType
indexingElementType = updateType elementType

elementType :: ValueType -> UnionType
elementType (BuiltinType StrType)         = oneType StrType
elementType (BuiltinType (TupleOf l))     = joinAll l
elementType (BuiltinType (ListOf t))      = t
elementType (BuiltinType (SetOf t))       = t
elementType (BuiltinType (FrozensetOf t)) = t
elementType (BuiltinType (DictOf _ v))    = v
elementType t | orInstance isSequence t = UTyTop
              | otherwise               = bot

-- functions to determine possible result types of a binary operation
justArithmetic, pow, mult, div, modulo, plus, bitwise, shift ::
    (ValueType, ValueType) -> UnionType
justArithmetic (a, b) | isNum a && isNum b = oneType $ commonArithmeticType a b
                      | otherwise = bot
pow (a, b) | isNum a && isNum b = case commonArithmeticType a b of
                                      IntType -> oneType IntType `join`
                                                     oneType FloatType
                                      t       -> oneType t
           | otherwise = bot
mult (a, b) | isSequence a && isIntegral b = oneType a
            | isIntegral a && isSequence b = oneType b
            | isNum a && isNum b   = oneType $ commonArithmeticType a b
            | otherwise = bot
div (a, b) | isNum a && isNum b = case commonArithmeticType a b of
                                      IntType     -> oneType FloatType
                                      FloatType   -> oneType FloatType
                                      ComplexType -> oneType ComplexType
           | otherwise = bot
modulo (BuiltinType StrType, _) = oneType StrType
modulo (a, b) | isNum a && isNum b = case commonArithmeticType a b of
                                         ComplexType -> bot
                                         t           -> oneType t
              | otherwise = bot
plus (BuiltinType StrType, BuiltinType StrType) = oneType StrType
plus (BuiltinType (TupleOf a), BuiltinType (TupleOf b)) =
    oneType $ TupleOf $ a ++ b
plus (BuiltinType (ListOf a), BuiltinType (ListOf b)) =
    oneType $ ListOf $ a `join` b
plus (a, b) | isTuple a && isTuple b = oneType TupleType
            | isList a && isList b   = oneType ListType
            | isNum a && isNum b     = oneType $ commonArithmeticType a b
            | otherwise              = bot
bitwise (BuiltinType BoolType, BuiltinType BoolType) = oneType BoolType
bitwise (a, b) | isNum a && isNum b = case commonArithmeticType a b of
                                          BoolType -> oneType BoolType
                                          IntType  -> oneType IntType
                                          _        -> bot
               | otherwise          = bot
shift (a, b) | isIntegral a && isIntegral b = oneType IntType
             | otherwise                    = bot

-- | Compute the cartesian product of two sets of types, apply the function to
-- each combination and return the join of all results.
eachCombination :: UnionType
                -> UnionType
                -> ((ValueType, ValueType) -> UnionType)
                -> UnionType
eachCombination UTyTop  _       _ = UTyTop
eachCombination _       UTyTop  _ = UTyTop
eachCombination (UTy a) (UTy b) f =
    let la = Set.toList a
        lb = Set.toList b
    in if any isInstance (la ++ lb)
       then UTyTop
       else joinAll [f (x, y) | x <- la, y <- lb]

-- | Convert the numeric arguments to a common type, as defined in section 5.1
-- of the language reference.
commonArithmeticType :: ValueType -> ValueType -> BuiltinType
commonArithmeticType (BuiltinType a) (BuiltinType b) = h a b
    where h ComplexType _           = ComplexType
          h _           ComplexType = ComplexType
          h FloatType   _           = FloatType
          h _           FloatType   = FloatType
          h _           _           = IntType
commonArithmeticType _ _ = IntType

-- | Find the type for a literal.
literalType :: Literal -> BuiltinType
literalType (BoolLiteral _)       = BoolType
literalType (StringLiteral _)     = StrType
literalType (ByteStringLiteral _) = BytesType
literalType (IntegerLiteral _)    = IntType
literalType (FloatLiteral _)      = FloatType
literalType (ImagLiteral _)       = ComplexType
literalType NoneLiteral           = NoneType

simple :: Configuration -> TF () -> TypeInferenceMonad (TransferFunction L)
simple c tf =
    return $
        SimpleTransferFunction $
            simpleTransferFunction (cfgFiModuleScope c) tf

call :: Configuration -> Label -> TF ([Label], Bool)
     -> TypeInferenceMonad (TransferFunction L)
call c lr tf =
    return $ CallTransferFunction lr
                                  (callTransferFunction (cfgFiModuleScope c) tf)

identity :: TypeInferenceMonad (TransferFunction L)
identity = return identityTransferFunction

identityTransferFunction :: TransferFunction L
identityTransferFunction = SimpleTransferFunction $ \l _ -> (l, Nothing, False)


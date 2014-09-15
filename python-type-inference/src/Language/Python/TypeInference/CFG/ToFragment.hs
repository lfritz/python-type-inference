-- | Functions to create a Fragment for (parts of) an abstract syntax tree.
module Language.Python.TypeInference.CFG.ToFragment (
    convertModule,
    runConversion,
    ConversionState
) where

import Control.Monad.State
import Data.Map (Map)
import Data.Maybe
import Data.Set (Set)
import Language.Python.Common.SrcLocation
import Language.Python.TypeInference.CFG.CFG
import Language.Python.TypeInference.CFG.Fragment
import Language.Python.TypeInference.Common
import Language.Python.TypeInference.Error
import qualified Data.Map as Map
import qualified Data.Set as Set
import qualified Language.Python.Common.AST as AST

-- | Create a fragment for a module.
convertModule :: String -> AST.ModuleSpan
    -> StateT ConversionState TypeInferenceMonad (Fragment, Set Identifier)
convertModule moduleName (AST.Module stmts) =
    do bound <- lift $ namesBound stmts
       moduleNames <- lift $ moduleNamesBound stmts
       let bindings = [ (n, Name (ModuleScope moduleName) n)
                      | n <- Set.toList bound ]
           identifiers = map snd bindings
           env = Map.fromList bindings
       fragment <- withStateT (\cs -> cs { csEnvironment = env,
                                           csCurrentModule = moduleName,
                                           csOtherModules = moduleNames } )
                              (convertAll stmts)
       return (fragment, Set.fromList identifiers)

-- | Create a fragment for a sequence of statements.
convertAll :: [AST.Statement SrcSpan] -> Conversion
convertAll stmts = do fs <- mapM convert stmts
                      return $ mconcat fs

-- | The environment indicates which name binding a name refers to.
type Environment = Map String Identifier

-- | State maintained while converting from AST to Fragment.
data ConversionState =
    ConversionState {
        csNextLabel       :: Int,
        csNextIdentifier  :: Int,
        csNextFunctionId  :: FunctionId,
        csNextClassId     :: ClassId,
        csNextWithId      :: Int,
        csNextForLoopId   :: Int,
        csEnvironment     :: Environment,
        csCurrentModule   :: String,
        csOtherModules    :: Set String,
        csExternalModules :: Set String
    }

-- | Given the module name and top-level environment, create an initial state.
initialState :: ConversionState
initialState = ConversionState 1 1 1 1 1 1 Map.empty "none" Set.empty Set.empty

-- | Type of a computation that converts from AST to Fragment.
type Conversion = StateT ConversionState TypeInferenceMonad Fragment

-- | Given the module name and top-level environment, run conversion.
runConversion :: Set String
              -> Int
              -> StateT ConversionState TypeInferenceMonad a
              -> TypeInferenceMonad a
runConversion externalModules nextClassId c =
    evalStateT c (initialState { csNextClassId = nextClassId
                               , csExternalModules = externalModules })

-- | Get a new, unique label.
newLabel :: StateT ConversionState TypeInferenceMonad Int
newLabel = do l <- gets csNextLabel
              modify $ \s -> s { csNextLabel = l + 1 }
              return l

-- | Get a new, unique identifier.
newIdentifier :: StateT ConversionState TypeInferenceMonad Identifier
newIdentifier = do i <- gets csNextIdentifier
                   modify $ \s -> s { csNextIdentifier = i + 1 }
                   return $ Generated i

-- | Get a new, unique function id.
newFunctionId :: StateT ConversionState TypeInferenceMonad FunctionId
newFunctionId = do l <- gets csNextFunctionId
                   modify $ \s -> s { csNextFunctionId = l + 1 }
                   return l

-- | Get a new, unique class id.
newClassId :: StateT ConversionState TypeInferenceMonad ClassId
newClassId = do l <- gets csNextClassId
                modify $ \s -> s { csNextClassId = l + 1 }
                return l

-- | Get a new, unique @with@ id.
newWithId :: StateT ConversionState TypeInferenceMonad Int
newWithId = do l <- gets csNextWithId
               modify $ \s -> s { csNextWithId = l + 1 }
               return l

-- | Get a new, unique @for@ loop id.
newForLoopId :: StateT ConversionState TypeInferenceMonad Int
newForLoopId = do l <- gets csNextForLoopId
                  modify $ \s -> s { csNextForLoopId = l + 1 }
                  return l

-- | Look up the given name in the current environment and return the
-- identifier it revers to.
getI :: String -> StateT ConversionState TypeInferenceMonad Identifier
getI name =
    do env <- gets csEnvironment
       return $ Map.findWithDefault (Name Global name) name env

mkIdentifier :: String -> String
             -> StateT ConversionState TypeInferenceMonad Identifier
mkIdentifier moduleName identifierName =
    do externalModules <- gets csExternalModules
       let scope = if moduleName `Set.member` externalModules
                   then ExternalScope
                   else ModuleScope
       return $ Name (scope moduleName) identifierName

-- | Execute an action on a state modified by adding a list of bindings to the
-- environment.
withBindings :: [(String, Identifier)]
             -> StateT ConversionState TypeInferenceMonad a
             -> StateT ConversionState TypeInferenceMonad a
withBindings list m =
    do let setEnv env = modify $ \s -> s { csEnvironment = env }
       env <- gets csEnvironment
       setEnv $ Map.fromList list `Map.union` env
       result <- m
       setEnv env
       return result

-- | Create a new fragment containing one program point.
newFragment :: ProgramPoint -> SrcSpan
            -> StateT ConversionState TypeInferenceMonad (Label, Fragment)
newFragment pp srcSpan =
    do l <- newLabel
       pos <- lift $ toPosition srcSpan
       let f = fragment (Map.singleton l (pp, pos))
                        Set.empty
                        (Set.singleton l)
                        (Set.singleton l)
       return (l, f)

-- | Like 'newFragment', but don't return the label.
newFragment' :: ProgramPoint -> SrcSpan -> Conversion
newFragment' p s = do (_, f) <- newFragment p s
                      return f


-- | Create Fragment for a statement.
convert :: AST.Statement SrcSpan -> Conversion

-- Import statements.
convert (AST.Import items s) =
    do imports <- mapM imported items
       fs <- mapM (importNodes s) imports
       return $ mconcat fs
convert (AST.FromImport m i s) =
    do imports <- fromImported m i
       importNodes s imports

-- While loop.
convert (AST.While cond body els _) =
    do (fCondBefore, e) <- toExpression cond
       fCondActual <- newFragment' (LoopCondition e) (AST.annot cond)
       let fCond = fCondBefore `mappend` fCondActual
       fBody <- convertAll body
       fEls <- convertAll els
       let fs      = [fCond, fBody] ++ if nullF fEls then [] else [fEls]
           nodes   = Map.unions (map getNodes fs)
           edges   = Set.unions (map getEdges fs)
                     `Set.union` (fCond --> fBody)
                     `Set.union` (fBody --> fCond)
                     `Set.union` (fCond --> fEls)
                     `Set.union` continueEdges fBody fCond
           initial = frInitial fCond
           final   = getBreak fBody
                     `Set.union` if nullF fEls
                                 then getFinal fCond
                                      `Set.union` getContinue fBody
                                 else getFinal fEls
           break   = if nullF fEls then Set.empty else getBreak fEls
           continu = if nullF fEls then Set.empty else getContinue fEls
           ret     = Set.unions $ map getReturn fs
           imports = Map.unions $ map getImports fs
           ft      = Map.unions $ map getFunctionTable fs
       return $ Fragment nodes edges initial final break continu ret imports ft

-- For loop.
convert (AST.For targets generator body els _) =
    do forLoopId <- newForLoopId
       let newBindings = [(n, Name (ForLoopScope forLoopId) n)
                         | n <- targetNames targets]
           newIdentifiers = map snd newBindings
           lookupName name = withBindings newBindings (getI name)
       (fGenBefore, e) <- toExpression generator
       i <- newIdentifier
       let srcSpan = AST.annot generator
       fGen <- newFragment' (Assignment [TargetIdentifier i] e) srcSpan
       let fg = fGenBefore `mappend` fGen
       targetList <- mapM (toTarget lookupName) targets
       let (fts, ts) = unzip targetList
       (lAssign, fAssign) <- newFragment (ForAssign (TargetList ts) i) srcSpan
       fBody <- withBindings newBindings (convertAll body)
       (sn, sx) <- scopeFragments newIdentifiers srcSpan
       let fBefore = mconcat (fts ++ [sn])
       fEls <- convertAll els
       let fs      = [fg, fBefore, fAssign, sx, fBody]
                     ++ if nullF fEls then [] else [fEls]
           nodes   = Map.unions (map getNodes fs)
           edges   = Set.unions (map getEdges fs)
                     `Set.union` (fg --> fBefore)
                     `Set.union` (fBefore --> fAssign)
                     `Set.union` (fAssign --> fBody)
                     `Set.union` (fBody --> fAssign)
                     `Set.union` (fAssign --> sx)
                     `Set.union` (sx --> fEls)
                     `Set.union` continueEdges fBody fAssign
                     `Set.union`
                         Set.fromList
                             [(b, i) | b <- Set.toList (getBreak fBody),
                                       i <- Set.toList (getInitial sx)]
           initial = frInitial fg
           final   = getFinal (if nullF fEls then sx else fEls)
           break   = if nullF fEls then Set.empty else getBreak fEls
           continu = if nullF fEls then Set.empty else getContinue fEls
           ret     = Set.unions $ map getReturn fs
           imports = Map.unions $ map getImports fs
           ft      = Map.unions $ map getFunctionTable fs
       return $ Fragment nodes edges initial final break continu ret imports ft

-- Function definition.
convert (AST.Fun (AST.Ident name _) params _ body s) =
    do functionId <- newFunctionId
       identifier <- getI name
       list <- mapM (toParameter (FunctionScope functionId)) params
       let (pfs, ps) = unzip (concat list)
       fd <- newFragment' (Def identifier functionId) s
       let fd' = mconcat $ pfs ++ [fd]
       (ln, fn) <- newFragment (FunctionEntry ps) s
       (lx, fx) <- newFragment (FunctionExit ps) s
       bound <- lift $ namesBound body
       nonlocal <- lift $ declaredNonlocal body
       global <- lift $ declaredGlobal body
       ps <- lift $ mapM paramName params
       moduleName <- gets csCurrentModule
       let paramNames     = concat ps
           newNames       = (Set.fromList paramNames `Set.union` bound)
                            Set.\\ (nonlocal `Set.union` global)
           moduleScope    = ModuleScope moduleName
           newBindings    = [ (n, Name (FunctionScope functionId) n)
                            | n <- Set.toList newNames]
           newIdentifiers = map snd newBindings
           globalBindings = [(n, Name moduleScope n) | n <- Set.toList global]
       fBody <- withBindings (newBindings ++ globalBindings) (convertAll body)
       (sn, sx) <- scopeFragments newIdentifiers s
       let fs      = [fd', fn, fx, fBody, sn, sx]
           nodes   = Map.unions (map getNodes fs)
           edges   = getEdges fd'
                     `Set.union` getEdges fBody
                     `Set.union` (sn --> fn)
                     `Set.union` (fn --> fBody)
                     `Set.union` returnEdges fBody fx
                     `Set.union` (fx --> sx)
           initial = frInitial fd'
           final   = getFinal fd'
           break   = Set.empty
           continu = Set.empty
           ret     = Set.empty
           imports = Map.unions $ map getImports fs
           ft      = Map.fromList [ (functionId, (a, b))
                                  | a <- Set.toList (getInitial sn),
                                    b <- Set.toList (getInitial sx) ]
                     `Map.union`
                     Map.unions (map getFunctionTable fs)
       return $ Fragment nodes edges initial final break continu ret imports ft

-- Class definition.
convert (AST.Class (AST.Ident name _) args body s) =
    do list <- mapM toArgument args
       let (fs, as) = unzip list
       identifier <- getI name
       classId <- newClassId
       (le, fe) <- newFragment (ClassEntry identifier classId as) s
       (lx, fx) <- newFragment (ClassExit identifier classId as) s
       bound <- lift $ namesBound body
       nonlocal <- lift $ declaredNonlocal body
       global <- lift $ declaredGlobal body
       moduleName <- gets csCurrentModule
       let newNames       = bound Set.\\ (nonlocal `Set.union` global)
           moduleScope    = ModuleScope moduleName
           newBindings    = [ (n, Name (ClassScope classId) n)
                            | n <- Set.toList newNames]
           newIdentifiers = map snd newBindings
           globalBindings = [(n, Name moduleScope n) | n <- Set.toList global]
       fb <- withBindings (newBindings ++ globalBindings) (convertAll body)
       (sn, sx) <- scopeFragments newIdentifiers s
       return $ mconcat (fs ++ [sn, fe, fb, fx, sx])

-- Conditional (if-elif-else).
convert (AST.Conditional ifs els _) =
    do list <- mapM convertPair ifs
       fEls <- if null els then return EmptyFragment else convertAll els
       let (cs, bs) = unzip list
           lastCond = last cs
           fs       = cs ++ bs ++ if null els then [] else [fEls]
           nodes    = Map.unions (map getNodes fs)
           edgesL   = map getEdges fs
                   ++ [c --> b | (c, b) <- list]
                   ++ [a --> b | (a, b) <- zip cs (tail cs)]
                   ++ if null els then [] else [lastCond --> fEls]
           edges    = Set.unions edgesL
           initial  = frInitial (head cs)
           finalL   = (if null els then getFinal lastCond else getFinal fEls)
                      : map getFinal bs
           final    = Set.unions finalL
           break    = Set.unions $ map getBreak fs
           continu  = Set.unions $ map getContinue fs
           ret      = Set.unions $ map getReturn fs
           imports  = Map.unions $ map getImports fs
           ft       = Map.unions (map getFunctionTable fs)
       return $ Fragment nodes edges initial final break continu ret imports ft
    where convertPair (cond, body) =
              do (fCondBefore, e) <- toExpression cond
                 fCond <- newFragment' (Condition e) (AST.annot cond)
                 fBody <- convertAll body
                 return (fCondBefore `mappend` fCond, fBody)

-- Assignment statement (= operator).
convert (AST.Assign lhs rhs s) =
    do list <- mapM (toTarget getI) lhs
       let (fs, ts) = unzip list
       (f2, e) <- toExpression rhs
       f3 <- newFragment' (Assignment ts e) s
       return $ mconcat (fs ++ [f2, f3])

-- Augmented assignment statement (+=, -=, etc).
convert (AST.AugmentedAssign lhs op rhs s) =
    do (f1, t) <- toAugTarget lhs
       let o = toAssignmentOperator op
       (f2, e) <- toExpression rhs
       f3 <- newFragment' (AugmentedAssignment t o e) s
       return $ f1 `mappend` f2 `mappend` f3

-- Decorated function or class definition. The decorator is ignored.
convert (AST.Decorated _ stmt _) = convert stmt

-- Return statement.
convert (AST.Return Nothing s) =
    do (l, f) <- newFragment (Return Nothing) s
       return $ f { frReturn = Set.singleton l,
                    frFinal = Set.empty }
convert (AST.Return (Just expr) s) =
    do (fe, e) <- toExpression expr
       (l, fr) <- newFragment (Return $ Just e) s
       let f = fe `mappend` fr
       return $ f { frReturn = Set.singleton l,
                    frFinal = Set.empty }

-- Try-catch-finally: We ignore exception handling, so the CFG for a try
-- statement is just the body, else and finally parts concatenated.
convert (AST.Try body _ els finally _) =
    do fs <- mapM convertAll [body, els, finally]
       return $ mconcat fs

-- Raise statement. Ignored since we don't support exception handling.
convert (AST.Raise _ _) = return EmptyFragment

-- With statement.
convert (AST.With ctx body s) =
    do withId <- newWithId
       let targets = mapMaybe snd ctx
           newBindings = [(n, Name (WithScope withId) n)
                         | n <- targetNames targets]
           newIdentifiers = map snd newBindings
           lookupName name = withBindings newBindings (getI name)
       list <- mapM (toTarget lookupName) targets
       let (fs, ts) = unzip list
       (lw, fw) <- newFragment (With ts) s
       fBody <- withBindings newBindings (convertAll body)
       (sn, sx) <- scopeFragments newIdentifiers s
       return $ mconcat (fs ++ [sn, fw, fBody, sx])

-- Pass statement.
convert (AST.Pass s) = newFragment' Pass s

-- Break and continue.
convert (AST.Break s) = do (l, f) <- newFragment Break s
                           return $ f { frBreak = Set.singleton l,
                                        frFinal = Set.empty }
convert (AST.Continue s) = do (l, f) <- newFragment Continue s
                              return $ f { frContinue = Set.singleton l,
                                           frFinal = Set.empty }

-- Delete statement.
convert (AST.Delete lhs s) =
    do list <- mapM (toTarget getI) lhs
       let (fs, ts) = unzip list
       f <- newFragment' (Del ts) s
       return $ mconcat (fs ++ [f])

-- Statement containing only an expression.
convert (AST.StmtExpr e s) =
    do (f, e) <- toExpression e
       f' <- newFragment' (Expression e) s
       return $ f `mappend` f'

-- Global and nonlocal statements.
convert (AST.Global _ _) = return EmptyFragment
convert (AST.NonLocal _ _) = return EmptyFragment

-- Assertion.
convert (AST.Assert _ s) = newFragment' Assert s

-- Statements that should not occur.
convert (AST.Print _ _ _ _) =
    throwError $ CFGError "print statement does not exist in Python 3"
convert (AST.Exec _ _ _) =
    throwError $ CFGError "exec statement does not exist in Python 3"


-- | Create 'ImportCall' and 'ImportReturn' nodes.
importNodes :: SrcSpan -> ImportedNames -> Conversion
importNodes s importedNames =
    do (lc, fc) <- newFragment ImportCall s
       (lr, fr) <- newFragment (ImportReturn importedNames) s
       let fromModule = case importedNames of ModuleImport n _ _ -> n
                                              FromImport n _ _   -> n
           imports = Map.singleton lc (lr, fromModule)
           f = fc `mappend` fr
       return $ f { frImports = imports }

-- | Get the names imported by an 'ImportItem'.
imported :: AST.ImportItem SrcSpan
         -> StateT ConversionState TypeInferenceMonad ImportedNames
imported (AST.ImportItem dotted as _) =
    do currentModule <- gets csCurrentModule
       return $ ModuleImport (dottedName dotted)
                             currentModule
                             (fmap (\(AST.Ident name _) -> name) as)

-- | Get the names imported by an 'ImportRelative'.
fromImported :: AST.ImportRelative SrcSpan -> AST.FromItems SrcSpan
             -> StateT ConversionState TypeInferenceMonad ImportedNames
fromImported (AST.ImportRelative _ name _) (AST.ImportEverything _) =
    do currentModule <- gets csCurrentModule
       let m = maybeDottedName name
       return $ FromImport m currentModule [] -- not really supported
fromImported (AST.ImportRelative _ name _) (AST.FromItems items _) =
    do currentModule <- gets csCurrentModule
       let m = maybeDottedName name
           names = [ (n, fmap (\(AST.Ident name _) -> name) as)
                   | AST.FromItem (AST.Ident n _) as _ <- items ]
       return $ FromImport m currentModule names

maybeDottedName :: Maybe (AST.DottedName SrcSpan) -> String
maybeDottedName Nothing  = "__init__"
maybeDottedName (Just x) = dottedName x

-- | Turn a dotted name into a regular module name.
dottedName :: AST.DottedName SrcSpan -> String
dottedName [] = ""
dottedName xs = let AST.Ident name _ = last xs in name

-- | Connect @continue@ statements in the first fragment to the second fragment.
continueEdges :: Fragment -> Fragment -> Set Edge
continueEdges body loop =
    Set.fromList [(c, i) | c <- Set.toList (getContinue body),
                           i <- Set.toList (getInitial loop)]

-- | Connect @return@ statements in the first fragment to the second fragment.
returnEdges :: Fragment -> Fragment -> Set Edge
returnEdges body fx =
    Set.fromList [(rf, i) | rf <- Set.toList (getReturn body `Set.union`
                                              getFinal body),
                            i <- Set.toList (getInitial fx) ]

-- | Find module names bound by @import@ statements.
moduleNamesBound :: AST.Suite SrcSpan -> TypeInferenceMonad (Set String)
moduleNamesBound stmts = collectInScope stmts find
    where find (AST.Import items _) =
              return $ Set.fromList $ importedModuleNames items
          find _ = return Set.empty

-- | Extract the names imported into the environment by an @import ... from
-- ...@ statement.
importedModuleNames :: [AST.ImportItem SrcSpan] -> [String]
importedModuleNames items =
    let getName (AST.ImportItem n Nothing _) = dottedName n
        getName (AST.ImportItem _ (Just (AST.Ident n _)) _) = n
    in map getName items

-- | Find names bound in the suite.
namesBound :: AST.Suite SrcSpan -> TypeInferenceMonad (Set String)
namesBound stmts = collectInScope stmts find
    where find (AST.Import items _) =
              return $ Set.fromList $ importedModuleNames items
          find (AST.FromImport _ (AST.ImportEverything _) _) =
              return Set.empty -- not really supported
          find (AST.FromImport _ (AST.FromItems items _) _) =
              let getName (AST.FromItem (AST.Ident n _) Nothing _) = n
                  getName (AST.FromItem _ (Just (AST.Ident n _)) _) = n
              in return $ Set.fromList $ map getName items
          find (AST.Assign lhs _ _) =
              return $ Set.fromList (targetNames lhs)
          find (AST.AugmentedAssign (AST.Var (AST.Ident name _) _) _ _ _) =
              return $ Set.singleton name
          find (AST.Delete exprs _) =
              let f (AST.Var (AST.Ident name _) _) = Set.singleton name
                  f _                              = Set.empty
              in return $ Set.unions (map f exprs)
          find (AST.Fun (AST.Ident name _) _ _ _ _) =
              return $ Set.singleton name
          find (AST.Class (AST.Ident name _) _ _ _) =
              return $ Set.singleton name
          find (AST.For targets _ body els _) =
              do boundInside <- collectInScope (body ++ els) find
                 let boundByLoop = Set.fromList (targetNames targets)
                 return $ boundInside Set.\\ boundByLoop
          find (AST.With ctx body _) =
              do boundInside <- collectInScope body find
                 let boundByWith = Set.fromList (targetNames (mapMaybe snd ctx))
                 return $ boundInside Set.\\ boundByWith
          find _ = return Set.empty

-- | Find names declared @nonlocal@ in the suite.
declaredNonlocal :: AST.Suite SrcSpan -> TypeInferenceMonad (Set String)
declaredNonlocal stmts = collectInScope stmts find
    where find (AST.NonLocal ns _)      =
              return $ Set.fromList [n | AST.Ident n _ <- ns]
          find (AST.For _ _ body els _) = collectInScope (body ++ els) find
          find (AST.With _ body _)      = collectInScope body find
          find _                        = return Set.empty

-- | Find names declared @global@ in the suite.
declaredGlobal :: AST.Suite SrcSpan -> TypeInferenceMonad (Set String)
declaredGlobal stmts = collectInScope stmts find
    where find (AST.Global ns _)        =
              return $ Set.fromList [n | AST.Ident n _ <- ns]
          find (AST.For _ _ body els _) = collectInScope (body ++ els) find
          find (AST.With _ body _)      = collectInScope body find
          find _                        = return Set.empty

-- | Apply a function to all simple statements, and @for@ and @with@
-- statements, in one scope and collect the results.
collectInScope :: Ord a => AST.Suite SrcSpan
                        -> (AST.Statement SrcSpan -> TypeInferenceMonad (Set a))
                        -> TypeInferenceMonad (Set a)
collectInScope stmts f =
    do results <- mapM f' stmts
       return $ Set.unions results
    where f' (AST.While _ body els _) =
              do list <- mapM f' (body ++ els)
                 return $ Set.unions list
          f' (AST.Conditional guards els _) =
              do list <- mapM f' (concatMap snd guards ++ els)
                 return $ Set.unions list
          f' (AST.Try body _ els finally _) =
              do list <- mapM f' (body ++ els ++ finally)
                 return $ Set.unions list
          f' stmt = f stmt

-- | Assuming the given list is the target of an assignment, return the names
-- it binds.
targetNames :: [AST.Expr SrcSpan] -> [String]
targetNames targets =
    concatMap f targets
    where f (AST.Var (AST.Ident n _) _) = [n]
          f (AST.Tuple exprs _)         = concatMap f exprs
          f (AST.List exprs _)          = concatMap f exprs
          f (AST.Paren expr _)          = f expr
          f _                           = []

-- | Assuming the given expression is the target of an assignment, convert it
-- to the Target type.
toTarget :: (String -> StateT ConversionState TypeInferenceMonad Identifier)
         -> AST.Expr SrcSpan
         -> StateT ConversionState TypeInferenceMonad (Fragment, Target)
toTarget lookupName (AST.Var (AST.Ident name _) _) =
    do identifier <- lookupName name
       return (EmptyFragment, TargetIdentifier identifier)
toTarget _ (AST.BinaryOp (AST.Dot _) e (AST.Var (AST.Ident name _) _) _) =
    do (f, e) <- toExpression e
       return (f, TargetAttributeRef $ AttributeRef e name)
toTarget _ (AST.Subscript x e _) =
    do (xf, xe) <- toExpression x
       (ef, _) <- toExpression e
       return (xf `mappend` ef, TargetSubscription $ Subscription xe)
toTarget _ (AST.SlicedExpr x s _) =
    do (xf, xe) <- toExpression x
       sf <- mapM fragmentForSlice s
       return (mconcat (xf : sf), TargetSlicing $ Slicing xe)
toTarget lookupName (AST.Tuple es _) =
    do list <- mapM (toTarget lookupName) es
       let (fs, ts) = unzip list
       return (mconcat fs, TargetList ts)
toTarget lookupName (AST.List es _) =
    do list <- mapM (toTarget lookupName) es
       let (fs, ts) = unzip list
       return (mconcat fs, TargetList ts)
toTarget lookupName (AST.Starred e _) =
    do (f, t) <- toTarget lookupName e
       return (f, StarTarget t)
toTarget lookupName (AST.Paren e _) = toTarget lookupName e
toTarget _ e =
    throwError $ CFGError $ "invalid expression in target: " ++ show e

-- | Assuming the given expression is the target of an augmented assignment,
-- convert it to the AugTarget type.
toAugTarget :: AST.Expr SrcSpan
            -> StateT ConversionState TypeInferenceMonad (Fragment, AugTarget)
toAugTarget (AST.Var (AST.Ident name _) _) =
    do identifier <- getI name
       return (EmptyFragment, AugTargetIdentifier identifier)
toAugTarget (AST.BinaryOp (AST.Dot _) e (AST.Var (AST.Ident name _) _) _) =
    do (f, e) <- toExpression e
       return (f, AugTargetAttributeRef $ AttributeRef e name)
toAugTarget (AST.Subscript x e _) =
    do (xf, xe) <- toExpression x
       (ef, _) <- toExpression e
       return (xf `mappend` ef, AugTargetSubscription $ Subscription xe)
toAugTarget (AST.SlicedExpr x s _) =
    do (xf, xe) <- toExpression x
       sf <- mapM fragmentForSlice s
       return (mconcat (xf : sf), AugTargetSlicing $ Slicing xe)
toAugTarget (AST.Paren e _) = toAugTarget e
toAugTarget e =
    throwError $ CFGError $ msg ++ show e
        where msg = "invalid expression in target for augmented assignment: "

-- | Convert parameters.
toParameter :: Scope
            -> AST.Parameter SrcSpan
            -> StateT ConversionState TypeInferenceMonad [(Fragment, Parameter)]
toParameter scope (AST.Param (AST.Ident name _) _ Nothing _) =
    returnP $ Parameter (Name scope name) Nothing
toParameter scope (AST.Param (AST.Ident name _) _ (Just d) srcSpan) =
    do (f, e) <- toExpression d
       i <- newIdentifier
       fAssign <- newFragment' (Assignment [TargetIdentifier i] e) srcSpan
       return [ (f `mappend` fAssign,
                 Parameter (Name scope name) (Just $ Identifier i)) ]
toParameter scope (AST.VarArgsPos (AST.Ident name _) _ _) =
    returnP $ StarParameter (Name scope name)
toParameter scope (AST.VarArgsKeyword (AST.Ident name _) _ _) =
    returnP $ StarStarParameter (Name scope name)
toParameter scope (AST.EndPositional _) = return []
toParameter scope (AST.UnPackTuple _ _ _) =
    throwError $ CFGError "tuple unpack parameters don't exist in Python 3"

-- | Return the name the parameter, if any.
paramName :: AST.Parameter SrcSpan -> TypeInferenceMonad [String]
paramName (AST.Param (AST.Ident name _) _ _ _)        = return [name]
paramName (AST.VarArgsPos (AST.Ident name _) _ _)     = return [name]
paramName (AST.VarArgsKeyword (AST.Ident name _) _ _) = return [name]
paramName (AST.EndPositional _)                       = return []
paramName (AST.UnPackTuple _ _ _)                     =
    throwError $ CFGError "tuple unpack parameters don't exist in Python 3"


-- | Convert expression.
toExpression :: AST.Expr SrcSpan
             -> StateT ConversionState TypeInferenceMonad (Fragment, Expression)

-- Parenthesized expression.
toExpression (AST.Paren e _) = toExpression e

-- Variable.
toExpression (AST.Var (AST.Ident name _) _) =
    do identifier <- getI name
       returnExpression $ Identifier identifier

-- Literal constants.
toExpression (AST.Int val _ _)       = returnLiteral $ IntegerLiteral val
toExpression (AST.Float val _ _)     = returnLiteral $ FloatLiteral val
toExpression (AST.Imaginary val _ _) = returnLiteral $ ImagLiteral val
toExpression (AST.Bool val _)        = returnLiteral $ BoolLiteral val
toExpression (AST.None _)            = returnLiteral NoneLiteral
toExpression (AST.ByteStrings l _)   = returnLiteral $ ByteStringLiteral $
                                                           concat l
toExpression (AST.Strings l _)       = returnLiteral $ StringLiteral (concat l)

-- Function call.
toExpression (AST.Call e args s) =
    do (f1, e1) <- toExpression e
       list <- mapM toArgument args
       let (fs, as) = unzip list
           f2 = mconcat (f1 : fs)
       i <- newIdentifier
       lc <- newLabel
       lr <- newLabel
       pos <- lift $ toPosition s
       let f3 = fragment (Map.fromList [(lc, (FunctionCall e1 as lr, pos)),
                                        (lr, (FunctionReturn e1 i lc, pos))])
                         Set.empty
                         (Set.singleton lc)
                         (Set.singleton lr)
       return (f2 `mappend` f3, Identifier i)

-- Subscription and slicing.
toExpression (AST.Subscript x e _) =
    do (xf, xe) <- toExpression x
       (ef, _) <- toExpression e
       return (xf `mappend` ef, SubscriptionExpression $ Subscription xe)
toExpression (AST.SlicedExpr x s _) =
    do (xf, xe) <- toExpression x
       sf <- mapM fragmentForSlice s
       return (mconcat (xf : sf), SlicingExpression $ Slicing xe)

-- Conditional expression ('left if cond else right')
toExpression (AST.CondExpr left cond right _) =
    do (fcBefore, ec) <- toExpression cond
       (flBefore, el) <- toExpression left
       (frBefore, er) <- toExpression right
       i <- newIdentifier
       fc <- newFragment' (Condition ec) (AST.annot cond)
       fl <- newFragment' (Assignment [TargetIdentifier i] el) (AST.annot left)
       fr <- newFragment' (Assignment [TargetIdentifier i] er) (AST.annot right)
       let c = fcBefore `mappend` fc
           l = flBefore `mappend` fl
           r = frBefore `mappend` fr
           nodes = Map.unions $ map getNodes [c, l, r]
           edges = Set.unions $ [c --> r, c --> l] ++ map getEdges [c, l, r]
           final = getFinal l `Set.union` getFinal r
       return (fragment nodes edges (frInitial c) final, Identifier i)

-- Binary operation.
toExpression (AST.BinaryOp (AST.Dot _)
                           (AST.Var (AST.Ident a _) _)
                           (AST.Var (AST.Ident b _) _) _) =
    do otherModules <- gets csOtherModules
       if a `Set.member` otherModules
           then do identifier <- mkIdentifier a b
                   returnExpression $ Identifier identifier
           else do identifier <- getI a
                   returnExpression $
                       AttributeReference $
                           AttributeRef (Identifier identifier) b
toExpression (AST.BinaryOp (AST.Dot _) a b _) =
    do (f, e) <- toExpression a
       case b of
           AST.Var (AST.Ident name _) _ ->
               return (f, AttributeReference (AttributeRef e name))
           _                         ->
               throwError $ CFGError "invalid attribute reference"
toExpression (AST.BinaryOp op a b _) =
    do (f, e) <- toExpression a
       o <- lift $ toBinaryOperator op
       (f', e') <- toExpression b
       return (f `mappend` f', BinaryOperation e o e')

-- Unary operation.
toExpression (AST.UnaryOp op expr _) =
    do o <- lift $ toUnaryOperator op
       (f, e) <- toExpression expr
       return (f, UnaryOperation o e)

-- Lambda expression (anonymous function).
toExpression (AST.Lambda params body s) =
    do functionId <- newFunctionId
       i <- newIdentifier
       (ld, fd) <- newFragment (Def i functionId) s
       list <- mapM (toParameter (FunctionScope functionId)) params
       let (pfs, ps) = unzip (concat list)
       (ln, fn) <- newFragment (FunctionEntry ps) s
       (lx, fx) <- newFragment (FunctionExit ps) s
       paramNames <- lift $ mapM paramName params
       let newBindings    = [(n, Name (FunctionScope functionId) n)
                            | n <- concat paramNames]
       (fbBefore, be) <- withBindings newBindings (toExpression body)
       (lb, fb) <- newFragment (Return $ Just be) s
       let fBody = fbBefore `mappend` fb
       let fs      = pfs ++ [fd, fn, fx, fBody]
           nodes   = Map.unions (map getNodes fs)
           edges   = Set.singleton (lb, lx)
                     `Set.union` getEdges fBody
                     `Set.union` (fn --> fBody)
           initial = Set.singleton ld
           final   = Set.singleton ld
           break   = Set.empty
           continu = Set.empty
           ret     = Set.empty
           imports = Map.empty
           ft      = Map.insert functionId (ln, lx) (getFunctionTable fBody)
       return (Fragment nodes edges initial final break continu ret imports ft,
               Identifier i)

-- | Tuples, lists, sets and dictionaries.
toExpression (AST.Tuple es _) =
    do list <- mapM toExpression es
       let (fs, exprs) = unzip list
       return (mconcat fs, TupleExpression exprs)
toExpression (AST.List es _) =
    do list <- mapM toExpression es
       let (fs, exprs) = unzip list
       return (mconcat fs, ListExpression exprs)
toExpression (AST.Set es _) =
    do list <- mapM toExpression es
       let (fs, exprs) = unzip list
       return (mconcat fs, SetExpression exprs)
toExpression (AST.Dictionary es _) =
    let pairToE (a, b) = do (f1, e1) <- toExpression a
                            (f2, e2) <- toExpression b
                            return (f1 `mappend` f2, (e1, e2))
    in do list <- mapM pairToE es
          let (fs, exprs) = unzip list
          return (mconcat fs, DictionaryExpression exprs)

-- List, set and dictionary comprehensions.
toExpression (AST.ListComp comprehension s) =
    convertCompr comprehension toExpression ListComprehension
toExpression (AST.SetComp comprehension _) =
    convertCompr comprehension toExpression SetComprehension
toExpression (AST.DictComp comprehension _) =
    convertCompr comprehension f DictComprehension
    where f (a, b) = do (fa, ea) <- toExpression a
                        (fb, eb) <- toExpression b
                        return (fb `mappend` fb, (ea, eb))

-- Generator expression and yield statement -- not really supported.
toExpression (AST.Generator _ _) = returnExpression Generator
toExpression (AST.Yield Nothing _) = returnExpression $ Yield Nothing
toExpression (AST.Yield (Just e) _) =
    do (f, exp) <- toExpression e
       return (f, Yield $ Just exp)

-- Expressions that should not occur here.
toExpression (AST.Starred _ _) =
    throwError $ CFGError "starred expression outside of assignment"
toExpression (AST.LongInt _ _ _) =
    throwError $ CFGError "long ints don't exist in Python 3"
toExpression (AST.Ellipsis _) =
    throwError $ CFGError "ellipsis in expression"
toExpression (AST.StringConversion _ _) =
    throwError $ CFGError "backquotes don't exist in Python 3"


-- | Convert comprehension.
convertCompr :: AST.Comprehension a SrcSpan
             -> (a -> StateT ConversionState TypeInferenceMonad (Fragment, b))
             -> (Identifier -> b -> ProgramPoint)
             -> StateT ConversionState TypeInferenceMonad (Fragment, Expression)
convertCompr (AST.Comprehension comprehensionExpr compFor s)
             convertComprehensionExpr
             pp =
    do forLoopId <- newForLoopId
       let newBindings = [(n, Name (ForLoopScope forLoopId) n)
                         | n <- compForNames compFor]
           newIdentifiers = map snd newBindings
       i <- newIdentifier
       (eBefore, e) <- withBindings newBindings $
                           convertComprehensionExpr comprehensionExpr
       fc <- newFragment' (pp i e) s
       f <- withBindings newBindings $ compForToFragment compFor
                                                         (eBefore `mappend` fc)
       (sn, sx) <- scopeFragments newIdentifiers s
       return (sn `mappend` f `mappend` sx, Identifier i)

-- | Create fragment for the @for ... in ...@ part of a comprehension.
compForToFragment :: AST.CompFor SrcSpan -> Fragment -> Conversion
compForToFragment (AST.CompFor targets generator next s) inner =
    do (gBefore, g) <- toExpression generator
       i <- newIdentifier
       gAssign <- newFragment' (Assignment [TargetIdentifier i] g) s
       let g = gBefore `mappend` gAssign
       targetList <- mapM (toTarget getI) targets
       let (fts, ts) = unzip targetList
           tBefore = mconcat fts
       ft <- newFragment' (ForAssign (TargetList ts) i) s
       inner' <- compIterToFragment next inner
       let ft'     = tBefore `mappend` ft
           fs      = [g, ft', inner']
           nodes   = Map.unions (map getNodes fs)
           edges   = Set.unions (map getEdges fs)
                     `Set.union` (g --> ft')
                     `Set.union` (ft' --> inner')
                     `Set.union` (inner' --> ft')
           initial = frInitial $ if nullF g then ft' else g
           final   = frFinal ft'
       return $ fragment nodes edges initial final

-- | Create fragment for the @if ...@ part of a comprehension.
compIfToFragment :: AST.CompIf SrcSpan -> Fragment -> Conversion
compIfToFragment (AST.CompIf cond next s) inner =
    do (fcBefore, ec) <- toExpression cond
       fc <- newFragment' (Condition ec) (AST.annot cond)
       inner' <- compIterToFragment next inner
       return $ fcBefore `mappend` fc `mappend` inner'

-- | Create fragment for part of a comprehension.
compIterToFragment :: Maybe (AST.CompIter SrcSpan) -> Fragment -> Conversion
compIterToFragment Nothing                  inner = return inner
compIterToFragment (Just (AST.IterFor f _)) inner = compForToFragment f inner
compIterToFragment (Just (AST.IterIf i _))  inner = compIfToFragment i inner

-- | Find names bound in a list comprehension.
compForNames :: AST.CompFor SrcSpan -> [String]
compForNames (AST.CompFor targets _ next _) = targetNames targets
                                           ++ compIterNames next

-- | Find names bound in a list comprehension.
compIfNames :: AST.CompIf SrcSpan -> [String]
compIfNames (AST.CompIf _ next _) = compIterNames next

-- | Find names bound in a list comprehension.
compIterNames :: Maybe (AST.CompIter SrcSpan) -> [String]
compIterNames (Just (AST.IterFor f _)) = compForNames f
compIterNames (Just (AST.IterIf f _))  = compIfNames f
compIterNames Nothing                  = []

-- | Convert funcation call argument.
toArgument :: AST.Argument SrcSpan
           -> StateT ConversionState TypeInferenceMonad (Fragment, Argument)
toArgument (AST.ArgExpr expr _) =
    do (f, e) <- toExpression expr
       return (f, PositionalArgument e)
toArgument (AST.ArgKeyword (AST.Ident k _) expr _) =
    do (f, e) <- toExpression expr
       return (f, KeywordArgument k e)
toArgument (AST.ArgVarArgsPos expr _) =
    do (f, e) <- toExpression expr
       return (f, StarArgument e)
toArgument (AST.ArgVarArgsKeyword expr _) =
    do (f, e) <- toExpression expr
       return (f, StarStarArgument e)

-- | Convert a slice expression.
fragmentForSlice :: AST.Slice SrcSpan -> Conversion
fragmentForSlice (AST.SliceProper l u s _) =
    do f1 <- f l
       f2 <- f u
       f3 <- case s of Nothing -> return EmptyFragment
                       Just e  -> f e
       return $ f1 `mappend` f2 `mappend` f3
    where f Nothing  = return EmptyFragment
          f (Just e) = do (f, _) <- toExpression e
                          return f
fragmentForSlice (AST.SliceExpr e _)       = do (f, _) <- toExpression e
                                                return f
fragmentForSlice (AST.SliceEllipsis _)     = return EmptyFragment

returnLiteral l = return (EmptyFragment, Literal l)
returnExpression e = return (EmptyFragment, e)
returnP p = return [(EmptyFragment, p)]

-- | Convert a unary operator.
toUnaryOperator :: AST.Op SrcSpan -> TypeInferenceMonad UnaryOperator
toUnaryOperator (AST.Not _)    = return BooleanNot
toUnaryOperator (AST.Minus _)  = return UnaryMinus
toUnaryOperator (AST.Plus _)   = return UnaryPlus
toUnaryOperator (AST.Invert _) = return Invert
toUnaryOperator op             =
    throwError $ CFGError ("not a unary operator: " ++ show op)

-- | Convert a binary operator.
toBinaryOperator :: AST.Op SrcSpan -> TypeInferenceMonad BinaryOperator
toBinaryOperator (AST.And _)               = return BooleanAnd
toBinaryOperator (AST.Or _)                = return BooleanOr
toBinaryOperator (AST.Exponent _)          = return Exponent
toBinaryOperator (AST.LessThan _)          = return Lt
toBinaryOperator (AST.GreaterThan _)       = return Gt
toBinaryOperator (AST.Equality _)          = return Eq
toBinaryOperator (AST.GreaterThanEquals _) = return GEq
toBinaryOperator (AST.LessThanEquals _)    = return LEq
toBinaryOperator (AST.NotEquals _)         = return NEq
toBinaryOperator (AST.In _)                = return In
toBinaryOperator (AST.Is _)                = return Is
toBinaryOperator (AST.IsNot _)             = return IsNot
toBinaryOperator (AST.NotIn _)             = return NotIn
toBinaryOperator (AST.BinaryOr _)          = return BitwiseOr
toBinaryOperator (AST.Xor _)               = return BitwiseXor
toBinaryOperator (AST.BinaryAnd _)         = return BitwiseAnd
toBinaryOperator (AST.ShiftLeft _)         = return LeftShift
toBinaryOperator (AST.ShiftRight _)        = return RightShift
toBinaryOperator (AST.Multiply _)          = return Times
toBinaryOperator (AST.Plus _)              = return Plus
toBinaryOperator (AST.Minus _)             = return Minus
toBinaryOperator (AST.Divide _)            = return Div
toBinaryOperator (AST.FloorDivide _)       = return DivDiv
toBinaryOperator (AST.Modulo _)            = return Modulo
toBinaryOperator (AST.NotEqualsV2 _)       =
    throwError $ CFGError "<> operator doesn't exist in Python 3"
toBinaryOperator op             =
    throwError $ CFGError ("not a binary operator: " ++ show op)

-- | Convert an assigment operator.
toAssignmentOperator :: AST.AssignOp SrcSpan -> AssignmentOperator
toAssignmentOperator (AST.PlusAssign _)       = PlusGets
toAssignmentOperator (AST.MinusAssign _)      = MinusGets
toAssignmentOperator (AST.MultAssign _)       = TimesGets
toAssignmentOperator (AST.DivAssign _)        = DivGets
toAssignmentOperator (AST.ModAssign _)        = ModGets
toAssignmentOperator (AST.PowAssign _)        = ExpGets
toAssignmentOperator (AST.BinAndAssign _)     = AndGets
toAssignmentOperator (AST.BinOrAssign _)      = OrGets
toAssignmentOperator (AST.BinXorAssign _)     = XorGets
toAssignmentOperator (AST.LeftShiftAssign _)  = LeftShiftGets
toAssignmentOperator (AST.RightShiftAssign _) = RightShiftGets
toAssignmentOperator (AST.FloorDivAssign _)   = DivDivGets

-- | Convert a source code position.
toPosition :: SrcSpan -> TypeInferenceMonad Position
toPosition (SpanCoLinear filename row _ _)    = return $ Position filename row
toPosition (SpanMultiLine filename row _ _ _) = return $ Position filename row
toPosition (SpanPoint filename row _)         = return $ Position filename row
toPosition SpanEmpty                          =
    throwError $ CFGError "missing source location information"

-- | Create ScopeEntry and ScopeExit fragments.
scopeFragments :: [Identifier] -> SrcSpan
               -> StateT ConversionState TypeInferenceMonad (Fragment, Fragment)
scopeFragments newIdentifiers srcSpan =
    do sn <- newFragment' (ScopeEntry newIdentifiers) srcSpan
       sx <- newFragment' (ScopeExit newIdentifiers) srcSpan
       return (sn, sx)


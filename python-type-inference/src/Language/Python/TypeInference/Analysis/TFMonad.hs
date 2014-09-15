-- | Defines a monad for transfer functions.
module Language.Python.TypeInference.Analysis.TFMonad (
    goFlowInsensitive,
    TFState,
    TF,
    simpleTransferFunction,
    callTransferFunction,
    getType,
    getTypeWithDefault,
    setType,
    removeType,
    getAllFromL,
    removeFromL,
    extractFromL,
    getGlobalTypes,
    modifyType,
    modifyAttribute,
    cpType,
    mvType,
    clsAttr,
    instAttr,
    classOfInstance
) where

import Control.Monad.State hiding (join)
import Data.Map (Map)
import Data.Maybe (catMaybes, fromMaybe, listToMaybe)
import Language.Analysis.DFA.Lattice
import Language.Analysis.DFA.MonotoneFramework
import Language.Python.TypeInference.Analysis.MapLattice
import Language.Python.TypeInference.Analysis.TypeLattice
import Language.Python.TypeInference.CFG.CFG
import qualified Data.Map as Map
import qualified Data.Set as Set

-- | Use flow-insensitive analysis for the identifier?
goFlowInsensitive :: Bool -> Identifier -> Bool
goFlowInsensitive _     (ClassIdentifier _)        = True
goFlowInsensitive _     (InstanceIdentifier _)     = True
goFlowInsensitive _     (Name (ExternalScope _) _) = True
goFlowInsensitive True  (Name (ModuleScope _) _)   = True
goFlowInsensitive _     _                          = False

-- | State used and changed by transfer functions.
data TFState = TFState {
                   tfsL              :: L,
                   tfsGlobalL        :: L,
                   tfsChangedGlobalL :: Bool,
                   tfsUsedGlobalL    :: Bool,
                   tfsFiModuleScope  :: Bool
               }

initialTFState :: Bool -> L -> L -> TFState
initialTFState fiModuleScope l gl = TFState l gl False False fiModuleScope

-- | Monad for transfer functions.
type TF = State TFState

-- | Create a 'SimpleTransferFunction' given a flag specifying if
-- flow-insensitive analysis for module-scope identifiers is used, and a
-- computation in the 'TF' monad.
simpleTransferFunction :: Bool -> TF () -> SimpleTF L
simpleTransferFunction fiModuleScope tf =
    f
    where f :: L -> L -> (L, Maybe L, Bool)
          f l gl = let TFState l' gl' changedGL usedGL _ =
                           execState tf (initialTFState fiModuleScope l gl)
                       maybeGL' = if changedGL then Just gl' else Nothing
                   in (l', maybeGL', usedGL)

-- | Create a 'CallTransferFunction' given a flag specifying if
-- flow-insensitive analysis for module-scope identifiers is used, and a
-- computation in the 'TF' monad.
callTransferFunction :: Bool -> TF ([Label], Bool) -> CallTF L
callTransferFunction fiModuleScope tf =
    f
    where f :: L -> L -> ([Label], Bool, L, Maybe L, Bool)
          f l gl = let ((fs, d), TFState l' gl' changedGL usedGL _) =
                           runState tf (initialTFState fiModuleScope l gl)
                       maybeGL' = if changedGL then Just gl' else Nothing
                   in (fs, d, l', maybeGL', usedGL)

setChangedGlobalL, setUsedGlobalL :: TF ()
setChangedGlobalL = modify $ \s -> s { tfsChangedGlobalL = True }
setUsedGlobalL    = modify $ \s -> s { tfsUsedGlobalL = True }

-- | Retrieve the type for an identifier.
getType :: Identifier -> TF (Maybe UnionType)
getType i = do fiModuleScope <- gets tfsFiModuleScope
               let useGlobal = goFlowInsensitive fiModuleScope i
                   lookHere = if useGlobal then tfsGlobalL else tfsL
               when useGlobal setUsedGlobalL
               l <- gets lookHere
               return $ Map.lookup i l

-- | Retrieve the type for an identifier; return 'bot' if the identifier is not
-- in the lattice value.
getTypeWithDefault :: UnionType -> Identifier -> TF UnionType
getTypeWithDefault def i = do mt <- getType i
                              return $ fromMaybe def mt

-- | Set the type for an identifier.
setType :: Identifier -> UnionType -> TF ()
setType i t = do fiModuleScope <- gets tfsFiModuleScope
                 let useGlobal = goFlowInsensitive fiModuleScope i
                     f s = if useGlobal
                           then let l = tfsGlobalL s
                                    t' = t `join` Map.findWithDefault bot i l
                                in s {tfsGlobalL = Map.insert i t' l }
                           else s {tfsL = Map.insert i t (tfsL s)}
                 when useGlobal setChangedGlobalL
                 modify f

-- | Remove identifier/type.
removeType :: Identifier -> TF ()
removeType i = do fiModuleScope <- gets tfsFiModuleScope
                  let useGlobal = goFlowInsensitive fiModuleScope i
                      f s = s {tfsL = Map.delete i (tfsL s)}
                  unless useGlobal (modify f)

-- | Retrieve the mappings for all identifier that match a predicate from the
-- lattice value. The global lattice value is not used.
getAllFromL :: (Identifier -> Bool) -> TF [(Identifier, UnionType)]
getAllFromL p = do l <- gets tfsL
                   return $ filter (p . fst) (Map.toList l)

-- | Remove the mappings for identifiers that match a predicate from the
-- lattice value. The global lattice value is not used.
removeFromL :: (Identifier -> Bool) -> TF ()
removeFromL p = do s <- get
                   let l = tfsL s
                       (_, b) = Map.partitionWithKey (\k _ -> p k) l
                   put $ s { tfsL = b }

-- | Remove and return the mappings for identifiers that match a predicate from
-- the lattice value. The global lattice value is not used.
extractFromL :: (Identifier -> Bool) -> TF (Map Identifier UnionType)
extractFromL p = do s <- get
                    let l = tfsL s
                        (a, b) = Map.partitionWithKey (\k _ -> p k) l
                    put $ s { tfsL = b }
                    return a

-- | Return the mappings for identifiers that match a predicate from the global
-- lattice value.
getGlobalTypes :: (Identifier -> Bool) -> TF (Map Identifier UnionType)
getGlobalTypes p = do l <- gets tfsGlobalL
                      setUsedGlobalL
                      return $ Map.filterWithKey (\k _ -> p k) l

-- | Modify the type for the identifier.
modifyType :: Identifier -> (UnionType -> UnionType) -> TF ()
modifyType i f = do mt <- getType i
                    case mt of Nothing -> return ()
                               Just t  -> setType i (f t)

-- | Update the type of an expression of the form /identifier.attribute/.
modifyAttribute :: Identifier -> String -> (UnionType -> UnionType) -> TF ()
modifyAttribute i attr f =
    do mt <- getType i
       case mt of
           Nothing      -> return ()
           Just UTyTop  -> return ()
           Just (UTy s) -> do types <- mapM g (Set.toList s)
                              setType i (joinAll types)
    where g :: ValueType -> TF UnionType
          -- reference types: modify corresponding global type instead
          g t@(ClassType (ClsRef classId)) =
              do modifyAttribute (ClassIdentifier classId) attr f
                 return $ oneType t
          g t@(InstanceType (InstRef classId)) =
              do modifyAttribute (InstanceIdentifier classId) attr f
                 return $ oneType t
          -- class and instance types: modify attribute
          g (ClassType (ClsTy classId sup env)) =
              return $ oneType $ ClsTy classId sup (updEnv env)
          g (InstanceType (InstTy cls env)) =
              return $ oneType $ InstTy cls (updEnv env)
          g _ = return bot
          updEnv = Map.alter (Just . f') attr
          f' Nothing  = f bot
          f' (Just t) = f t

-- | @cpType from to@ sets the type of @to@ to the type of @from@.
cpType :: Identifier -> Identifier -> TF ()
cpType from to = do mt <- getType from
                    case mt of Just t  -> setType to t
                               Nothing -> return ()

-- | @cpType from to@ sets the type of @to@ to the type of @from@ and removes
-- the entry for @from@.
mvType :: Identifier -> Identifier -> TF ()
mvType from to = do mt <- getType from
                    case mt of Just t  -> do removeType from
                                             setType to t
                               Nothing -> return ()

-- | Look up the attribute in the given class type (and the types of its
-- superclasses).
clsAttr :: String -> ClassType -> TF (Maybe UnionType)
clsAttr name (ClsRef classId) =
    do mt <- getType $ ClassIdentifier classId
       case mt of
           Nothing      -> return Nothing
           Just UTyTop  -> return $ Just UTyTop
           Just (UTy s) -> do let helper :: ValueType -> TF (Maybe UnionType)
                                  helper (ClassType ct) = clsAttr name ct
                                  helper _              = return $ Just bot
                              list <- mapM helper (Set.toList s)
                              case catMaybes list of
                                  [] -> return Nothing
                                  ts -> return $ Just $ joinAll ts
clsAttr name (ClsTy _ sup env) =
   case Map.lookup name env of
       (Just t) -> return $ Just t
       Nothing  -> do attrs <- mapM (clsAttr name) sup
                      return $ listToMaybe $ catMaybes attrs

-- | Look up the attribute in the given instance type (and its class type).
instAttr :: String -> InstanceType -> TF (Maybe UnionType)
instAttr name (InstRef classId) =
    do mt <- getType $ InstanceIdentifier classId
       case mt of
           Nothing      -> return Nothing
           Just UTyTop  -> return $ Just UTyTop
           Just (UTy s) -> do let helper :: ValueType -> TF (Maybe UnionType)
                                  helper (InstanceType it) = instAttr name it
                                  helper _                 = return $ Just bot
                              list <- mapM helper (Set.toList s)
                              case catMaybes list of
                                  [] -> return Nothing
                                  ts -> return $ Just $ joinAll ts
instAttr name (InstTy cls env) =
   case Map.lookup name env of
       (Just t) -> return $ Just t
       Nothing  -> clsAttr name cls

-- | Get the class type for an instance type.
classOfInstance :: InstanceType -> TF ClassType
classOfInstance (InstTy classType _) = return classType
classOfInstance (InstRef classId) =
    do mt <- getType $ InstanceIdentifier classId
       let Just (UTy s) = mt
           [InstanceType (InstTy classType _)] = Set.toList s
       return classType


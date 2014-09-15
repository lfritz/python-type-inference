-- | A type lattice for Python 3.
module Language.Python.TypeInference.Analysis.TypeLattice (
    UnionType (..),
    ValueType (..),
    BuiltinType (..),
    FunctionType (..),
    ClassType (..),
    InstanceType (..),
    HasClassId (..),
    Env,
    nabla,
    check,
    AType (..),
    oneType,
    filterType,
    filterOr,
    isBuiltin, isFunction, isClass, isInstance, orInstance, isNum,
    isIntegral, isSequence,
    isTuple, isList,
    allTypes,
    updateType,
    applyFunctionType
) where

import Control.DeepSeq
import Control.Monad (zipWithM)
import Data.List (groupBy, intercalate, partition, sortBy)
import Data.Map (Map)
import Data.Maybe (catMaybes, fromMaybe, isNothing)
import Data.Ord (comparing)
import Data.Set (Set)
import Language.Analysis.DFA.Lattice
import Language.Python.TypeInference.Common
import Text.Printf
import qualified Data.Map as Map
import qualified Data.Set as Set

-- | Union type: models types of variables.
data UnionType
    = -- | A set of types that the variable may have.
      UTy (Set ValueType)
      -- | Top element: we don't know anything about the type.
    | UTyTop
      -- | Type variable. Only to be used within function types ('FunTy').
    | TypeVariable String
    deriving (Eq, Ord)

instance NFData UnionType where
    rnf (UTy s)          = rnf $ Set.toList s
    rnf UTyTop           = ()
    rnf (TypeVariable v) = rnf v

-- | Value type: models types that values can have at runtime.
data ValueType = BuiltinType BuiltinType
               | FunctionType FunctionType
               | ClassType ClassType
               | InstanceType InstanceType
    deriving (Eq, Ord)

instance NFData ValueType where
    rnf (BuiltinType t)  = rnf t
    rnf (FunctionType t) = rnf t
    rnf (ClassType t)    = rnf t
    rnf (InstanceType t) = rnf t

-- | Builtin Python type. See section 3.2 of the language reference.
data BuiltinType = NoneType | NotImplementedType | EllipsisType | IntType
                 | BoolType | FloatType | ComplexType | StrType
                 | BytesType | BytearrayType
                 -- unparameterized collection types
                 | TupleType | ListType | SetType | FrozensetType | DictType
                 -- parameterized collection types
                 | TupleOf [UnionType] | ListOf UnionType | SetOf UnionType
                 | FrozensetOf UnionType | DictOf UnionType UnionType
    deriving (Eq, Ord)

instance NFData BuiltinType where
    rnf bt = case bt of
                 (TupleOf ts)    -> rnf ts
                 (ListOf t)      -> rnf t
                 (SetOf t)       -> rnf t
                 (FrozensetOf t) -> rnf t
                 (DictOf k v)    -> rnf (k, v)
                 _               -> ()

-- | Function type.
data FunctionType
    = -- | Function id identifying a function in the code under analysis.
      FunId FunctionId
      -- | Function type with types of arguments and type of return value.
    | FunTy [UnionType] UnionType
    deriving (Eq, Ord)

instance NFData FunctionType where
    rnf (FunId i)   = rnf i
    rnf (FunTy a r) = rnf (a, r)

-- | Class type.
data ClassType = -- | Class with class id, superclasses and class attributes.
                 ClsTy ClassId [ClassType] Env
               | -- | Reference to a global class type, used when class types
                 -- are flow-insensitive.
                 ClsRef ClassId
    deriving (Eq, Ord)

instance NFData ClassType where
    rnf (ClsTy t sup e) = rnf (t, sup, Map.toList e)
    rnf (ClsRef i)      = rnf i

-- | Class instance type.
data InstanceType = -- | Instance with class and instance attributes.
                    InstTy ClassType Env
                  | -- | Reference to a global instance type, used when
                    -- instance types are flow-insensitive.
                    InstRef ClassId
    deriving (Eq, Ord)

instance NFData InstanceType where
    rnf (InstTy t e) = rnf (t, Map.toList e)
    rnf (InstRef i)  = rnf i

-- | Type class for types from which a class id can be extracted.
class HasClassId a where
    getClassId :: a -> ClassId
instance HasClassId ClassType where
    getClassId (ClsTy classId _ _) = classId
    getClassId (ClsRef classId)    = classId
instance HasClassId InstanceType where
    getClassId (InstTy classType _) = getClassId classType
    getClassId (InstRef classId)    = classId

-- | An environment, eg, the attributes of a class or object.
type Env = Map String UnionType

instance Lattice UnionType where
    bot = UTy Set.empty
    join UTyTop  _       = UTyTop
    join _       UTyTop  = UTyTop
    join (UTy a) (UTy b) = joinTypes $ Set.toList (a `Set.union` b)
    join a b = error $ "cannot join types " ++ show a ++ " and " ++ show b

joinTypes :: [ValueType] -> UnionType
joinTypes types =
    let joinClasses l = map (ClassType . foldl1 mergeClassTypes)
                            (groupByClassId [t | ClassType t <- l])
        joinInstances l = map (InstanceType . foldl1 mergeInstanceTypes)
                              (groupByClassId [t | InstanceType t <- l])
        isTupleOf (BuiltinType (TupleOf _)) = True
        isTupleOf _                         = False
        isTuple (BuiltinType (TupleOf _)) = True
        isTuple (BuiltinType TupleType)   = True
        isTuple _                         = False
        joinTuples l =
            if all isTupleOf l
            then map (BuiltinType . foldl1 mergeTupleTypes)
                     (groupByTupleSize [t | BuiltinType t <- l])
            else [BuiltinType TupleType]
        isListOf (BuiltinType (ListOf _)) = True
        isListOf _                        = False
        joinListOfTypes ts =
            [BuiltinType $ ListOf $ joinAll [t | BuiltinType (ListOf t) <- ts]]
        isSetOf (BuiltinType (SetOf _)) = True
        isSetOf _                       = False
        joinSetOfTypes ts =
            [BuiltinType $ SetOf $ joinAll [t | BuiltinType (SetOf t) <- ts]]
        isFrozensetOf (BuiltinType (FrozensetOf _)) = True
        isFrozensetOf _                             = False
        joinFrozensetOfTypes ts =
            [BuiltinType $
                 FrozensetOf $ joinAll [t | BuiltinType (FrozensetOf t) <- ts]]
        isDictOf (BuiltinType (DictOf _ _)) = True
        isDictOf _                          = False
        joinDictOfTypes ts =
            [BuiltinType $
                 DictOf (joinAll [t | BuiltinType (DictOf t _) <- ts])
                        (joinAll [t | BuiltinType (DictOf _ t) <- ts])]
        pairs = [ (isClass, joinClasses)
                , (isInstance, joinInstances)
                , (isTuple, joinTuples)
                , (isListOf, joinListOfTypes)
                , (isSetOf, joinSetOfTypes)
                , (isFrozensetOf, joinFrozensetOfTypes)
                , (isDictOf, joinDictOfTypes)
                ]
    in UTy $ Set.fromList (splitAndMerge pairs types)

splitAndMerge :: [(a -> Bool, [a] -> [a])] -> [a] -> [a]
splitAndMerge _                [] = []
splitAndMerge []               l  = l
splitAndMerge ((p, f) : pairs) l  =
    let (yes, no) = partition p l
        current = if null yes then [] else f yes
    in current ++ splitAndMerge pairs no

-- | Group a list of class or instance types by class id.
groupByClassId :: HasClassId a => [a] -> [[a]]
groupByClassId list =
    let sorted = sortBy (comparing getClassId) list
    in groupBy (\a b -> getClassId a == getClassId b) sorted

-- | Group a list of 'TupleOf' types by tuple size.
groupByTupleSize :: [BuiltinType] -> [[BuiltinType]]
groupByTupleSize list =
    let sorted = sortBy (comparing (\(TupleOf l) -> length l)) list
    in groupBy (\(TupleOf a) (TupleOf b) -> length a == length b) sorted

-- | Merge two class types that refer to the same class.
mergeClassTypes :: ClassType -> ClassType -> ClassType
mergeClassTypes (ClsRef classId) _ = ClsRef classId
mergeClassTypes _ (ClsRef classId) = ClsRef classId
mergeClassTypes (ClsTy classId s1 e1) (ClsTy _ s2 e2) =
    ClsTy classId (mergeSuperClasses s1 s2) (mergeEnv e1 e2)

-- | Merge two instance types that refer to the same class.
mergeInstanceTypes :: InstanceType -> InstanceType -> InstanceType
mergeInstanceTypes (InstRef classId) _ = InstRef classId
mergeInstanceTypes _ (InstRef classId) = InstRef classId
mergeInstanceTypes (InstTy c1 e1) (InstTy c2 e2) =
    InstTy (mergeClassTypes c1 c2) (mergeEnv e1 e2)

mergeSuperClasses :: [ClassType] -> [ClassType] -> [ClassType]
mergeSuperClasses sup    []     = sup
mergeSuperClasses []     sup    = sup
mergeSuperClasses (a:as) (b:bs)
    | getClassId a == getClassId b = mergeClassTypes a b
                                     : mergeSuperClasses as bs
    | otherwise                    = a : mergeSuperClasses as (b:bs)

mergeEnv :: Env -> Env -> Env
mergeEnv = Map.unionWith join

-- | Merge two tuple types with the same size (number of elements).
mergeTupleTypes :: BuiltinType -> BuiltinType -> BuiltinType
mergeTupleTypes (TupleOf a) (TupleOf b) = TupleOf (zipWith join a b)

-- | Widening operator: joins two 'UnionType's and jumps to 'UTyTop' if the
-- result is too large. Parameterized with three numbers /n/, /m/ and /o/,
-- where /n/ is the maximum size of a set of types, /m/ is the maximum nesting
-- depth and /o/ is the maximum number of attributes of a class or object.
nabla :: Int -> Int -> Int -> UnionType -> UnionType -> UnionType
nabla n m o t1 t2 = limitUnionType n m o (t1 `join` t2)

-- | Limit the size of a union type; return 'UTyTop' if it is too large. The
-- parameters are the same as for 'nabla'.
limitUnionType :: Int -> Int -> Int -> UnionType -> UnionType
limitUnionType _ _ 0 _       = UTyTop
limitUnionType _ _ _ UTyTop  = UTyTop
limitUnionType n m o (UTy s)
    | Set.size s > n = UTyTop
    | otherwise      = maybe UTyTop
                             UTy
                             (do let l = Set.toList s
                                 l' <- mapM (limitValueType n m (o-1)) l
                                 return $ Set.fromList l')

-- | Limit the size of a value type; return 'Nothing' if it is too large. The
-- parameters are the same as for 'nabla'.
limitValueType :: Int -> Int -> Int -> ValueType -> Maybe ValueType
limitValueType _ _ 0 _ = Nothing
limitValueType n m o t =
    case t of
        BuiltinType (TupleOf l)     ->
            if length l > o
            then Just $ BuiltinType TupleType
            else Just $ BuiltinType $ TupleOf $ map lu l
        BuiltinType (ListOf u)      -> Just $ BuiltinType $ ListOf (lu u)
        BuiltinType (SetOf u)       -> Just $ BuiltinType $ SetOf (lu u)
        BuiltinType (FrozensetOf u) -> Just $ BuiltinType $ FrozensetOf (lu u)
        BuiltinType (DictOf k v)    -> Just $ BuiltinType $ DictOf (lu k) (lu v)
        ClassType c                 -> do c' <- limitClassType n m o c
                                          return $ ClassType c'
        InstanceType (InstTy cls env)
            | Map.size env > o -> Nothing
            | otherwise        -> do cls' <- limitClassType n m (o-1) cls
                                     let env' = Map.map lu env
                                     return $ InstanceType (InstTy cls' env')
        _                           -> Just t
    where lu = limitUnionType n m (o - 1)

-- | Limit the size of a class type; return 'Nothing' if it is too large. The
-- parameters are the same as for 'nabla'.
limitClassType :: Int -> Int -> Int -> ClassType -> Maybe ClassType
limitClassType _ _ _ (ClsRef classId) = Just $ ClsRef classId
limitClassType n m o (ClsTy classId sup env)
    | length sup > o   = Nothing
    | Map.size env > o = Nothing
    | otherwise        = do sup' <- mapM (limitClassType n m (o-1)) sup
                            let env' = Map.map (limitUnionType n m (o-1)) env
                            return $ ClsTy classId sup' env'

instance Show UnionType where
    show (UTy ts) | Set.null ts = "bot"
                  | otherwise   = "{" ++ commas (Set.toAscList ts) ++ "}"
    show UTyTop                 = "top"
    show (TypeVariable a)       = '!' : a

instance Read UnionType where
    readsPrec _ r =
        case lex r of
            [("!",   r1)] -> case lex r1 of
                                 [(a, r2)] -> [(TypeVariable a, r2)]
                                 _         -> []
            [("bot", r1)] -> [(UTy Set.empty, r1)]
            [("top", r1)] -> [(UTyTop, r1)]
            [("{",   r1)] ->
                case (readCommaList :: ReadS [ValueType]) r1 of
                    [(ts, r2)] ->
                        case lex r2 of
                            [("}", r3)] -> [(UTy (Set.fromList ts), r3)]
                            _           -> []
                    _              -> []
            _             -> []

readCommaList :: Read a => ReadS [a]
readCommaList = readSimpleList ","

readSemicolonList :: Read a => ReadS [a]
readSemicolonList = readSimpleList ";"

readSimpleList :: Read a => String -> ReadS [a]
readSimpleList sep r =
    case reads r of
        [(t, r1)] ->
            case lex r1 of
                [(token, r2)] | token == sep ->
                    case readSimpleList sep r2 of
                        [(ts, r3)] -> [(t : ts, r3)]
                        _          -> []
                _ -> [([t], r1)]
        _ -> [([], r)]

instance Show ValueType where
    show (BuiltinType  t) = show t
    show (FunctionType t) = show t
    show (ClassType    t) = show t
    show (InstanceType t) = show t

instance Read ValueType where
    readsPrec _ r =
        case (reads :: ReadS BuiltinType) r of
         [(t, r')] -> [(BuiltinType t, r')]
         _ -> case (reads :: ReadS FunctionType) r of
               [(t, r')] -> [(FunctionType t, r')]
               _ -> case (reads :: ReadS ClassType) r of
                     [(t, r')] -> [(ClassType t, r')]
                     _ -> case (reads :: ReadS InstanceType) r of
                           [(t, r')] -> [(InstanceType t, r')]
                           _ -> []

instance Show BuiltinType where
    show NotImplementedType = "NotImplementedType"
    show NoneType           = "NoneType"
    show EllipsisType       = "ellipsis"
    show IntType            = "int"
    show BoolType           = "bool"
    show FloatType          = "float"
    show ComplexType        = "complex"
    show StrType            = "str"
    show BytesType          = "bytes"
    show BytearrayType      = "bytearray"
    show TupleType          = "tuple"
    show ListType           = "list"
    show SetType            = "set"
    show FrozensetType      = "frozenset"
    show DictType           = "dict"
    show (TupleOf ts)       = "tuple<" ++ intercalate "; " (map show ts) ++ ">"
    show (ListOf t)         = "list<" ++ show t ++ ">"
    show (SetOf t)          = "set<" ++ show t ++ ">"
    show (FrozensetOf t)    = "frozenset<" ++ show t ++ ">"
    show (DictOf k v)       = "dict<" ++ show k ++ "; " ++ show v ++ ">"

instance Read BuiltinType where
    readsPrec _ r =
        case lex r of
            [("NotImplementedType", r')] -> [(NotImplementedType, r')]
            [("NoneType",           r')] -> [(NoneType, r')]
            [("ellipsis",           r')] -> [(EllipsisType, r')]
            [("int",                r')] -> [(IntType, r')]
            [("bool",               r')] -> [(BoolType, r')]
            [("float",              r')] -> [(FloatType, r')]
            [("complex",            r')] -> [(ComplexType, r')]
            [("str",                r')] -> [(StrType, r')]
            [("bytes",              r')] -> [(BytesType, r')]
            [("bytearray",          r')] -> [(BytearrayType, r')]
            [("tuple",              r')] ->
                case readOfList r' of [(ts, r2)] -> [(TupleOf ts, r2)]
                                      _          -> [(TupleType, r')]
            [("list",               r')] -> parameterized ListType ListOf r'
            [("set",                r')] -> parameterized SetType SetOf r'
            [("frozenset",          r')] -> parameterized FrozensetType
                                                          FrozensetOf
                                                          r'
            [("dict",               r')] ->
                case readOfList r' of [([k, v], r2)] -> [(DictOf k v, r2)]
                                      _              -> [(DictType, r')]
            _ -> []
        where parameterized :: BuiltinType -> (UnionType -> BuiltinType)
                            -> ReadS BuiltinType
              parameterized bt bto r = case readOf r of
                                           [(t, r')] -> [(bto t, r')]
                                           _         -> [(bt, r)]
              readOf :: ReadS UnionType
              readOf r =
                  case lex r of
                      [("<", r1)] ->
                          case (reads :: ReadS UnionType) r1 of
                              [(t, r2)] -> case lex r2 of
                                               [(">", r3)] -> [(t, r3)]
                                               [] -> []
                              _ -> []
                      _ -> []
              readOfList :: ReadS [UnionType]
              readOfList r =
                  case lex r of
                      [("<", r1)] ->
                          case (readSemicolonList :: ReadS [UnionType]) r1 of
                              [(ts, r2)] ->
                                  case lex r2 of
                                      [(">", r3)] -> [(ts, r3)]
                                      _ -> []
                              _ -> []
                      _ -> []

instance Show FunctionType where
    show (FunId i) = "fun" ++ show i
    show (FunTy a r) = "lamba " ++ commas a ++ " -> " ++ show r

instance Read FunctionType where
    readsPrec _ r
        | r `startsWith` "fun" =
            let r1 = drop 3 r
            in case (reads :: ReadS Int) r1 of
                   [(n, r2)] -> [(FunId n, r2)]
                   _ -> []
        | r `startsWith` "lambda " =
            let r1 = drop 7 r
            in case (readCommaList :: ReadS [UnionType]) r1 of
                   [(argTypes, r2)] ->
                       case lex r2 of
                           [("->", r3)] ->
                               case (reads :: ReadS UnionType) r3 of
                                   [(returnType, r4)] ->
                                       [(FunTy argTypes returnType, r4)]
                                   _ -> []
                           _ -> []
                   _ -> []
        | otherwise = []

instance Show ClassType where
    show (ClsTy classId sup env) =
        printf "class<%d; %s; %s>" classId (show sup) (showMapping env)
    show (ClsRef classId) =
        printf "class<%d>" classId

instance Read ClassType where
    readsPrec _ r =
        case lex r of
         [("class", r1)] ->
             case lex r1 of
              [("<", r2)] ->
                  case (reads :: ReadS Int) r2 of
                   [(classId, r3)] -> 
                       case lex r3 of
                        [(">", r4)] -> [(ClsRef classId, r4)]
                        [(";", r4)] ->
                            case (reads :: ReadS [ClassType]) r4 of
                             [(sup, r5)] ->
                                 case lex r5 of
                                  [(";", r6)] ->
                                      case readMapping r6 of
                                       [(attrs, r7)] ->
                                           case lex r7 of
                                            [(">", r8)] ->
                                                [(ClsTy classId sup attrs, r8)]
                                            _ -> []
                                       _ -> []
                                  _ -> []
                             _ -> []
                        _ -> []
                   _ -> []
              _ -> []
         _ -> []

instance Show InstanceType where
    show (InstTy cls env) =
        printf "inst<%s; %s>" (show cls) (showMapping env)
    show (InstRef classId) =
        printf "inst<%d>" classId

instance Read InstanceType where
    readsPrec _ r =
        case lex r of
         [("inst", r1)] ->
             case lex r1 of
              [("<", r2)] ->
                  case (reads :: ReadS Int) r2 of
                   [(classId, r3)] ->
                       case lex r3 of
                        [(">", r4)] -> [(InstRef classId, r4)]
                        _ -> []
                   _ -> case (reads :: ReadS ClassType) r2 of
                         [(cls, r3)] ->
                             case lex r3 of
                              [(";", r4)] ->
                                  case readMapping r4 of
                                   [(attrs, r5)] ->
                                       case lex r5 of
                                        [(">", r6)] -> [(InstTy cls attrs, r6)]
                                        _ -> []
                                   _ -> []
                              _ -> []
                         _ -> []
              _ -> []
         _ -> []

check :: (Read a, Show a, Eq a) => a -> Bool
check a = a == read (show a)

-- | Typeclass for types that describe a single Python type.
class AType a where
    toValueType :: a -> ValueType

instance AType ValueType where
    toValueType = id
instance AType BuiltinType where
    toValueType = BuiltinType
instance AType FunctionType where
    toValueType = FunctionType
instance AType ClassType where
    toValueType = ClassType
instance AType InstanceType where
    toValueType = InstanceType

-- | Create a union type containing just one value type.
oneType :: AType a => a -> UnionType
oneType t = UTy $ Set.singleton $ toValueType t

-- | Modify the given union type so that it only contains value types for which
-- the predicate is true.
filterType :: (ValueType -> Bool) -> UnionType -> UnionType
filterType _         UTyTop  = UTyTop
filterType predicate (UTy s) = UTy $ Set.filter predicate s

-- | Modify the given union type so that it only contains value types for which
-- at least one of the predicates is true.
filterOr :: [ValueType -> Bool] -> UnionType -> UnionType
filterOr predicates = filterType (isAny predicates)

-- | Is it an instance type?
isInstance :: ValueType -> Bool
isInstance (InstanceType _) = True
isInstance _                = False

-- | Is it a builtin type?
isBuiltin :: ValueType -> Bool
isBuiltin (BuiltinType _) = True
isBuiltin _               = False

-- | Is it a function type?
isFunction :: ValueType -> Bool
isFunction (FunctionType _) = True
isFunction _                = False

-- | Is it a class type?
isClass :: ValueType -> Bool
isClass (ClassType _) = True
isClass _             = False

-- | Modify the given predicate so that it is true for all instance types.
orInstance :: (ValueType -> Bool) -> ValueType -> Bool
orInstance f t = f t || isInstance t

-- | Is it a built-in numeric type?
isNum :: ValueType -> Bool
isNum (BuiltinType t) = t `elem` [IntType, BoolType, FloatType, ComplexType]
isNum _               = False

-- | Is it a built-in integral type?
isIntegral :: ValueType -> Bool
isIntegral (BuiltinType t) = t `elem` [IntType, BoolType]
isIntegral _               = False

-- | Is it a built-in sequence type (string, tuple, list)?
isSequence :: ValueType -> Bool
isSequence (BuiltinType t) =
    case t of
        TupleOf _ -> True
        ListOf _  -> True
        _         -> t `elem` [StrType, TupleType, ListType]
isSequence _ = False

-- | Is it a tuple?
isTuple :: ValueType -> Bool
isTuple (BuiltinType TupleType)   = True
isTuple (BuiltinType (TupleOf _)) = True
isTuple _                         = False

-- | Is it a list?
isList :: ValueType -> Bool
isList (BuiltinType ListType)   = True
isList (BuiltinType (ListOf _)) = True
isList _                        = False

-- | Is any of the predicates true for the value?
isAny :: [a -> Bool] -> a -> Bool
isAny predicates value = or [p value | p <- predicates]

-- | Check if the predicate holds for all value types in the union type. Always
-- false for @UTyTop@.
allTypes :: (ValueType -> Bool) -> UnionType -> Bool
allTypes _ UTyTop  = False
allTypes p (UTy s) = all p (Set.toList s)

-- | Apply the function to all value types in the union type and join the
-- results.
updateType :: (ValueType -> UnionType) -> UnionType -> UnionType
updateType f (UTy s) = joinAll $ map f (Set.toList s)
updateType _ t       = t

-- | Apply a function type ('FunTy') to a list of argument types.
applyFunctionType :: [UnionType] -> UnionType -> [UnionType] -> UnionType
applyFunctionType argTypes _ arguments
    | length argTypes /= length arguments = bot
applyFunctionType argTypes returnType arguments =
    let match :: UnionType -> UnionType -> Maybe (Map String UnionType)
        match UTyTop           _                = Just Map.empty
        match (TypeVariable a) t                = Just $ Map.singleton a t
        match (UTy a)          (UTy b)
            | Set.null (a `Set.intersection` b) = Just Map.empty
        match _                _                = Nothing
    in case zipWithM match argTypes arguments of
           Nothing      -> bot
           Just matched ->
               fromMaybe bot (replace (Map.unions matched) returnType)

class ReplaceVariables a where
    replace :: Map String UnionType -> a -> Maybe a

instance ReplaceVariables UnionType where
    replace _ UTyTop           = Just UTyTop
    replace m (TypeVariable a) = Map.lookup a m
    replace m (UTy s)          = case mapM (replace m) (Set.toList s) of
                                     Nothing -> Nothing
                                     Just l  -> Just $ UTy $ Set.fromList l

instance ReplaceVariables ValueType where
    replace m (BuiltinType t)  = do t' <- replace m t
                                    return $ BuiltinType t'
    replace m (FunctionType t) = do t' <- replace m t
                                    return $ FunctionType t'
    replace m (ClassType t)    = do t' <- replace m t
                                    return $ ClassType t'
    replace m (InstanceType t) = do t' <- replace m t
                                    return $ InstanceType t'

instance ReplaceVariables BuiltinType where
    replace m (TupleOf ts)    = do ts' <- mapM (replace m) ts
                                   return $ TupleOf ts'
    replace m (ListOf t)      = do t' <- replace m t
                                   return $ ListOf t'
    replace m (SetOf t)       = do t' <- replace m t
                                   return $ SetOf t'
    replace m (FrozensetOf t) = do t' <- replace m t
                                   return $ FrozensetOf t'
    replace m (DictOf k v)    = do k' <- replace m k
                                   v' <- replace m v
                                   return $ DictOf k' v'
    replace _ t               = Just t

instance ReplaceVariables FunctionType where
    replace _ (FunId i)   = Just $ FunId i
    replace m (FunTy a r) = do -- XXX: deal with shadowed type variables
                               a' <- mapM (replace m) a
                               r' <- replace m r
                               return $ FunTy a' r'

instance ReplaceVariables ClassType where
    replace m (ClsTy classId sup env) = do sup' <- mapM (replace m) sup
                                           env' <- replaceEnv m env
                                           return $ ClsTy classId sup' env'
    replace _ (ClsRef classId) = Just $ ClsRef classId

instance ReplaceVariables InstanceType where
    replace m (InstTy classId env) = do env' <- replaceEnv m env
                                        return $ InstTy classId env'
    replace _ (InstRef classId) = Just $ InstRef classId

replaceEnv :: Map String UnionType -> Env -> Maybe Env
replaceEnv m = mapMapM (replace m)


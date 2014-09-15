-- | Parsing user-supplied type specifications.
module Language.Python.TypeInference.UserSuppliedTypes (
    UserSuppliedTypes,
    noUserSuppliedTypes,
    parseFile
) where

import Data.List (elemIndex)
import Data.Map (Map)
import Data.Maybe (catMaybes, mapMaybe)
import Data.Set (Set)
import Language.Analysis.DFA.Lattice
import Language.Python.TypeInference.Analysis.TypeLattice
import Language.Python.TypeInference.CFG.CFG
import Language.Python.TypeInference.Common
import Language.Python.TypeInference.Error
import Text.Regex
import qualified Data.Map as Map
import qualified Data.Set as Set

-- | Information on user-supplied types: the types, the modules names used, and
-- the next class id.
type UserSuppliedTypes = (Map Identifier UnionType, Set String, Int)

noUserSuppliedTypes :: UserSuppliedTypes
noUserSuppliedTypes = (Map.empty, Set.empty, 1)

-- | Parse the contents of a file with user-supplied types. Returns a set of
-- types and the highest class id occuring in the mappings.
parseFile :: String -> TypeInferenceMonad UserSuppliedTypes
parseFile input =
    do let ls = lines input
       maybeMappings <- mapM parseLine ls
       let mappings = catMaybes maybeMappings
           f :: Map Identifier UnionType -> (I, UnionType)
             -> Map Identifier UnionType
           f m (InClass classId name, ty) =
               let i = ClassIdentifier classId
                   t = oneType $ ClsTy classId [] (Map.singleton name ty)
                   newT = case Map.lookup i m of Nothing   -> t
                                                 Just oldT -> oldT `join` t
               in Map.insert i newT m
           f m (InInstance classId name, ty) =
               let i = InstanceIdentifier classId
                   t = oneType $ InstTy (ClsRef classId) (Map.singleton name ty)
                   newT = case Map.lookup i m of Nothing   -> t
                                                 Just oldT -> oldT `join` t
               in Map.insert i newT m
           f m (InModule moduleName name, ty) =
               Map.insert (Name (ExternalScope moduleName) name) ty m
           result = Map.map addInit (foldl f Map.empty mappings)
           maxClassId = maximum $ 0 : mapMaybe (iClassId . fst) mappings
           moduleNames = Set.fromList $ mapMaybe (iModuleName . fst) mappings
       return (result, moduleNames, maxClassId + 1)

-- | Add default @__init__@ methods to classes.
addInit :: UnionType -> UnionType
addInit (UTy s) = UTy $ Set.fromList $ map h (Set.toList s)
    where h :: ValueType -> ValueType
          h (ClassType (ClsTy classId sup env))
              | not ("__init__" `Map.member` env) =
              let funTy = oneType $ FunTy [] UTyTop
                  env' = Map.insert "__init__" funTy env
              in ClassType $ ClsTy classId sup env'
          h t = t

data I = InClass ClassId String
       | InInstance ClassId String
       | InModule String String
    deriving (Eq, Ord)

iClassId :: I -> Maybe ClassId
iClassId (InClass classId _)    = Just classId
iClassId (InInstance classId _) = Just classId
iClassId _                      = Nothing

iModuleName :: I -> Maybe String
iModuleName (InModule moduleName _) = Just moduleName
iModuleName _                       = Nothing

parseLine :: String -> TypeInferenceMonad (Maybe (I, UnionType))
parseLine l =
    let l' = dropWhitespace l
    in if null l'
       then return Nothing
       else case elemIndex ':' l' of
                Nothing -> err $ "cannot parse line: " ++ l
                Just i  -> do let (a, b) = splitAt i l'
                              identifier <- parseIdentifier $ dropWhitespace a
                              unionType <- parseType $ dropWhitespace (tail b)
                              return $ Just (identifier, unionType)

parseIdentifier :: String -> TypeInferenceMonad I
parseIdentifier s =
    let clsRegex   = mkRegex "class([0-9]+)[ \t]*\\.[ \t]*([a-zA-Z_]+)"
        instRegex  = mkRegex "instance([0-9]+)[ \t]*\\.[ \t]*([a-zA-Z_]+)"
        otherRegex = mkRegex "([a-zA-Z]+)[ \t]*\\.[ \t]*([a-zA-Z_]+)"
        parseFail  = err $ "cannot parse identifier: " ++ s
    in case matchRegex clsRegex s of
           Just [a, b] ->
               case reads a of
                   [(classId, "")] -> return $ InClass classId b
                   _               -> parseFail
           Nothing -> case matchRegex instRegex s of
               Just [a, b] ->
                   case reads a of
                       [(classId, "")] -> return $ InInstance classId b
                       _               -> parseFail
               Nothing -> case matchRegex otherRegex s of
                   Just [a, b] -> return $ InModule a b
                   Nothing -> parseFail

parseType :: String -> TypeInferenceMonad UnionType
parseType s = case reads s of
                  [(t, "")] -> return t
                  _         -> err $ "cannot parse type: " ++ s

err :: String -> TypeInferenceMonad a
err msg = throwError $ UserSuppliedTypesError msg

dropWhitespace :: String -> String
dropWhitespace = let drop = dropWhile (`elem` " \t")
                 in drop . reverse . drop . reverse


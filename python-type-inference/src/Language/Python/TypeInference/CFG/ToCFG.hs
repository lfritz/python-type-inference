-- | Conversion from abstract syntax tree to control flow graph.
module Language.Python.TypeInference.CFG.ToCFG (
    createCFG
) where

import Data.List (delete)
import Data.Set (Set)
import Language.Python.TypeInference.CFG.CFG
import Language.Python.TypeInference.CFG.Fragment
import Language.Python.TypeInference.CFG.ToFragment
import Language.Python.TypeInference.Common
import Language.Python.TypeInference.Error
import Language.Python.TypeInference.UserSuppliedTypes
import qualified Data.Map as Map
import qualified Data.Set as Set
import qualified Language.Python.Common.AST as AST

-- | Construct control flow graphs given a list of (module name, module AST)
-- pairs.
createCFG :: [(String, AST.ModuleSpan)] -> UserSuppliedTypes
          -> TypeInferenceMonad CFG
createCFG modules userSuppliedTypes =
    do fragments <- modulesToFragment modules userSuppliedTypes
       let nonEmpty = filter (\(_,f,_) -> not (nullF f)) fragments
           (_, fs, identifierSets) = unzip3 nonEmpty
           withNames = [(n,f) | (n,f,_) <- nonEmpty]
           identifiers = Set.unions identifierSets
           f = foldr combine EmptyFragment fs
           f' = f { frEdges = frEdges f `Set.union` importEdges withNames }
       fragmentToCfg f' identifiers

-- | Create a fragment for a list of modules.
modulesToFragment :: [(String, AST.ModuleSpan)] -> UserSuppliedTypes
                  -> TypeInferenceMonad [(String, Fragment, Set Identifier)]
modulesToFragment modules (_, userSpecifiedModules, nextClassId) =
    let moduleNames = Set.fromList $ map fst modules
        externalModules = userSpecifiedModules Set.\\ moduleNames
        h (moduleName, moduleSpan) =
            do (f, ids) <- convertModule moduleName moduleSpan
               return (moduleName, f, ids)
    in runConversion externalModules nextClassId $ mapM h modules

-- | Create edges for import statements.
importEdges :: [(String, Fragment)] -> Set Edge
importEdges pairs =
    let moduleMap = Map.fromList pairs
        fragments = map snd pairs
        i f = Set.unions [ oneEntry f lc lr m
                         | (lc, (lr, m)) <- Map.toList (frImports f)]
        oneEntry f lc lr m =
            case Map.lookup m moduleMap of
                Nothing -> Set.empty
                Just f  ->
                    Set.fromList [(lc, i) | i <- Set.toList (getInitial f)]
                    `Set.union`
                    Set.map (\final -> (final, lr)) (frFinal f)
    in Set.unions $ map i fragments


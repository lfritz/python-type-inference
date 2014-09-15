-- | Type inference for Python 3. It serves as the entry point for users of the
-- library.
module Language.Python.TypeInference.TypeInference (
    parseModules,
    toCFG,
    inferTypes,
    parseUserSuppliedTypes
) where

import Data.Map (Map)
import Data.Set (Set)
import Language.Python.Common.AST
import Language.Python.TypeInference.Analysis.Analysis
import Language.Python.TypeInference.Analysis.TypeLattice
import Language.Python.TypeInference.CFG.CFG
import Language.Python.TypeInference.CFG.ToCFG
import Language.Python.TypeInference.Common
import Language.Python.TypeInference.Configuration
import Language.Python.TypeInference.Error
import Language.Python.TypeInference.Parse
import Language.Python.TypeInference.UserSuppliedTypes

-- | Parse modules.
parseModules :: [(SourceCode, Filename)]
             -> TypeInferenceMonad [(String, ModuleSpan)]
parseModules = mapM (uncurry parse)

-- | Create control flow graph.
toCFG :: [(String, ModuleSpan)] -> UserSuppliedTypes -> TypeInferenceMonad CFG
toCFG = createCFG

-- | Run type inference analysis.
inferTypes :: Configuration -> CFG -> Map Identifier UnionType
           -> TypeInferenceMonad (TypeInferenceResult, Set Edge', Int)
inferTypes = analyze

-- | Parse the contents of a file with user-supplied types.
parseUserSuppliedTypes :: String -> TypeInferenceMonad UserSuppliedTypes
parseUserSuppliedTypes = parseFile


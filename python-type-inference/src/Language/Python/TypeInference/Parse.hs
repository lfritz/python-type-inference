-- | Parsing Python code.
module Language.Python.TypeInference.Parse (
    parse
) where

import Language.Python.Common.AST
import Language.Python.Common.SrcLocation
import Language.Python.TypeInference.Common
import Language.Python.TypeInference.Error
import Language.Python.Version3.Parser

-- | Parse the source code of a Python module.
parse :: SourceCode -> Filename -> TypeInferenceMonad (String, ModuleSpan)
parse code filename = do name <- moduleName filename
                         case parseModule code filename of
                             Left err     -> throwError (ParseError (show err))
                             Right (m, _) -> return (name, m)

-- | Infer Python module name from filename.
moduleName :: String -> TypeInferenceMonad String
moduleName filename =
    case reverse filename of
        'y':'p':'.':cs -> return $ reverse $ takeWhile (`notElem` "/\\") cs
        _              -> throwError $ ParseError ("bad filename: " ++ filename)


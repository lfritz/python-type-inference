-- | Error handling for Python type inference.
module Language.Python.TypeInference.Error (
    throwError,
    TypeInferenceError (..),
    TypeInferenceMonad,
    run
) where

import Control.Monad.Error

-- | An error that occured during type inference.
data TypeInferenceError
    = ParseError String    -- ^ Python code could not be parsed.
    | CFGError String      -- ^ Error trying to construct control flow graph.
    | AnalysisError String -- ^ Error trying to set up the analysis.
    | UserSuppliedTypesError String -- ^ Error with user-supplied types.
    | OtherError String    -- ^ Other error.

instance Error TypeInferenceError where
    noMsg  = OtherError "type inference error"
    strMsg = OtherError

instance Show TypeInferenceError where
    show (ParseError s)    = "Parse error: " ++ s
    show (CFGError s)      = "Error constructing control flow graph: " ++ s
    show (AnalysisError s) = "Error setting up the analysis: " ++ s
    show (UserSuppliedTypesError s) = "Error loading user-supplied types: " ++ s
    show (OtherError s)    = "Error: " ++ s

-- | Monad for error handling.
type TypeInferenceMonad = Either TypeInferenceError

-- | Run computation and call the function if there is an error.
run :: TypeInferenceMonad a -> (TypeInferenceError -> a) -> a
run v f = case v of
              Left e  -> f e
              Right x -> x


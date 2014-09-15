-- | Configuration parameter for type inference.
module Language.Python.TypeInference.Configuration (
    Configuration (..),
    showConfiguration
) where

import Control.DeepSeq
import Data.Set (Set)
import Language.Python.TypeInference.Common
import Text.Printf
import qualified Data.Set as Set

-- | Parameters for type inference.
data Configuration =
    Configuration {
        -- | Parameters n, m, o for widening operator (see 'nabla').
        cfgWideningParameters :: (Int, Int, Int),
        -- | Use parameterized data types such as list of int.
        cfgParameterizedDatatypes :: Bool,
        -- | Length of callstrings for context-sensitive analysis. 0 means
        -- context-insensitive analysis.
        cfgContext :: Int,
        -- | Use flow-insensitive analysis for module-scope identifiers.
        cfgFiModuleScope :: Bool,
        -- | Use flow-insensitive analysis for class types.
        cfgFiClasses :: Bool,
        -- | Use flow-insensitive analysis for instance types.
        cfgFiInstances :: Bool,
        -- | External modules, that is, modules that are are used in, but not
        -- part of, the code under analysis.
        cfgExternalModules :: Set String
    }

instance NFData Configuration where
    rnf (Configuration w pd k fim fic fii externalModules) =
        rnf (w, pd, k, fim, fic, fii, Set.toList externalModules)

-- | Show configuration in multi-line format.
showConfiguration :: Configuration -> String
showConfiguration (Configuration (n, m, o) pd k
                   fiModuleScope fiClasses fiInstances externalModules) =
    unlines
    [ printf "Parameters for widening: (n, m, o) = (%d, %d, %d)" n m o
    , "Use parameterized data types: " ++ yes pd
    , "Context-sensitive analysis: "
      ++ (if k == 0 then "no" else "with callstrings of length " ++ show k)
    , "Use flow-insensitive analysis for module-scope identifiers: "
      ++ yes fiModuleScope
    , "Use flow-insensitive analysis for class types: "
      ++ yes fiClasses
    , "Use flow-insensitive analysis for instance types: "
      ++ yes fiInstances
    , "External modules: "
      ++ commas (Set.toAscList externalModules)
    ]
    where yes True  = "yes"
          yes False = "no"



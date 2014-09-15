-- | Lattice for type inference.
module Language.Python.TypeInference.Analysis.MapLattice (
    L,
    showL
) where

import Data.List (intercalate)
import Data.Map (Map)
import Language.Analysis.DFA.Lattice
import Language.Python.TypeInference.Analysis.TypeLattice
import Language.Python.TypeInference.CFG.CFG
import Language.Python.TypeInference.Common
import qualified Data.Map as Map

-- | The value computed for each program point during type inference: a map
-- containing the type of each identifier in scope.
type L = Map Identifier UnionType

-- | Show in concise, human-readable format.
showL :: L -> String
showL m = intercalate ", " [ show i ++ rightArrow ++ show t
                           | (i, t) <- Map.toAscList m ]

instance (Eq a, Ord a, Eq b, Lattice b) => Lattice (Map a b) where
    bot        = Map.empty
    a `join` b = Map.unionWith join a b


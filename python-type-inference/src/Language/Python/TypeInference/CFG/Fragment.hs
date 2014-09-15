-- | Defines a type for fragments of Python code and functions operting on it.
module Language.Python.TypeInference.CFG.Fragment (
    Fragment (..),
    getNodes, getEdges, getInitial, getFinal, getBreak, getContinue, getReturn,
    getImports, getFunctionTable,
    fragmentToCfg,
    fragment,
    singletonFragment,
    mappend,
    mconcat,
    combine,
    (-->),
    nullF
) where

import Control.Monad (unless)
import Data.List (intercalate)
import Data.Map (Map)
import Data.Monoid
import Data.Set (Set)
import Language.Python.TypeInference.CFG.CFG
import Language.Python.TypeInference.Common
import Language.Python.TypeInference.Error
import qualified Data.Map as Map
import qualified Data.Set as Set

-- | A fragment of Python code: represents the control flow graph for a subtree
-- of the abstract syntax tree.
data Fragment
    = EmptyFragment
    | Fragment {
          frNodes         :: Map Label (ProgramPoint, Position),
          frEdges         :: Set Edge,
          frInitial       :: Set Label,
          frFinal         :: Set Label,
          frBreak         :: Set Label,
          frContinue      :: Set Label,
          frReturn        :: Set Label,
          frImports       :: Map Label (Label, String),
          frFunctionTable :: Map Label (Label, Label)
      }

-- | Get the nodes in the fragment (or an empty map for an empty fragment).
getNodes :: Fragment -> Map Label (ProgramPoint, Position)
getNodes EmptyFragment = Map.empty
getNodes f             = frNodes f

-- | Get the edges in the fragment (or an empty set for an empty fragment).
getEdges :: Fragment -> Set Edge
getEdges EmptyFragment = Set.empty
getEdges f             = frEdges f

-- | Get the initial nodes (or an empty set for an empty fragment).
getInitial :: Fragment -> Set Label
getInitial EmptyFragment = Set.empty
getInitial f             = frInitial f

-- | Get the final nodes (or an empty set for an empty fragment).
getFinal :: Fragment -> Set Label
getFinal EmptyFragment = Set.empty
getFinal f             = frFinal f

-- | Get the nodes corresponding to @break@ statements (or an empty set for an
-- empty fragment).
getBreak :: Fragment -> Set Label
getBreak EmptyFragment = Set.empty
getBreak f             = frBreak f

-- | Get the nodes corresponding to @continue@ statements (or an empty set for
-- an empty fragment).
getContinue :: Fragment -> Set Label
getContinue EmptyFragment = Set.empty
getContinue f             = frContinue f

-- | Get the nodes corresponding to @return@ statements (or an empty set for an
-- empty fragment).
getReturn :: Fragment -> Set Label
getReturn EmptyFragment = Set.empty
getReturn f             = frReturn f

-- | Get the import statements (or an empty map for an empty fragment).
getImports :: Fragment -> Map Label (Label, String)
getImports EmptyFragment = Map.empty
getImports f             = frImports f

-- | Get the function table for the fragment (or an empty set for an empty
-- fragment).
getFunctionTable :: Fragment -> Map Label (Label, Label)
getFunctionTable EmptyFragment = Map.empty
getFunctionTable f             = frFunctionTable f

instance Eq Fragment where
    EmptyFragment == EmptyFragment = True
    EmptyFragment == _             = False
    _             == EmptyFragment = False
    (Fragment n e i f b c r is ft) == (Fragment n' e' i' f' b' c' r' is' ft') =
        Map.map fst n == Map.map fst n'
        && e == e' && i == i' && f == f' && b == b' && c == c' && r == r'
        && ft == ft'

-- | Convert a fragment corresponding to one or more modules to a control flow
-- graph.
fragmentToCfg :: Fragment -> Set Identifier -> TypeInferenceMonad CFG
fragmentToCfg f identifiers =
    do checkNoBreak f
       checkNoContinue f
       checkNoReturn f
       return $ CFG (frNodes f)
                    (frEdges f)
                    (frInitial f)
                    (frFinal f)
                    (frFunctionTable f)
                    identifiers

checkNull f s msg = unless (Set.null $ s f)
                           (throwError $ CFGError msg)
checkNoBreak f = checkNull f getBreak "break statement outside of loop"
checkNoContinue f = checkNull f getContinue "continue statement outside of loop"
checkNoReturn f = checkNull f getReturn "return statement outside of function"

-- | Create a fragment given program points, edges, initial label and final
-- labels.
fragment :: Map Label (ProgramPoint, Position)
         -> Set Edge -> Set Label -> Set Label
         -> Fragment
fragment nodes edges initial final =
    Fragment nodes edges initial final
             Set.empty Set.empty Set.empty Map.empty Map.empty

-- | Create a fragment for a single program point.
singletonFragment :: Label -> ProgramPoint -> Position -> Fragment
singletonFragment l pp pos = fragment (Map.singleton l (pp, pos))
                                      Set.empty
                                      (Set.singleton l)
                                      (Set.singleton l)

instance Monoid Fragment where
    mempty  = EmptyFragment
    mappend = compose

compose :: Fragment -> Fragment -> Fragment
EmptyFragment `compose` a             = a
a             `compose` EmptyFragment = a
a `compose` b =
    let nodes    = frNodes a `Map.union` frNodes b
        edges    = frEdges a `Set.union` frEdges b `Set.union` (a --> b)
        initial  = frInitial a
        final    = frFinal b
        break    = frBreak a `Set.union` frBreak b
        continue = frContinue a `Set.union` frContinue b
        return   = frReturn a `Set.union` frReturn b
        imports  = frImports a `Map.union` frImports b
        ft       = frFunctionTable a `Map.union` frFunctionTable b
    in Fragment nodes edges initial final break continue return imports ft

combine :: Fragment -> Fragment -> Fragment
EmptyFragment `combine` a             = a
a             `combine` EmptyFragment = a
a `combine` b =
    let nodes    = frNodes a `Map.union` frNodes b
        edges    = frEdges a `Set.union` frEdges b
        initial  = frInitial a `Set.union` frInitial b
        final    = frFinal a `Set.union` frFinal b
        break    = frBreak a `Set.union` frBreak b
        continue = frContinue a `Set.union` frContinue b
        return   = frReturn a `Set.union` frReturn b
        imports  = frImports a `Map.union` frImports b
        ft       = frFunctionTable a `Map.union` frFunctionTable b
    in Fragment nodes edges initial final break continue return imports ft

-- | Create edges connecting one fragment to the next.
(-->) :: Fragment -> Fragment -> Set Edge
EmptyFragment --> _             = Set.empty
_             --> EmptyFragment = Set.empty
a             --> b             =
    Set.fromList [(f, i) | f <- Set.toList (frFinal a),
                           i <- Set.toList (frInitial b)]

instance Show Fragment where
    show EmptyFragment = "EmptyFragment"
    show (Fragment nodes edges initial final break continue ret imports ft) =
        unlines
            [ "Nodes:"
            , intercalate "\n" [ show l ++ ": " ++ show pp
                               | (l, (pp, _)) <- Map.toAscList nodes ]
            , "Edges: " ++ unwords [ show a ++ rightArrow ++ show b
                                   | (a, b) <- Set.toAscList edges ]
            , "Initial node: " ++ show initial
            , "Final nodes: " ++ show final
            , "Break stmts: " ++ show break
            , "Continue stmts: " ++ show continue
            , "Return stmts: " ++ show ret
            , "Import stmts: " ++ show imports
            , "Function table: " ++ show ft
            ]

-- | Is the fragment empty? More precisely: does it contain zero program
-- points?
nullF :: Fragment -> Bool
nullF EmptyFragment = True
nullF f             = Map.null $ frNodes f


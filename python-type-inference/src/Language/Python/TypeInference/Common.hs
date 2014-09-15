-- | Some definitions shared by the various modules.
module Language.Python.TypeInference.Common where

import Control.DeepSeq
import Data.List (intercalate)
import Data.Map (Map)
import Text.Printf
import qualified Data.Map as Map

type Filename = String

type SourceCode = String

type LineNo = Int

type Label = Int

type FunctionId = Int

type ClassId = Int

-- | Position in the source code.
data Position = Position Filename LineNo
    deriving Eq

instance NFData Position where
    rnf (Position f l) = rnf (f, l)

instance Show Position where
    show (Position f l) = f ++ ":" ++ show l

alpha = "\x03b1"
beta = "\x03b2"
gamma = "\x03b3"
chi = "\x03c7"
iota = "\x03b9"
rho = "\x03c1"
sigma = "\x03C3"
dots = "\x2026"
rightArrow = "->"

-- | Show list with elements separated by commas.
commas :: Show a => [a] -> String
commas l = intercalate ", " (map show l)

-- | Show map in concise, human-readable format.
showMapping :: Show b => Map String b -> String
showMapping m =
    printf "{%s}" list
    where list = intercalate ", " [ a ++ rightArrow ++ show b
                                  | (a, b) <- Map.toAscList m ]

readMapping :: Read b => ReadS (Map String b)
readMapping r =
    case lex r of
     [("{", r1)] ->
         readRemaining r1
     _ -> []       
    where readRemaining r =
              case lex r of
               [("}", r1)] -> [(Map.empty, r1)]
               [(name, r1)] ->
                   case lex r1 of
                    [(arr, r2)] | arr == rightArrow ->
                        case reads r2 of
                         [(b, r3)] ->
                             case lex r3 of
                              [("}", r4)] -> [(Map.singleton name b, r4)]
                              [(",", r4)] ->
                                  case readRemaining r4 of
                                   [(mapping, r5)] ->
                                       [(Map.insert name b mapping, r5)]
                                   _ -> []
                              _ -> []
                         _ -> []
                    _ -> []

startsWith :: String -> String -> Bool
a `startsWith` b = take (length b) a == b

-- | Like 'mapM', but for maps.
mapMapM :: (Monad m, Ord k) => (a -> m b) -> Map k a -> m (Map k b)
mapMapM f mp = let f' (key, val) = do val' <- f val
                                      return (key, val')
               in do list <- mapM f' (Map.toList mp)
                     return (Map.fromList list)


-- | Parse Python code and infer types.

import Control.DeepSeq
import Control.Monad (when, unless)
import Data.List (intercalate, partition)
import Data.Map (Map)
import Data.Maybe (catMaybes)
import Data.Ratio
import Language.Python.Common.AST
import Language.Python.TypeInference.Analysis.Analysis
import Language.Python.TypeInference.Analysis.TypeLattice
import Language.Python.TypeInference.CFG.CFG
import Language.Python.TypeInference.Common
import Language.Python.TypeInference.Configuration
import Language.Python.TypeInference.Error
import Language.Python.TypeInference.TypeInference
import Language.Python.TypeInference.UserSuppliedTypes
import System (getArgs, getProgName)
import System.CPUTime
import System.Console.GetOpt
import Text.Printf
import qualified Data.Map as Map
import qualified Data.Set as Set

main :: IO ()
main =
    do args <- getArgs
       case parseArgs args of
           Nothing -> usage
           Just (mode, c, filenames) ->
               do codeList <- mapM readFile filenames
                  userSuppliedTypes <-
                      case typeFile mode of
                          Nothing -> return noUserSuppliedTypes
                          Just f ->
                              do contents <- readFile f
                                 case parseUserSuppliedTypes contents of
                                     Left e -> do putStrLn $ "Error: " ++ show e
                                                  return noUserSuppliedTypes
                                     Right ts -> return ts
                  let loc = sum $ map (length . lines) codeList
                      s = initialStatistics { stNModules = length codeList,
                                              stLinesOfCode = loc }
                  step1 filenames codeList mode c userSuppliedTypes s

-- | Step 1: parsing
step1 :: [String] -> [String] -> Mode -> Configuration -> UserSuppliedTypes
      -> Statistics -> IO ()
step1 filenames codeList mode c userSuppliedTypes s =
    case parseModules (zip codeList filenames) of
        Left e -> putStrLn $ "Error: " ++ show e
        Right asts ->
            do when (printAST mode)
                    (putStrLn $ printList (zip filenames (map snd asts)))
               when (doCFG mode)
                    (step2 filenames asts mode c userSuppliedTypes s)

-- | Step 2: constructing control-flow graph
step2 :: [String] -> [(String, ModuleSpan)] -> Mode -> Configuration
      -> UserSuppliedTypes -> Statistics -> IO ()
step2 filenames asts mode c userSuppliedTypes@(_, userSpecifiedModules, _) s =
    do let moduleNames = Set.fromList $ map fst asts
           externalModules = userSpecifiedModules Set.\\ moduleNames
           c' = c { cfgExternalModules = externalModules }
       unless (printRaw mode)
           $ putStr (showConfiguration c')
       case toCFG asts userSuppliedTypes of
           Left e -> putStrLn $ "Error: " ++ show e
           Right cfg ->
               do let s' = s { stNCFGNodes = Map.size (cfgNodes cfg),
                               stNCFGEdges = Set.size (cfgEdges cfg) }
                  when (printCFG mode)
                       (print cfg)
                  when (doTypeInference mode)
                       (step3 filenames cfg mode c' userSuppliedTypes s')

-- | Step 3: type inference
step3 :: [String] -> CFG -> Mode -> Configuration -> UserSuppliedTypes
      -> Statistics -> IO ()
step3 filenames cfg mode c (userSuppliedTypes, _, _) s =
    do start <- (c, cfg, Map.toList userSuppliedTypes) `deepseq` startTime
       let r = inferTypes c cfg userSuppliedTypes
       case r of
           Left e -> putStrLn $ "Error: " ++ show e
           Right (result, addedEdges, count) ->
               do time <- result `deepseq` endTime start
                  unless (printRaw mode)
                      $ putStrLn ("Time: " ++ showTime time)
                  when (printCFG mode) $ do putStrLn "Added edges:"
                                            putStrLn $ showEdges addedEdges
                  when (printTypes mode)
                       $ putStrLn $ if showContext mode
                                    then showResultWithContext result
                                    else showResult result
                  let s' = s { stWaIterations = count
                             , stTypeSize =
                                   typeSizeDistribution
                                       cfg (tirCtx result) (tirGlobal result)
                             }
                  when (printStatistics mode)
                       (print s')
                  when (printRaw mode)
                      $ putStrLn (showRawResults s' time)

-- Statistics collected during analysis.
data Statistics = Statistics {
                      stNModules     :: Int,
                      stLinesOfCode  :: Int,
                      stWaIterations :: Int,
                      stNCFGNodes    :: Int,
                      stNCFGEdges    :: Int,
                      stTypeSize     :: Map TypeSize Int
                  }

initialStatistics :: Statistics
initialStatistics = Statistics 0 0 0 0 0 Map.empty

ratioUsefulToTotal :: Map TypeSize Int -> Double
ratioUsefulToTotal m =
    let list = Map.toAscList m
        total = sum $ map snd list
        usefulTypeSize (TypeSize 0) = False
        usefulTypeSize TypeSizeTop  = False
        usefulTypeSize _            = True
        good = sum [count | (sz, count) <- list, usefulTypeSize sz]
    in fromRational $ toRational $ good % total

printTypeSizeMap :: Map TypeSize Int -> String
printTypeSizeMap m | Map.null m = "  - none -"
                   | otherwise =
    let list = Map.toAscList m
        total = sum $ map snd list
        onePercent = fromIntegral total / 100.0
        withPercent :: [(TypeSize, Int, Float)]
        withPercent = [ (size, count, fromIntegral count / onePercent)
                      | (size, count) <- list ]
    in intercalate "\n"
           $ [ printf "%3s: %6d %8.2f %%" (show s) c p
             | (s, c, p) <- withPercent ]
             ++
             [ printf "Ratio useful to total: %.5f" (ratioUsefulToTotal m) ]

instance Show Statistics where
    show (Statistics modules loc waIterations nodes edges typeSize) =
        unlines [ "Modules:       " ++ printf "%8d" modules
                , "Lines of code: " ++ printf "%8d" loc
                , "Iterations:    " ++ printf "%8d" waIterations
                , "Nodes in CFG:  " ++ printf "%8d" nodes
                , "Edges in CFG:  " ++ printf "%8d" edges
                , "Size of inferred types:"
                , printTypeSizeMap typeSize
                ]

showRawResults :: Statistics -> Time -> String
showRawResults s t =
    printf "%12d%12.5f" (timeToUs t) (ratioUsefulToTotal (stTypeSize s))

-- | The size of a union type: the number of value types it contains (directly,
-- not nested), or top.
data TypeSize = TypeSize Int
              | TypeSizeTop
    deriving (Eq, Ord)

typeSize :: UnionType -> TypeSize
typeSize UTyTop  = TypeSizeTop
typeSize (UTy s) = TypeSize (Set.size s)

-- | Given the context and global values determined by type inference, calculate
-- the distribution of type sizes. In other words, determine how many types
-- have size 0, how many have size 1, etc.
typeSizeDistribution :: CFG
                     -> Map Label (Map Identifier UnionType)
                     -> Map Identifier UnionType
                     -> Map TypeSize Int
typeSizeDistribution cfg ctx global =
    let nodes = Map.toList $ Map.map fst $ cfgNodes cfg
        getType :: Label -> Identifier -> Maybe UnionType
        getType l i = do m <- Map.lookup l ctx
                         case Map.lookup i m of
                             Just x  -> Just x
                             Nothing -> Map.lookup i global
        types = catMaybes [ getType l i
                          | (l, p) <- nodes
                          , i <- Set.toList (getIdentifiers p) ]
        insert :: Map TypeSize Int -> UnionType -> Map TypeSize Int
        insert m t = let size = typeSize t
                         count = Map.findWithDefault 0 size m
                     in Map.insert size (count + 1) m
    in foldl insert Map.empty types

instance Show TypeSize where
    show (TypeSize n)  = show n
    show (TypeSizeTop) = "\x22a4"

data Timestamp = Timestamp Integer
data Time = Time Integer

startTime :: IO Timestamp
startTime = do t <- getCPUTime
               return $ Timestamp t

endTime :: Timestamp -> IO Time
endTime (Timestamp s) = do t <- getCPUTime
                           return $ Time $ t - s

showTime :: Time -> String
showTime time = printf "%d us (cpu time)" (timeToUs time)

timeToUs :: Time -> Integer
timeToUs (Time t) = t `div` 1000000

-- | Mode selected by the user with flags.
data Mode = Mode {
                printAST        :: Bool,
                printCFG        :: Bool,
                printTypes      :: Bool,
                printStatistics :: Bool,
                showContext     :: Bool,
                typeFile        :: Maybe String,
                printRaw        :: Bool
            }


doCFG, doTypeInference :: Mode -> Bool
doCFG mode = printCFG mode || doTypeInference mode
doTypeInference mode = printTypes mode || printStatistics mode || printRaw mode

printList :: Show a => [(String, a)] -> String
printList list = unlines (map (uncurry printWithFilename) list)

printWithFilename :: Show a => String -> a -> String
printWithFilename filename a = filename ++ ":\n" ++ show a ++ "\n"

data Flag = PrintAST | PrintCFG | PrintTypes | PrintStatistics
          | N Int | M Int | O Int | PD | Context Int | ShowContext
          | FiModuleScope | FiClasses | FiInstances | TypeFile String
          | PrintRaw

setFlag :: (Mode, Configuration) -> Flag -> (Mode, Configuration)
setFlag (mode, c) PrintAST        = (mode {printAST        = True}, c)
setFlag (mode, c) PrintCFG        = (mode {printCFG        = True}, c)
setFlag (mode, c) PrintTypes      = (mode {printTypes      = True}, c)
setFlag (mode, c) PrintStatistics = (mode {printStatistics = True}, c)
setFlag (mode, c) (N n) = let (_,m,o) = cfgWideningParameters c
                          in (mode, c {cfgWideningParameters = (n,m,o)})
setFlag (mode, c) (M m) = let (n,_,o) = cfgWideningParameters c
                          in (mode, c {cfgWideningParameters = (n,m,o)})
setFlag (mode, c) (O o) = let (n,m,_) = cfgWideningParameters c
                          in (mode, c {cfgWideningParameters = (n,m,o)})
setFlag (mode, c) PD              = (mode, c {cfgParameterizedDatatypes = True})
setFlag (mode, c) (Context k)     = (mode, c {cfgContext = k})
setFlag (mode, c) ShowContext     = (mode {showContext = True}, c)
setFlag (mode, c) FiModuleScope   = (mode, c {cfgFiModuleScope = True})
setFlag (mode, c) FiClasses       = (mode, c {cfgFiClasses = True})
setFlag (mode, c) FiInstances     = (mode, c {cfgFiInstances = True})
setFlag (mode, c) (TypeFile f)    = (mode {typeFile = Just f}, c)
setFlag (mode, c) PrintRaw        = (mode {printRaw = True}, c)

options :: [OptDescr Flag]
options =
    [ Option "a" ["ast"]        (NoArg PrintAST) "print abstract syntax tree"
    , Option "c" ["cfg"]        (NoArg PrintCFG) "print control flow graph"
    , Option "t" ["types"]      (NoArg PrintTypes) "infer and print types"
    , Option "s" ["statistics"] (NoArg PrintStatistics)
             "print statistics for type inference"
    , Option "n" []             (ReqArg (N . read) "n")
          "parameter n for widening operator"
    , Option "m" []             (ReqArg (M . read) "m")
          "parameter m for widening operator"
    , Option "o" []             (ReqArg (O . read) "o")
          "parameter o for widening operator"
    , Option "p" ["pd"]         (NoArg PD)
           "use parameterized data types (eg, list<int>)"
    , Option "k" ["context"]    (ReqArg (Context . read) "k")
          "context-sensitive analysis w/callstrings of length k"
    , Option "q" ["show-context"] (NoArg ShowContext)
          "show context (callstrings) when printing types"
    , Option "f" ["fi-module-scope"] (NoArg FiModuleScope)
          "flow-insensitive analysis for module-scope variables"
    , Option "g" ["fi-classes"] (NoArg FiClasses)
          "flow-insensitive analysis for class types"
    , Option "h" ["fi-instances"] (NoArg FiInstances)
          "flow-insensitive analysis for instance types"
    , Option "u" ["type-file"]  (ReqArg TypeFile "f")
          "specify file with user-supplied types"
    , Option "r" ["raw"] (NoArg PrintRaw)
          "print precision and runtime numbers on their own"
    ]

-- | Parse command line arguments.
parseArgs :: [String] -> Maybe (Mode, Configuration, [String])
parseArgs argv =
    case getOpt Permute options argv of
        (o, fs, []) | length fs > 0 ->
            let defaultMode = Mode False False False False False Nothing False
                defaultConfiguration = Configuration (3, 3, 20) False 0
                                                     False False False Set.empty
                (mode, c) = foldl setFlag (defaultMode, defaultConfiguration) o
            in Just (mode, c, fs)
        (_, _,  es) -> Nothing

-- | Print usage message.
usage :: IO ()
usage = do name <- getProgName
           let header = printf "Usage: %s [OPTION...] files..." name
           putStrLn $ usageInfo header options


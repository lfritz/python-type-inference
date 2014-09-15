-- | Control flow graphs for Python source code.
module Language.Python.TypeInference.CFG.CFG (
    CFG (..),
    Edge,
    showEdge,
    FunctionTable,
    ProgramPoint (..),
    ImportedNames (..),
    Expression (..),
    Literal (..),
    Identifier (..),
    isName,
    isGenerated,
    isPositionalAI, isKeywordAI, isStarAI, isStarStarAI,
    isArgumentIdentifier,
    isReturnValue,
    Scope (..),
    UnaryOperator (..),
    BinaryOperator (..),
    isComparisonOperator,
    isBooleanOperator,
    AttributeRef (..),
    Subscription (..),
    Slicing (..),
    AssignmentOperator (..),
    Target (..),
    AugTarget (..),
    Argument (..),
    isPositionalArgument, isKeywordArgument, isStarArgument, isStarStarArgument,
    Parameter (..),
    getParamIdentifier,
    isRegularParameter, isStarParameter, isStarStarParameter,
    HasIdentifiers(..)
) where

import Control.DeepSeq
import Data.List (intercalate)
import Data.Map (Map)
import Data.Set (Set)
import Language.Python.TypeInference.Common
import Language.Python.TypeInference.Error
import qualified Data.Map as Map
import qualified Data.Set as Set

-- | Control flow graph for a Python modules.
data CFG = CFG {
               cfgNodes         :: Map Label (ProgramPoint, Position),
               cfgEdges         :: Set Edge,
               cfgInitial       :: Set Label,
               cfgFinal         :: Set Label,
               cfgFunctionTable :: FunctionTable,
               cfgBindings      :: Set Identifier
           }

instance NFData CFG where
    rnf (CFG n e i f ft b) =
        rnf (Map.toList n, Set.toList e, Set.toList i, Set.toList f
            , Map.toList ft, Set.toList b)

instance Eq CFG where
    CFG n e i f ft b == CFG n' e' i' f' ft' b' =
        Map.map fst n == Map.map fst n'
        && e == e'
        && i == i'
        && f == f'
        && ft == ft'
        && b == b'

instance Show CFG where
    show (CFG m e initial final ft b) =
        let programPoints = intercalate "\n" [ show l ++ ": " ++ show pp
                                             | (l, (pp, _)) <- Map.toAscList m ]
            edges = unwords $ map showEdge (Set.toAscList e)
            functionTable =
                if Map.null ft
                then "(empty)"
                else intercalate "\n" [ show l ++ ": " ++ show f
                                      | (l, f) <- Map.toAscList ft ]
        in unlines [ "Program points:"
                   , programPoints
                   , "Edges: " ++ edges
                   , "Initial labels: " ++ commas (Set.toAscList initial)
                   , "Final labels: " ++ commas (Set.toAscList final)
                   , "Module-level bindings: " ++ commas (Set.toAscList b)
                   , "Function table:"
                   ] ++
                   functionTable

-- | An edge between two program points representing potential flow of control.
type Edge = (Label, Label)

showEdge :: Edge -> String
showEdge (a, b) = show a ++ rightArrow ++ show b

-- | The function table contains, for each function, the entry and exit labels
-- (ln and lx).
type FunctionTable = Map FunctionId (Label, Label)

-- | A program point in the Python program, corresponding to a node in the
-- control flow graph. A program point often (but not always) corresponds to a
-- statement in the source code.
data ProgramPoint
      -- | Program point for a statement consisting only of an expression.
    = Expression Expression
      -- | Program point for an import statement.
    | ImportCall
      -- | Program point for an import statement.
    | ImportReturn ImportedNames
      -- | Program point for an assignment statement (assignment with @=@).
    | Assignment [Target] Expression
      -- | Program point for an augmented assignment statement (assignment with
      -- @+=@, @*=@ etc).
    | AugmentedAssignment AugTarget AssignmentOperator Expression
      -- | Program point for a @del@ statement.
    | Del [Target]
      -- | Program point for an @assert@ statement. The expression is dropped,
      -- for now.
    | Assert
      -- | Program point for a @pass@ statement.
    | Pass
      -- | Program point for a function call (/lc/), containing the callee, the
      -- list of arguments and the corresponding function return label.
    | FunctionCall Expression [Argument] Label
      -- | Program point for a function return (/lr/), containing the callee,
      -- an identifier that the returned value is assigned to and the
      -- corresponding function call label.
    | FunctionReturn Expression Identifier Label
      -- | Program point for function entry (/ln/).
    | FunctionEntry [Parameter]
      -- | Program point for function exit (/lx/).
    | FunctionExit [Parameter]
      -- | Program point for function definition (/ld/).
    | Def Identifier FunctionId
      -- | Program point for @return@ statement.
    | Return (Maybe Expression)
      -- | Program point for @break@ statement.
    | Break
      -- | Program point for @continue@ statement.
    | Continue
      -- | Program point for the condition of a @while@ loop.
    | LoopCondition Expression
      -- | Program point for the assignment of a @for@ loop. Contains the
      -- target(s) of the assignment and a (generated) identifier for the
      -- expression.
    | ForAssign Target Identifier
      -- | Program point for a condition in a conditional expression of
      -- @if@-@elif@-@else@ construct.
    | Condition Expression
      -- | Program point for a @with@ statement. The expression(s) yielding the
      -- context manager(s) are dropped, for now.
    | With [Target] -- ignore the expressions
      -- | Program point for the start of a class definition, with class name,
      -- class id and inheritance list.
    | ClassEntry Identifier ClassId [Argument]
      -- | Program point for the end of a class definition, with class name,
      -- class id and inheritance list.
    | ClassExit Identifier ClassId [Argument]
      -- | Program point for a list comprehension.
    | ListComprehension Identifier Expression
      -- | Program point for a set comprehension.
    | SetComprehension Identifier Expression
      -- | Program point for a dictionary comprehension.
    | DictComprehension Identifier (Expression, Expression)
      -- | Program point for the start of a scope, with a list of identifiers
      -- that come into scope at this point.
    | ScopeEntry [Identifier]
      -- | Program point for the end of a scope, with a list of identifiers
      -- that fall out of scope at this point.
    | ScopeExit [Identifier]
    deriving (Eq, Show)

instance NFData ProgramPoint where
    rnf (Expression e)                    = rnf e
    rnf ImportCall                        = ()
    rnf (ImportReturn names)              = rnf names
    rnf (Assignment targets e)            = rnf (targets, e)
    rnf (AugmentedAssignment target op e) = rnf (target, op, e)
    rnf (Del targets)                     = rnf targets
    rnf Assert                            = ()
    rnf Pass                              = ()
    rnf (FunctionCall e args l)           = rnf (e, args, l)
    rnf (FunctionReturn e i l)            = rnf (e, i, l)
    rnf (FunctionEntry ps)                = rnf ps
    rnf (FunctionExit ps)                 = rnf ps
    rnf (Def i f)                         = rnf (i, f)
    rnf (Return me)                       = rnf me
    rnf Break                             = ()
    rnf Continue                          = ()
    rnf (LoopCondition e)                 = rnf e
    rnf (ForAssign t i)                   = rnf (t, i)
    rnf (Condition e)                     = rnf e
    rnf (With targets)                    = rnf targets
    rnf (ClassEntry i c args)             = rnf (i, c, args)
    rnf (ClassExit i c args)              = rnf (i, c, args)
    rnf (ListComprehension i e)           = rnf (i, e)
    rnf (SetComprehension i e)            = rnf (i, e)
    rnf (DictComprehension i kv)          = rnf (i, kv)
    rnf (ScopeEntry is)                   = rnf is
    rnf (ScopeExit is)                    = rnf is

-- | Name(s) imported by an import statement.
data ImportedNames
    -- | Module name imported by an @import ...@ statement. Contains the module
    -- imported from, the module imported to and an optional @as@ name.
    = ModuleImport String String (Maybe String)
    -- | Names imported by a @from ... import ...@ statement. Contains the
    -- module imported from, the module imported to and the names imported with
    -- optional @as@ names.
    | FromImport String String [(String, Maybe String)]
    deriving (Eq, Show)

instance NFData ImportedNames where
    rnf (ModuleImport f t l) = rnf (f, t, l)
    rnf (FromImport f t l)   = rnf (f, t, l)

-- | Expression in the source code.
data Expression
    = Identifier Identifier
    | Literal Literal
    | TupleExpression [Expression]
    | ListExpression [Expression]
    | SetExpression [Expression]
    | DictionaryExpression [(Expression, Expression)]
    | AttributeReference AttributeRef
    | SubscriptionExpression Subscription
    | SlicingExpression Slicing
    | UnaryOperation UnaryOperator Expression
    | BinaryOperation Expression BinaryOperator Expression
      -- to properly support the yield construct, we'd have to create a
      -- separate program point
    | Yield (Maybe Expression)
    | Generator
    deriving Eq

instance NFData Expression where
    rnf (Identifier i)             = rnf i
    rnf (Literal l)                = rnf l
    rnf (TupleExpression es)       = rnf es
    rnf (ListExpression es)        = rnf es
    rnf (SetExpression es)         = rnf es
    rnf (DictionaryExpression es)  = rnf es
    rnf (AttributeReference a)     = rnf a
    rnf (SubscriptionExpression s) = rnf s
    rnf (SlicingExpression s)      = rnf s
    rnf (UnaryOperation op e)      = rnf (op, e)
    rnf (BinaryOperation a op b)   = rnf (a, op, b)
    rnf (Yield me)                 = rnf me
    rnf Generator                  = ()

instance Show Expression where
    show (Identifier i)             = show i
    show (Literal l)                = show l
    show (TupleExpression l)        = "(" ++ commas l ++ ")"
    show (ListExpression l)         = "[" ++ commas l ++ "]"
    show (SetExpression l)          = "{" ++ commas l ++ "}"
    show (DictionaryExpression l)   = "{"
                                    ++ intercalate ", "
                                                   [show a ++ ": " ++ show b
                                                   | (a, b) <- l]
                                    ++ "}"
    show (AttributeReference r)     = show r
    show (SubscriptionExpression s) = show s
    show (SlicingExpression s)      = show s
    show (UnaryOperation op e)      = show op ++ " " ++ show e
    show (BinaryOperation a op b)   = show a ++ " " ++ show op ++ " " ++ show b
    show (Yield Nothing)            = "yield"
    show (Yield (Just e))           = "yield " ++ show e
    show Generator                  = dots ++ "generator" ++ dots

-- | Literal constant.
data Literal = BoolLiteral Bool
             | StringLiteral String
             | ByteStringLiteral String
             | IntegerLiteral Integer
             | FloatLiteral Double
             | ImagLiteral Double
             | NoneLiteral
    deriving Eq

instance NFData Literal where
    rnf (BoolLiteral l)       = rnf l
    rnf (StringLiteral l)     = rnf l
    rnf (ByteStringLiteral l) = rnf l
    rnf (IntegerLiteral l)    = rnf l
    rnf (FloatLiteral l)      = rnf l
    rnf (ImagLiteral l)       = rnf l
    rnf NoneLiteral           = ()

instance Show Literal where
    show (BoolLiteral b)       = show b
    show (StringLiteral s)     = show s
    show (ByteStringLiteral s) = 'b' : show s
    show (IntegerLiteral i)    = show i
    show (FloatLiteral f)      = show f
    show (ImagLiteral i)       = show i ++ "j"
    show NoneLiteral           = "None"

-- | An identifier: either a name in the source code or an identifier generated
-- for the control flow graph.
data Identifier = Name Scope String
                | Generated Int
                | -- | AI for argument identifier.
                  PositionalAI Int
                | KeywordAI String
                | StarAI
                | StarStarAI
                | ReturnValue
                | Shadowed Identifier
                | ClassIdentifier ClassId
                | InstanceIdentifier ClassId
    deriving (Eq, Ord)

instance NFData Identifier where
    rnf (Name s n)             = rnf (s, n)
    rnf (Generated i)          = rnf i
    rnf (PositionalAI i)       = rnf i
    rnf (KeywordAI k)          = rnf k
    rnf StarAI                 = ()
    rnf StarStarAI             = ()
    rnf ReturnValue            = ()
    rnf (Shadowed i)           = rnf i
    rnf (ClassIdentifier c)    = rnf c
    rnf (InstanceIdentifier c) = rnf c

instance Show Identifier where
    show (Name Global s)            = s
    show (Name (ModuleScope m) s)   = m ++ "." ++ s
    show (Name (ExternalScope m) s) = chi ++ m ++ "." ++ s
    show (Name (FunctionScope f) s) = 'f' : show f ++ s
    show (Name (ForLoopScope l) s)  = 'l' : show l ++ s
    show (Name (WithScope l) s)     = 'w' : show l ++ s
    show (Name (ClassScope c) s)    = 'c' : show c ++ s
    show (Generated i)              = iota ++ show i
    show (PositionalAI i)           = alpha ++ show i
    show (KeywordAI s)              = alpha ++ s
    show StarAI                     = alpha ++ "*"
    show StarStarAI                 = alpha ++ "**"
    show ReturnValue                = rho
    show (Shadowed i)               = sigma ++ show i
    show (ClassIdentifier i)        = beta ++ show i
    show (InstanceIdentifier i)     = gamma ++ show i

isName (Name _ _) = True
isName _          = False
isGenerated (Generated _) = True
isGenerated _             = False
isPositionalAI (PositionalAI _) = True
isPositionalAI _                = False
isKeywordAI (KeywordAI _) = True
isKeywordAI _             = False
isStarAI StarAI = True
isStarAI _      = False
isStarStarAI StarStarAI = True
isStarStarAI _          = False
isArgumentIdentifier (PositionalAI _) = True
isArgumentIdentifier (KeywordAI _)    = True
isArgumentIdentifier StarAI           = True
isArgumentIdentifier StarStarAI       = True
isArgumentIdentifier _                = False
isReturnValue ReturnValue = True
isReturnValue _           = False

-- | A scope for name bindings. As Python uses lexical (static) scoping, we can
-- infer the scope for each variable from the source code.
data Scope = Global
             -- | Module scope. Identified by the module's name.
           | ModuleScope String
             -- | External identifier, that is, identifier in a module not
             -- under analysis. Identified by the module's name.
           | ExternalScope String
             -- | Function scope.
           | FunctionScope FunctionId
             -- | Scope for variables introduced as the targets of a @for@ loop
             -- or a comprehension.
           | ForLoopScope Label
             -- | Scope for variables introduced as the targets of a @with@
             -- statement.
           | WithScope Label
             -- | Scope for variables introduced in a class definition.
           | ClassScope ClassId
    deriving (Eq, Ord, Show)

instance NFData Scope where
    rnf Global            = ()
    rnf (ModuleScope s)   = rnf s
    rnf (ExternalScope s) = rnf s
    rnf (FunctionScope i) = rnf i
    rnf (ForLoopScope l)  = rnf l
    rnf (WithScope l)     = rnf l
    rnf (ClassScope i)    = rnf i

-- | Unary operators.
data UnaryOperator = UnaryMinus | UnaryPlus | Invert | BooleanNot
    deriving Eq

instance NFData UnaryOperator where

instance Show UnaryOperator where
    show UnaryMinus = "-"
    show UnaryPlus  = "+"
    show Invert     = "~"
    show BooleanNot = "not"

-- | Binary operators.
data BinaryOperator
    = Times | Div | DivDiv | Modulo | Minus | Plus | Exponent
    | RightShift | LeftShift
    | BitwiseAnd | BitwiseXor | BitwiseOr
    | Lt | Gt | Eq | LEq | GEq | NEq | Is | IsNot | In | NotIn
    | BooleanAnd | BooleanOr
    deriving Eq

instance NFData BinaryOperator

isComparisonOperator :: BinaryOperator -> Bool
isComparisonOperator =
    (`elem` [Lt, Gt, Eq, LEq, GEq, NEq, Is, IsNot, In, NotIn])

isBooleanOperator :: BinaryOperator -> Bool
isBooleanOperator = (`elem` [BooleanAnd, BooleanOr])

instance Show BinaryOperator where
    show Times       = "*"
    show Div         = "/"
    show DivDiv      = "/"
    show Modulo      = "%"
    show Minus       = "-"
    show Plus        = "+"
    show RightShift  = ">>"
    show LeftShift   = "<<"
    show BitwiseAnd  = "&"
    show BitwiseXor  = "^"
    show BitwiseOr   = "|"
    show Lt          = "<"
    show Gt          = ">"
    show Eq          = "="
    show LEq         = "<="
    show GEq         = ">="
    show NEq         = "!="
    show Is          = "is"
    show IsNot       = "is not"
    show In          = "in"
    show NotIn       = "not in"
    show BooleanAnd  = "and"
    show BooleanOr   = "or"

-- | Attribute reference, eg. @a.x@.
data AttributeRef = AttributeRef Expression String
    deriving Eq

instance NFData AttributeRef where
    rnf (AttributeRef e s) = rnf (e, s)

instance Show AttributeRef where
    show (AttributeRef e i) = show e ++ "." ++ i

-- | Subscription, eg. @a[0]@. The subscription expression is dropped, for now.
data Subscription = Subscription Expression
    deriving Eq

instance NFData Subscription where
    rnf (Subscription e) = rnf e

instance Show Subscription where
    show (Subscription e) = show e ++ "[" ++ dots ++ "]"

-- | Slicing, eg. @a[2,5]@. The slice expression is dropped, for now.
data Slicing = Slicing Expression
    deriving Eq

instance NFData Slicing where
    rnf (Slicing e) = rnf e

instance Show Slicing where
    show (Slicing e) = show e ++ "[" ++ dots ++ "]"

-- | Assignment operators: @= += -= *= /= //= %= **= >>= <<= &= ^=@ and @|=@.
-- The assignment operator is called /gets/ here to avoid confusion with the
-- equality and @is@ operators.
data AssignmentOperator
    = Gets | PlusGets | MinusGets | TimesGets | DivGets | DivDivGets | ModGets
    | ExpGets | RightShiftGets | LeftShiftGets | AndGets | XorGets | OrGets
    deriving Eq

instance NFData AssignmentOperator

instance Show AssignmentOperator where
    show Gets           = "="
    show PlusGets       = "+="
    show MinusGets      = "-="
    show TimesGets      = "*="
    show DivGets        = "/="
    show DivDivGets     = "//="
    show ModGets        = "%="
    show ExpGets        = "**="
    show RightShiftGets = ">>="
    show LeftShiftGets  = "<<="
    show AndGets        = "&="
    show XorGets        = "^="
    show OrGets         = "|="

-- | Target of an assignment statement.
data Target = TargetIdentifier Identifier
            | TargetList [Target]
            | TargetAttributeRef AttributeRef
            | TargetSubscription Subscription
            | TargetSlicing Slicing
            | StarTarget Target
    deriving Eq

instance NFData Target where
    rnf (TargetIdentifier i)   = rnf i
    rnf (TargetList ts)        = rnf ts
    rnf (TargetAttributeRef a) = rnf a
    rnf (TargetSubscription s) = rnf s
    rnf (TargetSlicing s)      = rnf s
    rnf (StarTarget t)         = rnf t

instance Show Target where
    show (TargetIdentifier i)   = show i
    show (TargetList l)         = "(" ++ commas l ++ ")"
    show (TargetAttributeRef a) = show a
    show (TargetSubscription s) = show s
    show (TargetSlicing s)      = show s
    show (StarTarget t)         = '*' : show t

-- | Target of an augmented assignment statement.
data AugTarget = AugTargetIdentifier Identifier
               | AugTargetAttributeRef AttributeRef
               | AugTargetSubscription Subscription
               | AugTargetSlicing Slicing
    deriving Eq

instance NFData AugTarget where
    rnf (AugTargetIdentifier i)   = rnf i
    rnf (AugTargetAttributeRef a) = rnf a
    rnf (AugTargetSubscription s) = rnf s
    rnf (AugTargetSlicing s)      = rnf s

instance Show AugTarget where
    show (AugTargetIdentifier i)   = show i
    show (AugTargetAttributeRef a) = show a
    show (AugTargetSubscription s) = show s
    show (AugTargetSlicing s)      = show s

-- | Function call argument.
data Argument = PositionalArgument Expression
              | KeywordArgument String Expression
              | StarArgument Expression
              | StarStarArgument Expression
    deriving Eq

instance NFData Argument where
    rnf (PositionalArgument e) = rnf e
    rnf (KeywordArgument s e)  = rnf (s, e)
    rnf (StarArgument e)       = rnf e
    rnf (StarStarArgument e)   = rnf e

instance Show Argument where
    show (PositionalArgument e) = show e
    show (KeywordArgument k e)  = k ++ "=" ++ show e
    show (StarArgument e)       = '*' : show e
    show (StarStarArgument e)   = "**" ++ show e

isPositionalArgument (PositionalArgument _) = True
isPositionalArgument _                      = False
isKeywordArgument    (KeywordArgument _ _)  = True
isKeywordArgument    _                      = False
isStarArgument       (StarArgument _)       = True
isStarArgument       _                      = False
isStarStarArgument   (StarStarArgument _)   = True
isStarStarArgument   _                      = False

-- | Formal parameter in function definition.
data Parameter = Parameter Identifier (Maybe Expression)
               | StarParameter Identifier
               | StarStarParameter Identifier
    deriving Eq

instance NFData Parameter where
    rnf (Parameter i me)      = rnf (i, me)
    rnf (StarParameter i)     = rnf i
    rnf (StarStarParameter i) = rnf i

instance Show Parameter where
    show (Parameter i Nothing)  = show i
    show (Parameter i (Just e)) = show i ++ "=" ++ show e
    show (StarParameter i)      = '*' : show i
    show (StarStarParameter i)  = "**" ++ show i

getParamIdentifier :: Parameter -> Identifier
getParamIdentifier (Parameter i _)       = i
getParamIdentifier (StarParameter i)     = i
getParamIdentifier (StarStarParameter i) = i

isRegularParameter (Parameter _ _) = True
isRegularParameter _               = False
isStarParameter (StarParameter _) = True
isStarParameter _                 = False
isStarStarParameter (StarStarParameter _) = True
isStarStarParameter _                     = False

class HasIdentifiers a where
    getIdentifiers :: a -> Set Identifier

getAllIdentifiers :: HasIdentifiers a => [a] -> Set Identifier
getAllIdentifiers list = Set.unions $ map getIdentifiers list

instance HasIdentifiers ProgramPoint where
    getIdentifiers (Expression e)              = getIdentifiers e
    getIdentifiers (Assignment _ e)            = getIdentifiers e
    getIdentifiers (AugmentedAssignment _ _ e) = getIdentifiers e
    getIdentifiers (FunctionCall e args _)     = getIdentifiers e `Set.union`
                                                 getAllIdentifiers args
    getIdentifiers (FunctionReturn e _ _)       = getIdentifiers e
    getIdentifiers (Return (Just e))            = getIdentifiers e
    getIdentifiers (LoopCondition e)            = getIdentifiers e
    getIdentifiers (ForAssign _ i)              = Set.singleton i
    getIdentifiers (Condition e)                = getIdentifiers e
    getIdentifiers (ListComprehension _ e)      = getIdentifiers e
    getIdentifiers (SetComprehension _ e)       = getIdentifiers e
    getIdentifiers (DictComprehension _ (k, v)) = getIdentifiers k `Set.union`
                                                  getIdentifiers v
    getIdentifiers _                            = Set.empty

instance HasIdentifiers Expression where
    getIdentifiers (Identifier i)               = Set.singleton i
    getIdentifiers (TupleExpression es)         = getAllIdentifiers es
    getIdentifiers (ListExpression es)          = getAllIdentifiers es
    getIdentifiers (SetExpression es)           = getAllIdentifiers es
    getIdentifiers (DictionaryExpression pairs) = let (ks, vs) = unzip pairs
                                                  in getAllIdentifiers ks
                                                     `Set.union`
                                                     getAllIdentifiers vs
    getIdentifiers (AttributeReference a)       = getIdentifiers a
    getIdentifiers (SubscriptionExpression s)   = getIdentifiers s
    getIdentifiers (SlicingExpression s)        = getIdentifiers s
    getIdentifiers (UnaryOperation _ e)         = getIdentifiers e
    getIdentifiers (BinaryOperation a _ b)      = getIdentifiers a
                                                  `Set.union`
                                                  getIdentifiers b
    getIdentifiers (Yield (Just e))             = getIdentifiers e
    getIdentifiers _                            = Set.empty

instance HasIdentifiers Argument where
    getIdentifiers (PositionalArgument e) = getIdentifiers e
    getIdentifiers (KeywordArgument _ e)  = getIdentifiers e
    getIdentifiers (StarArgument e)       = getIdentifiers e
    getIdentifiers (StarStarArgument e)   = getIdentifiers e

instance HasIdentifiers AttributeRef where
    getIdentifiers (AttributeRef e _) = getIdentifiers e

instance HasIdentifiers Subscription where
    getIdentifiers (Subscription e) = getIdentifiers e

instance HasIdentifiers Slicing where
    getIdentifiers (Slicing e) = getIdentifiers e


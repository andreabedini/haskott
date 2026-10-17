-- | The checked specification: Ott's @syntaxdefn@.
--
-- "Haskott.Spec.Check" builds it from the raw specification, resolving
-- roots and synonyms, classifying the elements of productions, merging dot
-- forms, resolving hom references to element positions, and performing the
-- checks of Ott's @grammar_typecheck.ml@ that concern the grammar itself.
-- Rule bodies stay as lines of text until the grammar-derived term parser
-- of stage two exists.
module Haskott.Spec
  ( Spec (..)
  , MetavarDefn (..)
  , Rule (..)
  , Prod (..)
  , Element (..)
  , ListBody (..)
  , Hom
  , HomEl (..)
  , Bindspec (..)
  , Mse (..)
  , Subrule (..)
  , SubruleData (..)
  , Contextrule (..)
  , Substitution (..)
  , Freevar (..)
  , RootRef (..)
  , Embed (..)
  , ParsingAnnotation (..)
  , DefnClass (..)
  , Defn (..)
  , FunClass (..)
  , FunDefn (..)
  , SemirawRule (..)
  , EmbedEl (..)
  , Diagnostic (..)
  , module Haskott.Spec.Suffix
  ) where

import Data.Set (Set)
import Data.Text (Text)
import Graft.Range (TextRange)
import Haskott.Raw (EmbedEl (..), SemirawRule (..))
import Haskott.Spec.Suffix

data Spec = Spec
  { specMetavars :: [MetavarDefn]
  , specRules :: [Rule]
  -- ^ the user's rules, then the synthesised @formula@ (unless the user
  -- defined one), the rules of the definition classes, @judgement@ and
  -- @user_syntax@, in Ott's order
  , specSubrules :: [Subrule]
  , specSubruleData :: SubruleData
  , specContextrules :: [Contextrule]
  , specSubstitutions :: [Substitution]
  , specFreevars :: [Freevar]
  , specEmbeds :: [Embed]
  , specParsing :: [ParsingAnnotation]
  , specIndexvars :: [Text]
  -- ^ every index variable root and synonym
  , specDefnClasses :: [DefnClass]
  , specFunClasses :: [FunClass]
  , specAuxfns :: [(Text, Text)]
  -- ^ auxiliary functions and the primary nonterminal root they are
  -- defined over
  }
  deriving (Eq, Show)

data MetavarDefn = MetavarDefn
  { mvdName :: Text
  , mvdNames :: [(Text, [Hom])]
  , mvdHoms :: [Hom]
  , mvdIndexvar :: Bool
  , mvdLocallyNameless :: Bool
  , mvdPhantom :: Bool
  , mvdRange :: TextRange
  }
  deriving (Eq, Show)

data Rule = Rule
  { ruleName :: Text
  , ruleNames :: [(Text, [Hom])]
  , rulePrefix :: Text
  , ruleProds :: [Prod]
  , ruleHoms :: [Hom]
  , ruleMeta :: Bool
  , ruleSemiMeta :: Bool
  , rulePhantom :: Bool
  , ruleJudgement :: Bool
  , ruleCategories :: [Text]
  , ruleRange :: TextRange
  }
  deriving (Eq, Show)

data Prod = Prod
  { prodName :: Text
  -- ^ with the rule's prefix
  , prodMeta :: Bool
  , prodSugar :: Bool
  , prodCategories :: Set Text
  , prodElements :: [Element]
  , prodHoms :: [Hom]
  , prodDisambiguate :: Maybe (Text, Text)
  , prodBindspecs :: [Bindspec]
  , prodRange :: TextRange
  }
  deriving (Eq, Show)

data Element
  = Nonterm Text Text Suffix
  -- ^ primary root, root as written, suffix
  | Metavar Text Text Suffix
  | Terminal Text
  | ListForm ListBody
  deriving (Eq, Ord, Show)

data ListBody = ListBody
  { lbBound :: Maybe Bound
  , lbSeparator :: Maybe Text
  , lbElements :: [Element]
  }
  deriving (Eq, Ord, Show)

type Hom = (Text, [HomEl])

data HomEl
  = HomString Text
  | HomIndex Int
  | HomTerminal Text
  | HomLnFreeIndex [Int] Int
  deriving (Eq, Show)

data Bindspec
  = Bind Mse (Text, Suffix) TextRange
  | AuxFnDef Text Mse TextRange
  | NamesEqual Mse Mse TextRange
  | NamesDistinct Mse Mse TextRange
  | AllNamesDistinct Mse TextRange
  deriving (Eq, Show)

data Mse
  = MetaVarExp (Text, Suffix)
  | NonTermExp (Text, Suffix)
  | MetaVarListExp (Text, Suffix) Bound
  | NonTermListExp (Text, Suffix) Bound
  | Aux Text (Text, Suffix)
  | AuxList Text (Text, Suffix) Bound
  | Union Mse Mse
  | Empty
  deriving (Eq, Show)

data Subrule = Subrule
  { srLower :: Text
  , srUpper :: Text
  , srTop :: Text
  , srHoms :: [Hom]
  , srRange :: TextRange
  }
  deriving (Eq, Show)

data SubruleData = SubruleData
  { srdProperSubntrs :: [(Text, [Text])]
  -- ^ each root in the order with the roots strictly below it
  , srdGraph :: [(Text, Text)]
  -- ^ the transitive closure of the declared pairs
  }
  deriving (Eq, Show)

data Contextrule = Contextrule
  { crNtr :: Text
  , crTarget :: Text
  , crHole :: Text
  , crRange :: TextRange
  }
  deriving (Eq, Show)

data RootRef = Mvr Text | Ntr Text
  deriving (Eq, Show)

data Substitution = Substitution
  { sbName :: Text
  , sbThis :: Text
  , sbThat :: RootRef
  , sbMultiple :: Bool
  , sbHoms :: [Hom]
  , sbRange :: TextRange
  }
  deriving (Eq, Show)

data Freevar = Freevar
  { fvName :: Text
  , fvThis :: Text
  , fvThat :: RootRef
  , fvHoms :: [Hom]
  , fvRange :: TextRange
  }
  deriving (Eq, Show)

data Embed = Embed
  { embedName :: Text
  , embedSpec :: [EmbedEl]
  , embedRange :: TextRange
  }
  deriving (Eq, Show)

data ParsingAnnotation = ParsingAnnotation
  { paLeft :: Text
  , paOperator :: Text
  , paRight :: Text
  , paRange :: TextRange
  }
  deriving (Eq, Show)

-- | A definition class with its homs from hom sections merged in. The
-- rules keep their raw form.
data DefnClass = DefnClass
  { dcName :: Text
  , dcWrapper :: Text
  , dcHoms :: [Hom]
  , dcDefns :: [Defn]
  , dcRange :: TextRange
  }
  deriving (Eq, Show)

data Defn = Defn
  { dName :: Text
  , dWrapper :: Text
  , dElements :: [Element]
  , dCategories :: [Text]
  , dHoms :: [Hom]
  , dBody :: [SemirawRule]
  , dRange :: TextRange
  }
  deriving (Eq, Show)

data FunClass = FunClass
  { fcName :: Text
  , fcHoms :: [Hom]
  , fcDefns :: [FunDefn]
  , fcRange :: TextRange
  }
  deriving (Eq, Show)

data FunDefn = FunDefn
  { fdName :: Text
  , fdElements :: [Element]
  , fdResult :: Text
  -- ^ the primary root of the result
  , fdResultPrefix :: Text
  -- ^ the production-name prefix of the result's rule
  , fdHoms :: [Hom]
  , fdClauses :: [Text]
  , fdRange :: TextRange
  }
  deriving (Eq, Show)

-- | A checking error, with the range of the construct it concerns.
data Diagnostic = Diagnostic
  { diagRange :: TextRange
  , diagMessage :: Text
  }
  deriving (Eq, Show)

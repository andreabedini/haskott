{-# LANGUAGE OverloadedStrings #-}

-- | What the prover back ends share: the target, Ott's options for it, the
-- state Ott keeps in mutable references while it prints, and the
-- specification indexed for printing.
--
-- Ott's printers are impure: a counter names the hypotheses Coq rules
-- need for projections from lists, the Coq printer accumulates those
-- hypotheses, library functions are added as they are first used, and
-- ocamlgraph's vertex counter, shared by every graph of the run, decides
-- the order of mutually recursive definitions. All of that is the state
-- 'PState' of the monad 'P', and the printers run their effects in the
-- order OCaml evaluates them.
module Haskott.Prover.Types
  ( Target (..)
  , targetName
  , ProverOptions (..)
  , defaultProverOptions
  , PState (..)
  , initialPState
  , P
  , runP
  , failP
  , Env (..)
  , makeEnv
  , NtMv
  , SubntrData
  , De1i (..)
  , De1
  , De2
  , De3
  , De
  , deEmpty
  , Deps (..)
    -- * Lookups
  , ruleOfNtr
  , ruleOfNtrNonprimary
  , mvdOfMvr
  , mvdOfMvrNonprimary
  , primaryNtrOfNtr
  , primaryMvrOfMvr
  , primaryNtmvr
  , prodOfProdname
  , promoteNtr
  , promoteNtr'
  , promoteNtmvr
  , homSpecForTarget
  , isCoq
  , isIsa
  , isHol
  , isLem
  , isCaml
  , freshC
  , addToLib
  ) where

import Control.Monad.Trans.Class (lift)
import Control.Monad.Trans.State.Strict (StateT, get, put, runStateT)
import Data.List (find)
import qualified Data.Map.Strict as M
import Data.Maybe (fromMaybe)
import Data.Text (Text)
import qualified Data.Text as T
import Haskott.Spec
import Haskott.Term.Symterm (Ste, Symterm)

data Target = Coq | Isa | Hol | Lem | Caml
  deriving (Eq, Ord, Show)

-- | Ott's @hom_name_for_pp_mode@.
targetName :: Target -> Text
targetName t = case t of
  Coq -> "coq"
  Isa -> "isa"
  Hol -> "hol"
  Lem -> "lem"
  Caml -> "ocaml"

data ProverOptions = ProverOptions
  { optCoqExpandLists :: Bool
  -- ^ @-coq_expand_list_types@
  , optCoqNamesInRules :: Bool
  , optCoqUseFilterFn :: Bool
  , optCoqLngen :: Bool
  , optCoqAvoid :: Int
  , optIsaPrimrec :: Bool
  , optIsaInductive :: Bool
  , optIsaSyntax :: Bool
  , optIsaGenerateLemmas :: Bool
  , optCamlIncludeTerminals :: Bool
  , optNoRbcatn :: Bool
  }

defaultProverOptions :: ProverOptions
defaultProverOptions =
  ProverOptions
    { optCoqExpandLists = False
    , optCoqNamesInRules = True
    , optCoqUseFilterFn = False
    , optCoqLngen = False
    , optCoqAvoid = 1
    , optIsaPrimrec = True
    , optIsaInductive = True
    , optIsaSyntax = False
    , optIsaGenerateLemmas = True
    , optCamlIncludeTerminals = False
    , optNoRbcatn = True
    }

-- | Ott's mutable state while printing.
data PState = PState
  { psVertex :: !Int
  -- ^ ocamlgraph's vertex counter
  , psC :: !Int
  -- ^ @Grammar_pp.c@, naming hypothesis variables
  , psCoqNonLocalHypDefn :: Text
  , psCoqNonLocalHypDefnVars :: [(Text, Maybe Text)]
  , psCoqQuantifiedVarsFromDe :: [Text]
  , psCoqListTypes :: [Text]
  , psCoqListAuxFuncs :: Text
  , psCoqListAuxNewlyDefined :: [Text]
  , psLibrary :: (Text, [Text])
  -- ^ the library functions to print next, and the names of every
  -- library function added
  , psCoqBuffer :: Text
  -- ^ @pp_internal_coq_buffer@: decidable equality lemmas of the rules
  -- printed so far
  , psCounters :: M.Map Text (M.Map Text Int)
  -- ^ the split counters of the printers of functions, by printer
  , psCoqLocallyNameless :: Bool
  -- ^ Ott's @coq_locally_nameless@: printing for the locally nameless
  -- back end
  , psOpeningVars :: [Ste]
  -- ^ @Ln_transform.opening_vars@: the variables a term is opened with
  }

initialPState :: Int -> PState
initialPState vertex =
  PState
    { psVertex = vertex
    , psC = 100
    , psCoqNonLocalHypDefn = ""
    , psCoqNonLocalHypDefnVars = []
    , psCoqQuantifiedVarsFromDe = []
    , psCoqListTypes = []
    , psCoqListAuxFuncs = ""
    , psCoqListAuxNewlyDefined = []
    , psLibrary = ("", [])
    , psCoqBuffer = ""
    , psCounters = M.empty
    , psCoqLocallyNameless = False
    , psOpeningVars = []
    }

-- | Printing, which fails as Ott does when it finds a problem only at
-- output time.
type P = StateT PState (Either Text)

runP :: PState -> P a -> Either Text (a, PState)
runP s m = runStateT m s

failP :: Text -> P a
failP = lift . Left

-- | The counter @c@, incremented.
freshC :: P Int
freshC = do
  s <- get
  let n = psC s + 1
  put s {psC = n}
  pure n

-- | Ott's @add_to_lib@.
addToLib :: Text -> Text -> P ()
addToLib nm def = do
  s <- get
  let (txt, names) = psLibrary s
  if nm `elem` names then pure () else put s {psLibrary = (txt <> def, nm : names)}

-- | The dependencies Ott computes for a target (@xd_dependencies@).
data Deps = Deps
  { depTs :: [[RootRef]]
  -- ^ the topological sort of the groups of mutually recursive rules and
  -- metavariables
  , depGraph :: [(RootRef, [RootRef])]
  , depGraphNontran :: [(RootRef, [RootRef])]
  }

-- | The specification indexed for printing, for one target.
data Env = Env
  { envTarget :: Target
  , envOpts :: ProverOptions
  , envSpec :: Spec
  , envDeps :: Deps
  , envRuleByNtr :: M.Map Text Rule
  -- ^ by primary root
  , envRuleByName :: M.Map Text Rule
  -- ^ by every root
  , envMvdByMvr :: M.Map Text MetavarDefn
  , envMvdByName :: M.Map Text MetavarDefn
  , envPrimaryNtr :: M.Map Text Text
  , envPrimaryMvr :: M.Map Text Text
  , envProdByName :: M.Map Text Prod
  , envPromotion :: M.Map Text (Text, M.Map Text Text)
  , envAuxfnTypes :: [(Text, ([Text], RootRef))]
  -- ^ Ott's @xd_axs@: each auxiliary function, the rules it is defined
  -- over and its result type
  , envQuotation :: Text -> Symterm
  -- ^ the parser of the @[[ ]]@ quotations of embeds
  , envParse :: Text -> Text -> [Symterm]
  -- ^ every parse of a text as a term of a root, in order (none unless
  -- set: the printers of context rules need it)
  , envLoc :: Maybe (Int, Int) -> Text
  -- ^ a range of the sources as Ott prints a location
  }

makeEnv :: Target -> ProverOptions -> Deps -> [(Text, ([Text], RootRef))] -> (Text -> Symterm) -> Spec -> Env
makeEnv t opts deps axs quotation spec =
  Env
    { envTarget = t
    , envOpts = opts
    , envSpec = spec
    , envDeps = deps
    , envRuleByNtr = M.fromList [(ruleName r, r) | r <- reverse (specRules spec)]
    , envRuleByName = M.fromList [(n, r) | r <- reverse (specRules spec), (n, _) <- ruleNames r]
    , envMvdByMvr = M.fromList [(mvdName md, md) | md <- reverse (specMetavars spec)]
    , envMvdByName = M.fromList [(n, md) | md <- reverse (specMetavars spec), (n, _) <- mvdNames md]
    , envPrimaryNtr = M.fromList [(n, ruleName r) | r <- reverse (specRules spec), (n, _) <- ruleNames r]
    , envPrimaryMvr = M.fromList [(n, mvdName md) | md <- reverse (specMetavars spec), (n, _) <- mvdNames md]
    , envProdByName = M.fromList [(prodName p, p) | r <- reverse (specRules spec), p <- reverse (ruleProds r)]
    , envPromotion = M.fromList [(lower, (top, M.fromList pps)) | (lower, (top, pps)) <- srdPromotion (specSubruleData spec)]
    , envAuxfnTypes = axs
    , envQuotation = quotation
    , envParse = \_ _ -> []
    , envLoc = const ""
    }

isCoq, isIsa, isHol, isLem, isCaml :: Env -> Bool
isCoq = (== Coq) . envTarget
isIsa = (== Isa) . envTarget
isHol = (== Hol) . envTarget
isLem = (== Lem) . envTarget
isCaml = (== Caml) . envTarget

-- | A nonterminal or metavariable with its suffix.
type NtMv = (RootRef, Suffix)

-- | For a nonterminal of a subrule, its lower and top roots.
type SubntrData = Maybe (Text, Text)

-- | Ott's @dotenv1@ item: the nonterminals and metavariables of a bound,
-- the compound list variable, the pattern deconstructing an element, and
-- the Coq and HOL types.
data De1i = De1i
  { de1Ntmvsns :: [(NtMv, SubntrData)]
  , de1CompoundId :: Text
  , de1Pattern :: Text
  , de1CoqTypeOfPattern :: Text
  , de1HolTypeOfCompoundId :: Text
  }
  deriving (Eq, Show)

type De1 = [(Bound, De1i)]

-- | The projections from list forms: @l'j@ of @l'1 .. l'n@.
type De2 = [(NtMv, (Suffix, SuffixItem, Bound))]

-- | The nonterminals and metavariables that are not projections.
type De3 = [(NtMv, SubntrData)]

type De = (De1, De2)

deEmpty :: De
deEmpty = ([], [])

------------------------------------------------------------------------
-- Lookups

oops :: String -> a
oops m = error ("Haskott.Prover: " ++ m)

ruleOfNtr :: Env -> Text -> Rule
ruleOfNtr env n = fromMaybe (oops ("no rule " ++ T.unpack n)) (M.lookup n (envRuleByNtr env))

ruleOfNtrNonprimary :: Env -> Text -> Rule
ruleOfNtrNonprimary env n = fromMaybe (oops ("no rule " ++ T.unpack n)) (M.lookup n (envRuleByName env))

mvdOfMvr :: Env -> Text -> MetavarDefn
mvdOfMvr env n = fromMaybe (oops ("no metavar " ++ T.unpack n)) (M.lookup n (envMvdByMvr env))

mvdOfMvrNonprimary :: Env -> Text -> MetavarDefn
mvdOfMvrNonprimary env n = fromMaybe (oops ("no metavar " ++ T.unpack n)) (M.lookup n (envMvdByName env))

primaryNtrOfNtr :: Env -> Text -> Text
primaryNtrOfNtr env n = fromMaybe (oops ("no root " ++ T.unpack n)) (M.lookup n (envPrimaryNtr env))

primaryMvrOfMvr :: Env -> Text -> Text
primaryMvrOfMvr env n = fromMaybe (oops ("no metavar root " ++ T.unpack n)) (M.lookup n (envPrimaryMvr env))

primaryNtmvr :: Env -> RootRef -> RootRef
primaryNtmvr env r = case r of
  Ntr n -> Ntr (primaryNtrOfNtr env n)
  Mvr n -> Mvr (primaryMvrOfMvr env n)

prodOfProdname :: Env -> Text -> Prod
prodOfProdname env pn = fromMaybe (oops ("no production " ++ T.unpack pn)) (M.lookup pn (envProdByName env))

-- | Ott's @promote_ntr@: a subrule's root to its top root.
promoteNtr :: Env -> Text -> Text
promoteNtr env n = maybe n srTop (find ((== n) . srLower) (specSubrules (envSpec env)))

-- | Ott's @promote_ntr'@: the upper and top roots, if a subrule's.
promoteNtr' :: Env -> Text -> Maybe (Text, Text)
promoteNtr' env n = (\s -> (srUpper s, srTop s)) <$> find ((== n) . srLower) (specSubrules (envSpec env))

promoteNtmvr :: Env -> RootRef -> RootRef
promoteNtmvr env r = case r of
  Ntr n -> Ntr (promoteNtr env n)
  Mvr _ -> r

homSpecForTarget :: Env -> [Hom] -> Maybe [HomEl]
homSpecForTarget env = lookup (targetName (envTarget env))

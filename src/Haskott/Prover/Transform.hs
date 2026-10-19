{-# LANGUAGE OverloadedStrings #-}

-- | The renamings Ott applies to a specification before printing it for
-- a prover (@auxl.ml@): for Coq, nonterminals and metavariables written
-- with a primary root and no suffix get a fresh suffix
-- (@avoid_primaries_systemdefn@), so that a variable does not take the
-- name of its type; for OCaml, production names are capitalised and
-- primary roots uncapitalised (@caml_rename@).
module Haskott.Prover.Transform
  ( avoidPrimaries
  , camlRename
  , freshSuffix
  , freshNt
  ) where

import Data.Char (toLower, toUpper)
import qualified Data.Map.Strict as M
import Data.Maybe (fromMaybe)
import Data.Text (Text)
import qualified Data.Text as T
import qualified Data.Text.Read as TR
import Graft (TextRange)
import Haskott.Defns
import Haskott.Spec
import Haskott.Term.Symterm

-- | A renaming: of metavariable roots, of metavariables (when given,
-- instead of the roots), of nonterminal roots, of nonterminals, and of
-- production names.
data Renaming = Renaming
  { rnMvr :: M.Map Text Text
  , rnMv :: Maybe [((Text, Suffix), (Text, Suffix))]
  , rnNtr :: M.Map Text Text
  , rnNt :: Maybe [((Text, Suffix), (Text, Suffix))]
  , rnPn :: M.Map Text Text
  }

mvrR, ntrR, pnR :: Renaming -> Text -> Text
mvrR m x = M.findWithDefault x x (rnMvr m)
ntrR m x = M.findWithDefault x x (rnNtr m)
pnR m x = M.findWithDefault x x (rnPn m)

mvR :: Renaming -> (Text, Suffix) -> (Text, Suffix)
mvR m mv@(mvr, suff) = case rnMv m of
  Just mp -> fromMaybe mv (lookup mv mp)
  Nothing -> (mvrR m mvr, suff)

ntR :: Renaming -> (Text, Suffix) -> (Text, Suffix)
ntR m nt@(ntr, suff) = case rnNt m of
  Just mp -> fromMaybe nt (lookup nt mp)
  Nothing -> (ntrR m ntr, suff)

rootR :: Renaming -> RootRef -> RootRef
rootR m r = case r of
  Mvr x -> Mvr (mvrR m x)
  Ntr x -> Ntr (ntrR m x)

suffixItemR :: Renaming -> SuffixItem -> SuffixItem
suffixItemR m si = case si of
  SiVar v n -> SiVar (mvrR m v) n
  _ -> si

boundR :: Renaming -> Bound -> Bound
boundR m b = case b of
  BoundDotform l u n -> BoundDotform (suffixItemR m l) (suffixItemR m u) n
  BoundComp v -> BoundComp (mvrR m v)
  BoundCompU v u -> BoundCompU (mvrR m v) (suffixItemR m u)
  BoundCompLU v l u n -> BoundCompLU (mvrR m v) (suffixItemR m l) (suffixItemR m u) n

elementR :: Renaming -> Element -> Element
elementR m e = case e of
  Nonterm ntr n s -> let (n', s') = ntR m (n, s) in Nonterm (ntrR m ntr) n' s'
  Metavar mvr n s -> let (n', s') = mvR m (n, s) in Metavar (mvrR m mvr) n' s'
  Terminal _ -> e
  ListForm lb -> ListForm lb {lbBound = boundR m <$> lbBound lb, lbElements = map (elementR m) (lbElements lb)}

mseR :: Renaming -> Mse -> Mse
mseR m mse = case mse of
  MetaVarExp mv -> MetaVarExp (mvR m mv)
  NonTermExp nt -> NonTermExp (ntR m nt)
  MetaVarListExp mv b -> MetaVarListExp (mvR m mv) (boundR m b)
  NonTermListExp nt b -> NonTermListExp (ntR m nt) (boundR m b)
  Aux f nt -> Aux f (ntR m nt)
  AuxList f nt b -> AuxList f (ntR m nt) (boundR m b)
  Union a b -> Union (mseR m a) (mseR m b)
  Empty -> Empty

bindspecR :: Renaming -> Bindspec -> Bindspec
bindspecR m b = case b of
  Bind mse nt r -> Bind (mseR m mse) (ntR m nt) r
  AuxFnDef f mse r -> AuxFnDef f (mseR m mse) r
  NamesEqual a b' r -> NamesEqual (mseR m a) (mseR m b') r
  NamesDistinct a b' r -> NamesDistinct (mseR m a) (mseR m b') r
  AllNamesDistinct a r -> AllNamesDistinct (mseR m a) r

symtermR :: Renaming -> Symterm -> Symterm
symtermR m st = case st of
  StNode ntr pn es -> StNode ntr pn (map (steR m) es)
  StNonterm ntrp nt -> StNonterm (ntrR m ntrp) (ntR m nt)
  StNontermSub l t nt -> StNontermSub (ntrR m l) (ntrR m t) (ntR m nt)
  StUninterpreted _ _ -> st

steR :: Renaming -> Ste -> Ste
steR m ste = case ste of
  SteSt st -> SteSt (symtermR m st)
  SteMetavar mvrp mv -> SteMetavar (mvrR m mvrp) (mvR m mv)
  SteVar mvr v -> SteVar (mvrR m mvr) v
  SteList stlis -> SteList (map stli stlis)
  where
    stli s = case s of
      StliSingle es -> StliSingle (map (steR m) es)
      StliListform b es -> StliListform (boundR m b) (map (steR m) es)

------------------------------------------------------------------------
-- Freshening

-- | Ott's @fresh_suffix@.
freshSuffix :: [Suffix] -> Suffix -> Suffix
freshSuffix suffs suff0 =
  let nums = [n | suff <- suffs, SiNum t <- suff, Right (n, _) <- [TR.decimal t :: Either String (Int, Text)]]
      next n = if n `elem` nums then next (n + 1) else n
      nonPrimeLength suff = if SiPunct "'" `elem` suff then 0 else length suff
      underscores = foldl' max 0 (map nonPrimeLength suffs)
      indices = [si | si@(SiIndex _) <- suff0]
   in replicate underscores (SiPunct "_") ++ [SiNum (T.pack (show (next 5)))] ++ indices

-- | Ott's @fresh_nt@.
freshNt :: [(Text, Suffix)] -> (Text, Suffix) -> (Text, Suffix)
freshNt nts (ntr0, suff0) = (ntr0, freshSuffix [s | (n, s) <- nts, n == ntr0] suff0)

removeDuplicates :: Eq a => [a] -> [a]
removeDuplicates xs = case xs of
  [] -> []
  x : more -> if x `elem` more then removeDuplicates more else x : removeDuplicates more

-- | Ott's @avoid@: a fresh suffix for each metavariable and nonterminal
-- written with its primary root and no suffix.
avoid :: Spec -> [(Text, Suffix)] -> [(Text, Suffix)] -> Renaming
avoid spec mvs0 nts0 =
  let mvdOf mvr = [md | md <- specMetavars spec, mvr `elem` map fst (mvdNames md)]
      mvs2 = [mv | mv@(mvr, _) <- removeDuplicates mvs0, md : _ <- [mvdOf mvr], not (mvdIndexvar md), mvr == mvdName md]
      mvMap = [(mv, (mvr, freshSuffix [s | (m', s) <- mvs2, m' == mvr] [])) | mv@(mvr, []) <- mvs2]
      primaries = map ruleName (specRules spec)
      nts2 = [nt | nt@(ntr, _) <- removeDuplicates nts0, ntr `elem` primaries]
      ntMap = [(nt, (ntr, freshSuffix [s | (n', s) <- nts2, n' == ntr] [])) | nt@(ntr, []) <- nts2]
   in Renaming M.empty (Just mvMap) M.empty (Just ntMap) M.empty

elementsMvs, elementsNts :: [Element] -> [(Text, Suffix)]
elementsMvs = concatMap el
  where
    el e = case e of
      Metavar _ n s -> [(n, s)]
      ListForm lb -> elementsMvs (lbElements lb)
      _ -> []
elementsNts = concatMap el
  where
    el e = case e of
      Nonterm _ n s -> [(n, s)]
      ListForm lb -> elementsNts (lbElements lb)
      _ -> []

symtermsNts, symtermsMvs :: [Symterm] -> [(Text, Suffix)]
symtermsNts = concatMap st
  where
    st s = case s of
      StNode _ _ es -> concatMap ste es
      StNonterm _ nt -> [nt]
      StNontermSub _ _ nt -> [nt]
      StUninterpreted _ _ -> []
    ste e = case e of
      SteSt s -> st s
      SteList stlis -> concatMap stli stlis
      _ -> []
    stli s = case s of
      StliSingle es -> concatMap ste es
      StliListform _ es -> concatMap ste es
symtermsMvs = concatMap st
  where
    st s = case s of
      StNode _ _ es -> concatMap ste es
      _ -> []
    ste e = case e of
      SteSt s -> st s
      SteMetavar _ mv -> [mv]
      SteList stlis -> concatMap stli stlis
      _ -> []
    stli s = case s of
      StliSingle es -> concatMap ste es
      StliListform _ es -> concatMap ste es

-- | Ott's @secondaryify@: every metavariable and nonterminal renamed to
-- a fresh one with the secondary root of its declaration (its second
-- name, if it has one).
secondaryify :: Spec -> [(Text, Suffix)] -> [(Text, Suffix)] -> Renaming
secondaryify spec mvs0 nts0 =
  let secondaryMvr mvr = case [map fst (mvdNames md) | md <- specMetavars spec, mvr `elem` map fst (mvdNames md)] of
        ((_ : q : _) : _) -> q
        _ -> mvr
      secondaryNtr ntr = case [map fst (ruleNames r) | r <- specRules spec, ntr `elem` map fst (ruleNames r)] of
        ((_ : q : _) : _) -> q
        _ -> ntr
      build secondary = foldl (\acc x@(r, suff) -> let r' = secondary r in (x, (r', freshSuffix [s | (_, (r'', s)) <- acc, r'' == r'] suff)) : acc) []
   in Renaming M.empty (Just (build secondaryMvr (removeDuplicates mvs0))) M.empty (Just (build secondaryNtr (removeDuplicates nts0))) M.empty

-- | Ott's @avoid_primaries_systemdefn@: with a fresh suffix for the
-- unsuffixed primaries (@-coq_avoid 1@), or secondary names for all
-- (@-coq_avoid 2@).
avoidPrimaries :: Bool -> Spec -> Processed -> (Spec, Processed)
avoidPrimaries secondary spec processed =
  let avoid' = if secondary then secondaryify spec else avoid spec
      prod p =
        let m = avoid' (elementsMvs (prodElements p)) (elementsNts (prodElements p))
         in p {prodElements = map (elementR m) (prodElements p), prodBindspecs = map (bindspecR m) (prodBindspecs p)}
      spec' = spec {specRules = [r {ruleProds = map prod (ruleProds r)} | r <- specRules spec]}
      drule dr =
        let sts = druleConclusion dr : map snd (drulePremises dr)
            m = avoid' (symtermsMvs sts) (symtermsNts sts)
         in dr {drulePremises = [(hn, symtermR m st) | (hn, st) <- drulePremises dr], druleConclusion = symtermR m (druleConclusion dr)}
      clause fc =
        let sts = [fcLhs fc, fcRhs fc]
            m = avoid' (symtermsMvs sts) (symtermsNts sts)
         in fc {fcLhs = symtermR m (fcLhs fc), fcRhs = symtermR m (fcRhs fc)}
      item it = case it of
        PReln pc -> PReln pc {pcDefns = [d {pdRules = map rule (pdRules d)} | d <- pcDefns pc]}
        PFuns pfc -> PFuns pfc {pfcFuns = [f {pfClauses = map clause (pfClauses f)} | f <- pfcFuns pfc]}
      rule ri = case ri of
        ItemRule dr -> ItemRule (drule dr)
        ItemComment {} -> ri
   in (spec', Processed (map item (processedItems processed)))

------------------------------------------------------------------------
-- OCaml

capitalizeAscii, uncapitalizeAscii :: Text -> Text
capitalizeAscii s = case T.uncons s of
  Just (c, rest) | c >= 'a' && c <= 'z' -> T.cons (toUpper c) rest
  _ -> s
uncapitalizeAscii s = case T.uncons s of
  Just (c, rest) | c >= 'A' && c <= 'Z' -> T.cons (toLower c) rest
  _ -> s

-- | Ott's @detect_conflicts@: the first name whose renaming is also the
-- renaming of a later one.
detectConflict :: [(TextRange, Text, Text)] -> Maybe (TextRange, Text)
detectConflict l = case l of
  [] -> Nothing
  (r, _, x) : tl -> if x `elem` [y | (_, _, y) <- tl] then Just (r, x) else detectConflict tl

-- | Ott's @caml_rename@, or the conflict it finds; with the renamings of
-- metavariable and nonterminal roots, for the dependencies and the
-- structure computed before it.
camlRename :: Spec -> Processed -> Either Diagnostic (Spec, Processed, Text -> Text, Text -> Text)
camlRename spec processed = do
  let prods = concatMap ruleProds (specRules spec)
      pns = [(prodRange p, prodName p, capitalizeAscii (prodName p)) | p <- prods]
      ntrs = [(ruleRange r, ruleName r, uncapitalizeAscii (ruleName r)) | r <- specRules spec]
      mvrs = [(mvdRange md, mvdName md, uncapitalizeAscii (mvdName md)) | md <- specMetavars spec]
      check what xs = case detectConflict xs of
        Just (r, x) -> Left (Diagnostic r ("Renaming of " <> what <> " \"" <> x <> "\" generates a conflict"))
        Nothing -> Right (M.fromList [(a, b) | (_, a, b) <- reverse xs])
  pnMap <- check "production name" pns
  ntrMap <- check "primary nontermroot" ntrs
  mvrMap <- check "primary metavar" mvrs
  let m = Renaming mvrMap Nothing ntrMap Nothing pnMap
  pure (renameSpec m spec, renameProcessed m processed, mvrR m, ntrR m)

renameSpec :: Renaming -> Spec -> Spec
renameSpec m spec =
  spec
    { specMetavars = [md {mvdName = mvrR m (mvdName md), mvdNames = [(mvrR m n, hs) | (n, hs) <- mvdNames md]} | md <- specMetavars spec]
    , specRules =
        [ r
            { ruleName = ntrR m (ruleName r)
            , ruleNames = [(ntrR m n, hs) | (n, hs) <- ruleNames r]
            , ruleProds = [p {prodName = pnR m (prodName p), prodElements = map (elementR m) (prodElements p), prodBindspecs = map (bindspecR m) (prodBindspecs p)} | p <- ruleProds r]
            }
        | r <- specRules spec
        ]
    , specSubrules = [sr {srLower = ntrR m (srLower sr), srUpper = ntrR m (srUpper sr), srTop = ntrR m (srTop sr)} | sr <- specSubrules spec]
    , specSubruleData =
        SubruleData
          { srdProperSubntrs = [(ntrR m n, map (ntrR m) ns) | (n, ns) <- srdProperSubntrs (specSubruleData spec)]
          , srdGraph = [(ntrR m a, ntrR m b) | (a, b) <- srdGraph (specSubruleData spec)]
          , srdPromotion = [(ntrR m a, (ntrR m b, [(pnR m x, pnR m y) | (x, y) <- pps])) | (a, (b, pps)) <- srdPromotion (specSubruleData spec)]
          }
    , specContextrules = [cr {crNtr = ntrR m (crNtr cr), crTarget = ntrR m (crTarget cr), crHole = ntrR m (crHole cr)} | cr <- specContextrules spec]
    , specSubstitutions = [sb {sbThis = ntrR m (sbThis sb), sbThat = rootR m (sbThat sb)} | sb <- specSubstitutions spec]
    , specFreevars = [fv {fvThat = rootR m (fvThat fv)} | fv <- specFreevars spec]
    }

renameProcessed :: Renaming -> Processed -> Processed
renameProcessed m (Processed items) = Processed (map item items)
  where
    item it = case it of
      PReln pc -> PReln pc {pcDefns = [d {pdRules = map rule (pdRules d)} | d <- pcDefns pc]}
      PFuns pfc -> PFuns pfc {pfcFuns = [f {pfClauses = [fc {fcLhs = symtermR m (fcLhs fc), fcRhs = symtermR m (fcRhs fc)} | fc <- pfClauses f]} | f <- pfcFuns pfc]}
    rule ri = case ri of
      ItemRule dr -> ItemRule dr {drulePremises = [(hn, symtermR m st) | (hn, st) <- drulePremises dr], druleConclusion = symtermR m (druleConclusion dr)}
      ItemComment {} -> ri

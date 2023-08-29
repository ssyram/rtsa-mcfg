{-# LANGUAGE TupleSections #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE Strict #-}
{-# OPTIONS_GHC -Wno-name-shadowing #-}
module EnumStr (
  enumStringTuples,
  enumStrings,
  NoStrError(..)
) where
import qualified Data.Map as M
import Objects (Term (..), Rule (..), MultiCtxFreeGrammar (mcfgRules, mcfgStartNonTer), Symbol (..), LocVarDecl (..))
import Control.Monad.Reader (ReaderT (runReaderT), asks)
import Control.Monad.Except (MonadError (throwError), Except, runExcept)
import qualified Data.List as L
import GHC.Generics (Generic)
import Data.Hashable (Hashable)
import Control.Monad.Cont (when, MonadTrans (..))
import Data.Maybe (fromMaybe, isJust)
import Utils
import Data.Tuple (swap)
import Control.Monad.ST.Strict (runST)
import Debug.Trace

-- TODO: FIX THIS BUGGY FILE:
-- 1. MUTUAL RECURSIVE RULES MAY LEAD TO INFINITE LOOP, SHOULD RANK THE RULES
-- 2. FINISH THE CONSTANT SUBSTITUTION PROCESS

-- To enumerate the strings of MCFG


-- | Const Term, without variable
newtype CTerm t = CTerm [t]
  deriving (Eq, Ord, Show, Generic, Hashable)
-- | Const RHS
newtype ConstLHS t = ConstLHS [CTerm t]
  deriving (Eq, Ord, Show, Generic, Hashable)



data EnumCtx nt t v = EnumCtx
  { constRules :: M.Map nt [ConstLHS t]
  , recurRules :: M.Map nt [Rule nt t v] }

data NoStrError = NoStrError

type EnumState nt t v = ReaderT (EnumCtx nt t v) (Except NoStrError)

mkEnumCtx :: (Ord nt, Show nt, Show t, Show v) => MultiCtxFreeGrammar nt t v -> EnumCtx nt t v
mkEnumCtx mcfg =
  mcfgRules mcfg
  |> M.toList
  |> concatMap (\(nt, lst) -> fmap (nt,) lst)
  |> L.partition (isConstRule . snd)
  |> fstMap (fmap $ sndMap rmRHS)
  |> pairMap (toColMap, toColMap)
  |> uncurry EnumCtx

-- | Whether this rule is a constant rule
isConstRule :: Rule nt t v -> Bool
isConstRule (Rule lhs _) = all (\(Term lst) -> all isTer lst) lhs
  where isTer (STerminal _) = True
        isTer (SVar _)      = False

-- | Remove the RHS and convert the whole Rule to `ConstLHS`
--   Put ONLY the constant rules
rmRHS ::
  (Show nt, Show t, Show v) =>
  Rule nt t v -> ConstLHS t
rmRHS rule@(Rule lhs _) =
  fmap (\(Term lst) -> CTerm $ unwrapTer <$> lst) lhs
  |> ConstLHS
  where
    unwrapTer (STerminal t) = t
    unwrapTer (SVar _) = error $ "Rule: \"" ++ show rule ++ "\" is NOT constant."

getWordAt :: (Ord nt, Show nt, Show t, Show v) => nt -> Int -> EnumState nt t v [[t]]
getWordAt nt idx = collectResultT $ do
  when (idx < 0) $ throwError NoStrError
  constLen <- tryConstRules nt idx
  idx <- return $ idx - constLen
  tryRecurRules nt idx


tryConstRules :: (Ord nt, Show nt, Show t) => nt -> Int -> ColT [[t]] (EnumState nt t v) Int
tryConstRules nt idx = do
  constRules <- asks constRules
  let cRules = fromMaybe [] $ constRules M.!? nt
      len = length cRules
  if idx < len then 
    trace (
      "Const Query: " ++
      show nt ++ "@" ++ show idx ++ 
      " with Rule: " ++ show (cRules !! idx)) $
    collect $ toTString $ cRules !! idx
  else return len

toTString :: ConstLHS t -> [[t]]
toTString (ConstLHS lst) = fmap mapper lst
  where mapper (CTerm lst) = lst


tryRecurRules :: (Ord nt, Show nt, Show t, Show v) => nt -> Int -> ColT [[t]] (EnumState nt t v) [[t]]
tryRecurRules nt idx = do
  recurRules <- asks recurRules
  let rRules = fromMaybe [] $ recurRules M.!? nt
      len = length rRules
  when (len == 0) $ throwError NoStrError

  -- Recursive Rules
  let (enumIdx, ruleIdx)  = idx `divMod` len
      rule@(Rule lhs rhs) = rRules !! ruleIdx
      rhsDist = enumMultipleDims (length rhs) enumIdx

  trace (
    "Recursive Query: " ++ 
    show nt ++ "@" ++ show idx ++ 
    " with Rule: " ++ show rule) $ return ()

  rhsVals <- lift $ mapM mapper $ zip rhsDist rhs
  return $ fmap (applyRHS rhsVals) lhs

  where
    mapper (idx, LocVarDecl (nt, _)) = getWordAt nt idx


applyRHS :: [ [[t]] ] -> Term t -> [t]
applyRHS rhsVals (Term lst) = concatMap (mapper rhsVals) lst
  where
    mapper _ (STerminal t) = [t]
    mapper rhsVals (SVar (ntIdx, vIdx)) = rhsVals !! ntIdx !! vIdx


-- | returns an MCFG with no purely constant non-terminal
--   except the case when the starting symbol is itself a contant symbol
substConstVars mcfg =
  let (constMap, nonConstRules) = divConstRules $ mcfgRules mcfg in
  performSubst constMap nonConstRules mcfg
  where
    performSubst constMap nonConstRules mcfg
      | M.null constMap = mcfg
      | stWithin constMap mcfg = filterOnlySt constMap mcfg
      | otherwise = mcfg { mcfgRules = remapRules constMap nonConstRules }

remapRules :: M.Map nt [ConstLHS t]
  -> M.Map nt [Rule nt t v] -> M.Map nt [Rule nt t v]
remapRules constMap = M.map (mapRules constMap)

mapRules constMap lst = do
  (Rule lhs rhs) <- lst
  -- Collect the information to be used
  -- Enumerate all the possible constant combinations
  -- Change the `lhs` to the target
  undefined

divConstRules ::
  (Ord nt, Show nt, Show t, Show v) =>
  M.Map nt [Rule nt t v]
  -> (M.Map nt [ConstLHS t], M.Map nt [Rule nt t v])
divConstRules rules =
  M.toList rules
  |> L.partition (all isConstRule . snd)
  |> fstMap (fmap $ sndMap $ fmap rmRHS)
  |> pairMap (M.fromList, M.fromList)

filterOnlySt :: Ord k =>
  M.Map k [ConstLHS t]
  -> MultiCtxFreeGrammar k t v -> MultiCtxFreeGrammar k t v
filterOnlySt constMap mcfg = mcfg
  { mcfgRules = getOnly (mcfgStartNonTer mcfg) constMap }
  where
    getOnly nt constMap =
      constMap M.! nt
      |> fmap constLHSToRule
      |> flip (M.insert nt) M.empty

constLHSToRule :: ConstLHS t -> Rule nt t v
constLHSToRule (ConstLHS cterms) =
  flip Rule [] $ fmap ctermToTerm cterms
  where ctermToTerm (CTerm lst) = Term $ fmap STerminal lst

stWithin :: Ord k => M.Map k a -> MultiCtxFreeGrammar k t v -> Bool
stWithin constMap mcfg =
  let stNt = mcfgStartNonTer mcfg in
  isJust $ M.lookup stNt constMap


-- | To enumerate strings according to the query
--   Input the inqueries about the strings
enumStringTuples ::
  (Functor f, Ord nt, Show nt, Show t, Show v) =>
  MultiCtxFreeGrammar nt t v
  -> f (nt, Int) -> f (Either NoStrError [[t]])
enumStringTuples mcfg queries =
  let ctx = mkEnumCtx mcfg in
  fmap (mapper ctx) queries
  where
    mapper ctx (nt, idx) =
      getWordAt nt idx
      |> flip runReaderT ctx
      |> runExcept

-- | Enumerate the strings
enumStrings ::
  (Functor f, Ord nt, Show nt, Show t, Show v) =>
  MultiCtxFreeGrammar nt t v -> f Int -> f (Either NoStrError [t])
enumStrings mcfg indices =
  let st = mcfgStartNonTer mcfg in
  fmap mapper $ enumStringTuples mcfg $ fmap (st,) indices
  where
    mapper (Left l) = Left l
    mapper (Right [x]) = Right x
    mapper (Right _) = error "NON-DIM-1 START NON-TERMINAL."

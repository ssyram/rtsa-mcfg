{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE Strict #-}
{-# LANGUAGE CPP #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE LambdaCase #-}
{-# OPTIONS_GHC -Wno-name-shadowing #-}
{-# OPTIONS_GHC -Wno-unused-do-bind #-}
{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}
{-# OPTIONS_GHC -Wno-deriving-defaults #-}
module GrammarToAut (
  State(..),
  LocMem(..),
  StackSym(..),
  mcfgToRtsa
) where
import Objects (MultiCtxFreeGrammar (mcfgRules, mcfgStartNonTer), Rule (..), RestrictedTreeStackAut (RestrictedTreeStackAut), SpUnit, Operation (OpDown, OpUp), LocVarDecl (LocVarDecl), Symbol (..), Term (..), ExtendedRTSA (ExtendedRTSA), Gamma (..))
import Control.Monad.Reader (forM, forM_)
import Control.Monad.Except (MonadIO (liftIO))
import Data.Hashable ( Hashable )
import GHC.Generics ( Generic )
import qualified Control.Monad.Logic as L (observeAllT)
import Utils (foldToLogicT, Modifiable (newRef, readRef, modifyRef), RevList (RevList), revToList, (<<-), (|>), sndMap, fstMap, hashTableToMap)
import qualified Data.HashTable.IO as HT
import Control.Applicative
import qualified Data.Map.Strict as M
import qualified Data.List as List
import qualified Data.Map.Merge.Strict as M
import Data.Maybe (fromMaybe)
import qualified Data.Set as S

type HashTable k v = HT.BasicHashTable k v


#define STD_DER deriving (Show, Eq, Ord, Generic, Hashable)

-- | States convey the information about:
--   - For new `up` operation, the required dimension
--   - For new `down` operation, the source condition
data State nt
  -- | target dimension to go when `up`
  = StDim Int
  -- | the down state with the current dimension
  | StDown (StackSym nt, Int)
  STD_DER
-- | (NT, idx)
newtype StackSym nt = StackSym (nt, Int)
  STD_DER
-- | Local memory
data LocMem nt t v
  = LMNew
  | LMRule (Rule (StackSym nt) t v)
  STD_DER


{-| Convert the MCFG to rTSA

The procedure of conversion then is given by:
- Find the required number of indices for all non-terminals to use.
- Collect information for all rules.
- Re-arrange the rule list to the transition map.
- Generate the whole information.
-}
mcfgToRtsa ::
  (Hashable nt, Ord nt, Ord t, Ord v) =>
  MultiCtxFreeGrammar nt t v
  -> IO (ExtendedRTSA (State nt) (LocMem nt t v) (StackSym nt) [t] SpUnit)
mcfgToRtsa mcfg = do
  downMap <- HT.new :: IO (HashTable k v)
  let rulesWithDimAmounts = prepareConvRules mcfg
  rules <- convertRules downMap rulesWithDimAmounts
  let map = fmap (fstMap $ \(q, m, ig) -> (q, m, GNorm ig)) rules
            |> (initRules mcfg ++)
            |> fmap (sndMap (:[]))
            |> M.fromListWith (++)
            |> M.map S.fromList
      kMap = getKMap mcfg $ M.fromList $ fmap (sndMap fst) rulesWithDimAmounts
      k = M.toList kMap
          |> fmap snd
          |> foldl max 0
  downMap <- M.map S.fromList <$> hashTableToMap downMap
  let rtsa = RestrictedTreeStackAut map (StDim 0) LMNew k
  return $ ExtendedRTSA rtsa (Just kMap) (Just downMap)

initRules ::
  MultiCtxFreeGrammar nt t v
  -> [((State nt, LocMem nt t v, Gamma (StackSym nt)), ([t], Op nt t v))]
initRules mcfg =
  let startNt = mcfgStartNonTer mcfg
      stDown = StDown (StackSym (startNt, 0), 0)
  in
  [ ((StDim 0, LMNew, GBot), ([], OpUp   (StDim 0) LMNew (StackSym (startNt, 0))))
  , ((stDown , LMNew, GBot), ([], OpDown (StDim 0) LMNew))
  ]

getKMap :: Ord nt => MultiCtxFreeGrammar nt t v -> M.Map nt Int -> M.Map (StackSym nt) Int
getKMap mcfg dimAmountMap =
  mcfgRules mcfg
  |> M.map mapper
  |> M.toList
  |> expandMap dimAmountMap
  |> M.fromList
  where
    mapper = \case
      [] -> 0
      (Rule terms _) : _ -> length terms
    expandMap dimAmountMap lst = do
      (nt, k) <- lst
      let amount = fromMaybe 0 $ dimAmountMap M.!? nt
      idx <- [0..amount - 1]
      return (StackSym (nt, idx), k)
      
prepareConvRules :: Ord k => MultiCtxFreeGrammar k t v -> [(k, (Int, [Rule k t v]))]
prepareConvRules mcfg =
  M.toList (mcfgRules mcfg)
  |> concatMap snd
  |> fmap (fmap (\(LocVarDecl (nt, _)) -> nt) . rhs)
  |> fmap (M.fromList . fmap (\l -> (head l, length l)) . List.group . List.sort)
  |> foldl (M.unionWith max) M.empty
  |> M.merge onlyRules onlyDim combine (mcfgRules mcfg)
  |> M.toList
  where
    -- DEBUG: when only rules but not RHS, still regard as having `1` NOT `0`.
    onlyRules :: M.SimpleWhenMissing k x (Int, x)
    onlyRules = M.mapMaybeMissing $ \_ rules -> return (1, rules)
    onlyDim :: M.SimpleWhenMissing k y (y, [x])
    onlyDim   = M.mapMaybeMissing $ \_ dim   -> return (dim, [])
    combine :: M.SimpleWhenMatched k y x (x, y)
    combine   = M.zipWithMatched  $ \_ rules dim -> (dim, rules)


type Op nt t v = Operation (State nt) (LocMem nt t v) (StackSym nt) SpUnit


{-| Translate the given rule in the following way:

Let the rule be:

> N (t1, ..., tn) <- NT-1 (..), ... NT-n (..)

Each RHS must be of distinct non-terminals and for each rule the variable should have a map.

The branching rules:

> (StDim n, LMNew, NT-i) |-> op_n_Rule

So, for the dimension `n` of `Rule` of `NT` with index `i`, the translation is given by:
- starting with status (StDim n, {LMNew | LMRule Rule}, NT-i)
- take out term `tn`, binded by `t` from `Rule` and then inductively goes by:
  + If `t == []`: the operation is (StDown NT-i, LMRule Rule, down)
  + If `t == h : t'`:
    * If `h` is Terminal, collect it to the next `info`, continue
    * If `h` is Variable from `v-j` of `NT-k`, 
      the operation is (StDim j, LMRule Rule, up NT-k)
      clear `info`, change the next status to generate operation to be:
      (StDown NT-k, LMRule Rule, NT-i)

So the procedure goes by traversing `tn`, during the stuff, at each step, modify the environment.
-}
convertRules ::
  (Hashable nt, Eq nt) =>HashTable (State nt, StackSym nt) [State nt]
  -> [(nt, (Int, [Rule nt t v]))]
  -> IO [((State nt, LocMem nt t v, StackSym nt), ([t], Op nt t v))]
convertRules downMap lst = L.observeAllT $ do
  (nt, (ntIdxAmount, rules)) <- foldToLogicT lst
  oriRule <- foldToLogicT rules
  -- modify the rules
  rule@(Rule terms rhs) <- liftIO $ retagRHS oriRule

  -- intialise analysis environment
  ntIdx <- foldToLogicT [0..ntIdxAmount - 1]
  curM <- return LMNew <|> return (LMRule rule)
  (termIdx, Term term) <- foldToLogicT $ zip [0..] terms
  let nextM = LMRule rule
  let curGamma = StackSym (nt, ntIdx)

  -- traverse and add terms
  -- initialise the data structure and aux function
  resultRules <- liftIO $ newRef []
  let initSt = StDim termIdx
  curStatus <- liftIO $ newRef (initSt, curM, curGamma)
  curRevInfo <- liftIO $ newRef $ RevList []
  let addRule op = do
        status <- readRef curStatus
        revInfo <- readRef curRevInfo
        modifyRef resultRules ((status, (revToList revInfo, op)):)


  -- traverse each element
  liftIO $ forM_ term $ \case
    STerminal t -> modifyRef curRevInfo $ \(RevList l) -> RevList (t:l)
    SVar (ntIdx, upDim) -> do
      let LocVarDecl (stkSym, _) = rhs !! ntIdx
      -- (StDim j, LMRule Rule, up NT-k)
      addRule $ OpUp (StDim upDim) nextM stkSym
      -- clear `info`
      curRevInfo <<- RevList []
      -- update `status`
      -- (StDown NT-k, LMRule Rule, NT-i)
      curStatus <<- (StDown (stkSym, upDim), nextM, curGamma)

  -- finally, add the `down` operation
  let endSt = StDown (StackSym (nt, ntIdx), termIdx)
  let op = OpDown endSt nextM
  liftIO $ addRule op
  -- add to the given `downMap`
  liftIO $ HT.mutate downMap (initSt, curGamma) $ \case
     Nothing  -> (Just [endSt], ())
     Just sts -> (Just $ endSt : sts, ())


  -- return the results in the cell
  lst <- liftIO $ readRef resultRules
  foldToLogicT lst


retagRHS :: (Hashable nt, Eq nt) =>Rule nt t v -> IO (Rule (StackSym nt) t v)
retagRHS (Rule terms rhs) = do
  ntIdxMap <- HT.new :: IO (HashTable k v)
  rhs <- forM rhs $ \(LocVarDecl (nt, vars)) -> do
    nextIdx <- HT.mutate ntIdxMap nt $ \case
       Nothing  -> (Just 1, 0)
       Just idx -> (Just $ idx + 1, idx)
    return $ LocVarDecl (StackSym (nt, nextIdx), vars)
  return $ Rule terms rhs


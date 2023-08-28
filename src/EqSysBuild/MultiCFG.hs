{-# LANGUAGE InstanceSigs #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleContexts #-}
{-# OPTIONS_GHC -Wno-name-shadowing #-}
{-# LANGUAGE LambdaCase #-}
{-# OPTIONS_GHC -Wno-incomplete-uni-patterns #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE MonoLocalBinds #-}
{-# OPTIONS_GHC -Wno-deriving-defaults #-}
{-# OPTIONS_GHC -Wno-redundant-constraints #-}
module EqSysBuild.MultiCFG (
  NonTer,
  Var(..),
  Sym,
  AccInfo,
  rTSAToMultiCFG
) where
import Objects (RestrictedTreeStackAut, Gamma (GNorm), Symbol (SVar, STerminal), mapInfo, MultiCtxFreeGrammar (MultiCtxFreeGrammar), Rule (Rule), Term (Term), LocVarDecl (LocVarDecl), ExtendedRTSA (eRtsaAutomaton))
import Utils (RevList (..), revToList, toRevList, (|>), Modifiable (newRef, readRef, modifyRef), sndMap, toLogicT, toColMap, stAutoCallCount)
import EqSysBuild (AccStepInfo (..), StdReq, EqSys (..), AbsVar (AbsVar), SynComp (SynComp), x0Of, defGetBuildContext, runConstruction, BuildContext (flags), Flags (noUpVar))
import EqSysSimp (removeEmptyVars, removeDuplicatedVars, collectDuplicateInfo)
import qualified Data.Map.Strict as M
import Control.Monad.ST (runST, ST)
import qualified Data.HashTable.ST.Basic as HT
import Data.Hashable ( Hashable )
import Data.HashTable.ST.Basic (HashTable)
import Control.Monad.Cont (forM_, guard, forM)
import Data.STRef.Strict (STRef)
import GHC.Generics (Generic)
import Debug.Trace (trace)
import qualified Data.Set as S
import Control.Monad.Logic (observeAllT)
import qualified Data.UnionFind.ST as UF
import Control.Monad.ST.Class (MonadST(liftST))
import qualified Data.HashTable.Class as HT (fromList)


-- ------------------------------ Concepts Definition ------------------------------


type NonTer q g = AbsVar q g

newtype Var v = Var (v, Int)

instance Show g => Show (Var g) where
  show :: Show g => Var g -> String
  show (Var p) = "v@" ++ show p

data InSym t g
  = ISTer t
  | ISVar g
  deriving (Eq, Ord, Generic, Hashable, Show)

type Sym t = Symbol t

{-| Its operation (in non-reversed mode):

> [[..], ..., [x1 x2]] <> [[x3 x4], ..., [..]] => [[..], ..., [x1 x2 x3 x4], ..., [..]]

>>> revDoubleRevList $ toDoubleRevList [[1, 2], [3, 4], [5, 6]] <> toDoubleRevList [[7, 8], [9, 10], [11, 12]]
[[1,2],[3,4],[5,6,7,8],[9,10],[11,12]]
-}
newtype DRevList g = DRevList (RevList (RevList g))
  deriving (Eq, Ord, Generic, Hashable)

instance Show g => Show (DRevList g) where
  show :: Show g => DRevList g -> String
  show = show . revDoubleRevList

revDoubleRevList :: DRevList a -> [[a]]
revDoubleRevList (DRevList lst) = revToList <$> revToList lst

toDoubleRevList :: [[a]] -> DRevList a
toDoubleRevList lst = DRevList $ toRevList $ toRevList <$> lst

instance Semigroup (DRevList g) where
  (<>) :: DRevList g -> DRevList g -> DRevList g
  l <> (DRevList (RevList [])) = l
  (DRevList (RevList [])) <> r = r
  (DRevList (RevList (rl : rl's))) <> (DRevList (RevList [x])) = DRevList $ RevList ((rl <> x) : rl's)
  l <> (DRevList (RevList (rl : rl's))) =
    let (DRevList (RevList recur)) = l <> DRevList (RevList rl's) in
    DRevList $ RevList $ rl : recur

instance Monoid (DRevList g) where
  mempty :: DRevList g
  mempty = DRevList $ RevList []



type AccInfo t g = DRevList (InSym t g)

-- -- >>> test
-- -- DRevList (RevList [RevList [ISVar (InVar 2),ISTer 1]])
-- test :: DRevList (InSym Integer Integer)
-- test = mappendUpMark (DRevList (RevList [RevList [ISTer 1]])) 2

instance AccStepInfo (AccInfo t g) g where
  mappendDownMark :: AccInfo t g -> AccInfo t g
  mappendDownMark (DRevList (RevList rls)) = DRevList $ RevList $ RevList [] : rls
  mappendUpMark :: AccInfo t g -> g -> AccInfo t g
  mappendUpMark drl g = drl <> DRevList (RevList [RevList [ISVar g]])


-- --------------------------- Actual Conversion Function ---------------------------


{-| To convert the given rTSA to a MCFG.

Procedure:
- Prepare the rTSA to be with the `AccInfo`.
- Construct the equation system.
- Erase the empty variables.
- Remove the duplicated variables with identical RHS.
- Convert the equation system to the MCFG.
-}
rTSAToMultiCFG ::
  (StdReq q m g sp (AccInfo t g), Ord q, Ord m, Ord (sp q m g), Ord t, Hashable t) =>
  ExtendedRTSA q m g [t] sp
  -> IO (MultiCtxFreeGrammar (NonTer q g) t (Var g))
rTSAToMultiCFG eRtsa = do
  let rtsa = prepareRTSA $ eRtsaAutomaton eRtsa
  ctx <- defGetBuildContext eRtsa { eRtsaAutomaton = rtsa }
  eqSys <- runConstruction ctx { flags = (flags ctx) { noUpVar = True } } $ x0Of rtsa
  trace (show eqSys) $ return ()
  (_zeroVars, eqSys) <- return $ removeEmptyVars eqSys
  -- trace ("Empty vars found: " ++ show _zeroVars) $ return ()
  let x0 = x0Of rtsa
  -- DEBUG: cannot use the original procedure for `removeDuplicatedVars`
  -- Because the `acc` part should also be changed when the new information is found.
  eqSys <- return $ replaceDupRules eqSys
  return $ eqSysToMultiCFG x0 eqSys

replaceDupRules eqSys@(EqSys lst) = runST $ do
  varTab <- collectDuplicateInfo nonNumNormalise eqSys
  EqSys <$> replaceRules varTab lst

replaceRules varTab lst = observeAllT $ do
  (v, comps) <- toLogicT lst
  ~(Just p) <- liftST $ HT.lookup varTab v
  dv <- liftST $ UF.descriptor p
  guard $ v == dv
  comps <- liftST $ mapM (replaceComp varTab) comps
  return (v, comps)

-- | Tag the given information with also the id information
newtype WId g = WId (g, Int)

{-| Given a component: c * v1 * ... * vn

In `c`, which is a double list: [[...], ..., [...]], when a stuff is to be replaced
we should also replace the variable inside with id
-}
replaceComp varTab (SynComp (acc, vs)) = do
  -- Set up a `g` map from the current variables to the new one
  oldNewGMap <- HT.new
  vs <- forM vs $ \v -> do
    undefined
  -- Replace the old `g` with the new tagged `g`
  undefined

-- | Does not merge / combine the `acc` information in the equation system
nonNumNormalise :: (Monad m, Ord k, Ord a) =>
  EqSys k a -> m [(k, M.Map (M.Map k Int) (S.Set a))]
nonNumNormalise (EqSys lst) = return $ fmap (sndMap mapper) lst
  where
    mapper lst =
      M.fromListWith S.union $ fmap conj lst
    conj (SynComp (c, vs)) =
      (M.fromListWith (+) $ map (,1 :: Int) vs, S.insert c S.empty)
    

-- --------------------------- Aux Functions for the Core ---------------------------


-- | Technical function, to convert to `AccInfo`, to fit the equation construction
prepareRTSA ::
  (Ord q, Ord m, Ord g, Ord (sp q m g), Ord t) =>
  RestrictedTreeStackAut q m g [t] sp
  -> RestrictedTreeStackAut q m g (AccInfo t g) sp
prepareRTSA = mapInfo toAccInfo
  where
    toAccInfo str =
      fmap ISTer str
      |> (:[])
      |> toDoubleRevList



-- ---------------------------- From EqSys to MCFG ----------------------------


{-| To convert the equation system to a MCFG

An equation system:

> x = \sum_i acc_i * \prod_j x_ij

Is converted to:

> x (acc_i) <- x_i1 ... x_ij

The assumed characteristic of the equation system:
- 
-}
eqSysToMultiCFG ::
  (Hashable v, Show v, Ord v) =>
  v
  -> EqSys v (AccInfo t v)
  -> MultiCtxFreeGrammar v t (Var v)
eqSysToMultiCFG x0 eqSys =
  genMultiCFGRuleList eqSys
  |> toColMap
  |> flip MultiCtxFreeGrammar x0


-- | Convert the equation system to a list of MCFG rules
genMultiCFGRuleList ::
  (Hashable v, Show v) =>
  EqSys v (AccInfo t v)
  -> [(v, Rule v t (Var v))]
genMultiCFGRuleList (EqSys lst) = do
  (v, comp) <- lst
  (SynComp (acc, vars)) <- comp
  let (body, rhs) = computeRuleContent acc vars
  -- let body = revDoubleRevList acc
  --            |> retagList
  --            |> fmap Term
  --     rhs  =
  --       [
  --         LocVarDecl (v, [ Var (v, idx) | idx <- [0..maxIdx] ])
  --         |
  --         (v, maxIdx) <- M.toList $ maxIdxMap vars $ revDoubleRevList acc
  --       ]
  return (v, Rule body rhs)

-- maxIdxMap vars  = M.fromListWith max $ do
--   term <- body


computeRuleContent acc vars = runST $ do
  let lst = revDoubleRevList acc
  getNextIdx <- stAutoCallCount  -- the dimension of the variables
  varIdxMap <- HT.fromList $ zip vars [0 :: Int ..]

  -- Traverse `lst` to number it at the same time, the `varDimMap` will be initialised
  lst <- forM lst $ mapM $ \case
    ISTer t -> return $ STerminal t
    ISVar v -> HT.lookup varIdxMap v >>= \case
      Nothing -> error $
        "INTERNAL ERROR: when convert, found non-RHS variable for " ++
        show v
      Just rhsIdx -> do
        nextDimIdx <- getNextIdx v
        return $ SVar (rhsIdx, nextDimIdx)

  let body = fmap Term lst
  
  undefined


-- -- | Technical function to convert the `InSym` to `Sym` -- adding index to variables
-- retagList :: [[InSym t v]] -> [[Sym t]]
-- retagList lst = runST $ do
--   gMap <- HT.new
--   initGMap gMap lst
--   gNextIdxMap <- HT.new
--   mapM (mapM $ retagSym gMap gNextIdxMap) lst
--   where
--     retagSym gMap gNextIdxMap = \case
--       ISTer t -> return $ STerminal t
--       ISVar g -> do
--         ~(Just ntIdx) <- HT.lookup gMap g
--         HT.mutate gNextIdxMap g $ \case
--           Nothing -> (Just 1, SVar (ntIdx, 0))
--           Just nv -> (Just $ nv + 1, SVar (ntIdx, nv))

-- initGMap :: (Hashable g) => HashTable s g Int -> [[InSym t g]] -> ST s ()
-- initGMap gMap (lst :: [[InSym t g]]) = do
--   ref :: STRef s Int <- newRef 0
--   forM_ lst $ mapM_ $ \case
--     ISTer _  -> return ()
--     ISVar g -> do
--       HT.mutateST gMap g $ \case
--         Nothing -> do
--           next <- readRef ref
--           modifyRef ref (+1)
--           return (Just next, ())
--         Just ov -> return (Just ov, ())

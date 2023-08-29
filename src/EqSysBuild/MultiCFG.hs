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
{-# LANGUAGE TupleSections #-}
module EqSysBuild.MultiCFG (
  NonTer,
  Var(..),
  Sym,
  AccInfo,
  rTSAToMultiCFG
) where
import Objects (RestrictedTreeStackAut, Gamma (GNorm), Symbol (SVar, STerminal), mapInfo, MultiCtxFreeGrammar (MultiCtxFreeGrammar), Rule (Rule), Term (Term), LocVarDecl (LocVarDecl), ExtendedRTSA (eRtsaAutomaton))
import Utils (RevList (..), revToList, toRevList, (|>), sndMap, toLogicT, toColMap, stAutoNumber, stAutoCallCount)
import EqSysBuild (AccStepInfo (..), StdReq, EqSys (..), AbsVar (AbsVar), SynComp (SynComp), x0Of, defGetBuildContext, runConstruction, BuildContext (flags), Flags (noUpVar))
import EqSysSimp (removeEmptyVars, collectDuplicateInfo)
import qualified Data.Map.Strict as M
import Control.Monad.ST (runST, ST)
import qualified Data.HashTable.ST.Basic as HT
import Data.Hashable ( Hashable )
import Data.HashTable.ST.Basic (HashTable)
import Control.Monad.Cont (guard, forM)
import GHC.Generics (Generic)
import Debug.Trace (trace)
import qualified Data.Set as S
import Control.Monad.Logic (observeAllT)
import qualified Data.UnionFind.ST as UF
import Control.Monad.ST.Class (MonadST(liftST), World)


-- --------------------------------- Concepts Definition ---------------------------------


type NonTer q g = AbsVar q g

newtype Var g = Var (g, Int)

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
  (StdReq q m g sp (AccInfo t g), Ord q, Ord m, Ord (sp q m g), Ord t, Hashable t, Eq t) =>
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
  -- Decision: defer the duplication replacement to the MCFG conversion process
  -- eqSys <- return $ replaceDupRules eqSys
  return $ eqSysToMultiCFG x0 eqSys


-- replaceDupRules eqSys@(EqSys lst) = runST $ do
--   varTab <- collectDuplicateInfo nonNumNormalise eqSys
--   EqSys <$> replaceRules varTab lst

-- replaceRules varTab lst = observeAllT $ do
--   (v, comps) <- toLogicT lst
--   ~(Just p) <- liftST $ HT.lookup varTab v
--   dv <- liftST $ UF.descriptor p
--   guard $ v == dv
--   -- TODO: define `replaceComp`
--   comps <- liftST $ mapM (replaceComp varTab) comps
--   return (v, comps)

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


{-| To convert the equation system to an MCFG

An equation system:

> x = \sum_i acc_i * \prod_j x_ij

Is converted to:

> x (acc_i) <- x_i1 ... x_ij
-}
eqSysToMultiCFG ::
  (Ord g, Ord q, Hashable g, Eq g, Hashable q, Eq q, Hashable t, Eq t, Ord t) =>
  AbsVar q g
  -> EqSys (AbsVar q g) (AccInfo t g)
  -> MultiCtxFreeGrammar (NonTer q g) t (Var g)
eqSysToMultiCFG x0 eqSys =
  genMultiCFGRuleList eqSys
  |> toColMap
  |> flip MultiCtxFreeGrammar x0



-- | Convert the equation system to a list of MCFG rules
genMultiCFGRuleList ::
  (Hashable g, Eq g, Hashable q, Eq q, Hashable t, Eq t, Ord q, Ord g, Ord t) =>
  EqSys (AbsVar q g) (AccInfo t g)
  -> [(NonTer q g, Rule (NonTer q g) t (Var g))]
genMultiCFGRuleList eqSys@(EqSys lst) = runST $ observeAllT $ do
  varEqTab <- liftST $ collectDuplicateInfo nonNumNormalise eqSys
  (v, comps) <- toLogicT lst

  -- Guard to remove the duplicating rules, when no need to convert
  dv <- getDesV varEqTab v
  guard $ v == dv

  -- Do the core job
  comp <- toLogicT comps
  rule <- liftST $ computeRule varEqTab comp

  return (v, rule)


-- | Compute the Rule content, given a variable table, and the `SynComp`
--   Returns the rule
computeRule ::
  (Hashable g, Eq g, Hashable q, Eq q) =>
  HashTable s (AbsVar q g) (UF.Point s (AbsVar q g))
  -> SynComp (AbsVar q g) (DRevList (InSym t g))
  -> ST s (Rule (AbsVar q g) t (Var g))
computeRule varEqTab (SynComp (acc, vars)) = do
  let accLst = revDoubleRevList acc
  -- The map for `g` idx to be appear in `accLst`, correspond to the RHS id
  getGId <- stAutoNumber
  getNextId <- stAutoCallCount

  -- First build the RHS, mainly to record the RHS idx information
  rhs <- forM vars $ \v@(AbsVar _ _ ~(GNorm g)) -> do
    _ntId <- getGId g  -- This is to register this direction `g`
    dv@(AbsVar len _ _) <- getDesV varEqTab v
    return $ LocVarDecl (dv, [ Var (g, vId) | vId <- [0..(len - 1) `div` 2] ])

  -- During converting the body, use the `g` information is enough for vars
  body <- forM accLst $ mapM $ \case
    ISTer t -> return $ STerminal t
    ISVar g -> do
      ntId <- getGId g  -- Get the non-terminal direction
      vId  <- getNextId g  -- Get the next id as the vId for it
      return $ SVar (ntId, vId)
  
  -- Return
  return $ Rule (Term <$> body) rhs


getDesV :: (MonadST m, Hashable k, Eq k) =>
  HashTable (World m) k (UF.Point (World m) b) -> k -> m b
getDesV varEqTab v = do
  ~(Just p) <- liftST $ HT.lookup varEqTab v
  liftST $ UF.descriptor p


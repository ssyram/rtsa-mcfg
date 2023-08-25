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
module EqSysBuild.MultiCFG (
  NonTer,
  Var(..),
  Sym,
  AccInfo,
  rTSAToMultiCFG
) where
import Objects (RestrictedTreeStackAut, Gamma (GNorm), Symbol (SVar, STerminal), mapInfo, MultiCtxFreeGrammar (MultiCtxFreeGrammar), Rule (Rule), Term (Term), LocVarDecl (LocVarDecl), ExtendedRTSA (eRtsaAutomaton))
import Utils (RevList (..), revToList, toRevList, (|>), Modifiable (newRef, readRef, modifyRef))
import EqSysBuild (AccStepInfo (..), StdReq, constructEqSysFromX0, EqSys (..), AbsVar (AbsVar), SynComp (SynComp), x0Of, SpOp)
import EqSysSimp (removeEmptyVars)
import qualified Data.Map.Strict as M
import Control.Monad.ST (runST, ST)
import qualified Data.HashTable.ST.Basic as HT
import Data.Hashable ( Hashable )
import Data.HashTable.ST.Basic (HashTable)
import Control.Monad.Cont (forM_)
import Data.STRef.Strict (STRef)
import GHC.Generics (Generic)


-- ------------------------------ Concepts Definition ------------------------------


type NonTer q g = AbsVar q g
-- | Internal Var
newtype InVar g = InVar g deriving (Eq, Ord, Generic, Hashable)

newtype Var g = Var (g, Int)

data InSym t g
  = ISTer t
  | ISVar (InVar g)
  deriving (Eq, Ord, Generic, Hashable)

type Sym t = Symbol t

{-| Its operation (in non-reversed mode):

> [[..], ..., [x1 x2]] <> [[x3 x4], ..., [..]] => [[..], ..., [x1 x2 x3 x4], ..., [..]]

>>> revDoubleRevList $ toDoubleRevList [[1, 2], [3, 4], [5, 6]] <> toDoubleRevList [[7, 8], [9, 10], [11, 12]]
[[1,2],[3,4],[5,6,7,8],[9,10],[11,12]]
-}
newtype DRevList g = DRevList (RevList (RevList g))
  deriving (Eq, Ord)

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

instance AccStepInfo (AccInfo t g) g where
  mappendDownMark :: AccInfo t g -> AccInfo t g
  mappendDownMark (DRevList (RevList rls)) = DRevList $ RevList $ RevList [] : rls
  mappendUpMark :: AccInfo t g -> g -> AccInfo t g
  mappendUpMark drl g = drl <> DRevList (RevList [RevList [ISVar $ InVar g]])


-- --------------------------- Actual Conversion Function ---------------------------


{-| To convert the given rTSA to a MCFG.

Procedure:
- Prepare the rTSA to be with the `AccInfo`.
- Construct the equation system.
- Erase the empty variables.
- Convert the equation system to the MCFG.
-}
rTSAToMultiCFG ::
  (StdReq q m g (AccInfo t g), Ord q, SpOp sp, Ord m, Ord (sp q m g), Ord t) =>
  ExtendedRTSA q m g [t] sp
  -> IO (MultiCtxFreeGrammar (NonTer q g) t (Var g))
rTSAToMultiCFG eRtsa = do
  let rtsa = prepareRTSA $ eRtsaAutomaton eRtsa
  eqSys <- constructEqSysFromX0 $ eRtsa { eRtsaAutomaton = rtsa }
  (_zeroVars, eqSys) <- return $ removeEmptyVars eqSys
  let x0 = x0Of rtsa
  return $ eqSysToMultiCFG x0 eqSys


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


{-| To convert the equation system to a MCFG

An equation system:

> x = \sum_i acc_i * \prod_j x_ij

Is converted to:

> x (acc_i) <- x_i1 ... x_ij
-}
eqSysToMultiCFG :: (Ord g, Ord q, Hashable g) =>
  AbsVar q g
  -> EqSys (AbsVar q g) (AccInfo t g)
  -> MultiCtxFreeGrammar (NonTer q g) t (Var g)
eqSysToMultiCFG x0 eqSys =
  genMultiCFGRuleList eqSys
  |> foldl addToMap M.empty
  |> flip MultiCtxFreeGrammar x0
  where
    alterMap :: Monad m => a -> Maybe [a] -> m [a]
    alterMap e = \case
      Nothing -> return [e]
      Just el -> return $ e : el
    addToMap :: Ord k => M.Map k [a] -> (k, a) -> M.Map k [a]
    addToMap map (v, e) =
      M.alter (alterMap e) v map


-- | Convert the equation system to a list of MCFG rules
genMultiCFGRuleList ::
  (Hashable g) => EqSys (AbsVar q g) (AccInfo t g)
  -> [(NonTer q g, Rule (NonTer q g) t (Var g))]
genMultiCFGRuleList (EqSys lst) = do
  (v, comp) <- lst
  (SynComp (acc, vars)) <- comp
  let body = revDoubleRevList acc
             |> retagList
             |> fmap Term
      rhs  =
        [
          LocVarDecl (v, [ Var (g, idx) | idx <- [0..len `div` 2] ])
          |
          v@(AbsVar len _ ~(GNorm g)) <- vars
        ]
  return (v, Rule body rhs)


-- | Technical function to convert the `InSym` to `Sym` -- adding index to variables
retagList ::
  (Hashable g) => [[InSym t g]] -> [[Sym t]]
retagList lst = runST $ do
  gMap <- HT.new
  initGMap gMap lst
  gNextIdxMap <- HT.new
  mapM (mapM $ retagSym gMap gNextIdxMap) lst
  where
    retagSym gMap gNextIdxMap = \case
      ISTer t -> return $ STerminal t
      ISVar (InVar g) -> do
        ~(Just ntIdx) <- HT.lookup gMap g
        HT.mutate gNextIdxMap g $ \case
          Nothing -> (Just 1, SVar (ntIdx, 0))
          Just nv -> (Just $ nv + 1, SVar (ntIdx, nv))

initGMap :: (Hashable g) =>HashTable s g Int -> [[InSym t g]] -> ST s ()
initGMap gMap (lst :: [[InSym t g]]) = do
  ref :: STRef s Int <- newRef 0
  forM_ lst $ mapM_ $ \case
    ISTer _  -> return ()
    ISVar (InVar g) -> do
      HT.mutateST gMap g $ \case
        Nothing -> do
          next <- readRef ref
          modifyRef ref (+1)
          return (Just next, ())
        Just ov -> return (Just ov, ())

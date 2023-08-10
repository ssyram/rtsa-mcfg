{-# LANGUAGE InstanceSigs #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
module EqSysBuild.MultiCFG where
import Objects (RestrictedTreeStackAut, SpTer, Gamma, Symbol (SVar))
import Utils (RevList (..), revToList, toRevList)
import EqSysBuild (AccStepInfo (..))

type StrGenRPTSA q m g = RestrictedTreeStackAut q m g String SpTer

newtype NonTer g = NonTer (Gamma g)
newtype Var g = Var g
newtype Ter = Ter String

type Sym g = Symbol Ter (Var g)

{-| Its operation (in non-reversed mode):

> [[..], ..., [x1 x2]] <> [[x3 x4], ..., [..]] => [[..], ..., [x1 x2 x3 x4], ..., [..]]

>>> revDoubleRevList $ toDoubleRevList [[1, 2], [3, 4], [5, 6]] <> toDoubleRevList [[7, 8], [9, 10], [11, 12]]
[[1,2],[3,4],[5,6,7,8],[9,10],[11,12]]
-}
newtype DRevList g = DRevList (RevList (RevList g))

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

type AccInfo g = DRevList (Sym g)

instance AccStepInfo (AccInfo g) g where
  mappendDownMark :: AccInfo g -> AccInfo g
  mappendDownMark (DRevList (RevList rls)) = DRevList $ RevList $ RevList [] : rls
  mappendUpMark :: AccInfo g -> g -> AccInfo g
  mappendUpMark drl g = drl <> DRevList (RevList [RevList [SVar $ Var g]])



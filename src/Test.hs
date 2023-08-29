{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE InstanceSigs #-}
{-# OPTIONS_GHC -Wno-redundant-constraints #-}
module Test where
import EqSysBuild
import Control.Monad.Identity (Identity(..))
import EqSysSimp
import Data.Hashable (Hashable)
import GHC.Generics (Generic)
import Objects (MultiCtxFreeGrammar)
import Examples (exampleCOPY, toNStringMCFG)
import Utils
import EnumStr


newtype PInt = PInt Int
  deriving (Eq, Ord, Generic, Hashable, Num)

instance Show PInt where show :: PInt -> String
                         show (PInt int) = show int
instance Semigroup PInt where
  (<>) :: PInt -> PInt -> PInt
  (<>) = (+)
instance Monoid PInt where
  mempty :: PInt
  mempty = PInt 0


-- ----------------------- Unit Test Suit -----------------------

-- Some Definitions

(=.) :: ToSynComps n => a -> n -> (a, [SynComp (V n) (Acc n)])
v =. lst = (v, toSynComps lst)

infixl 3 =.

(*.) :: acc -> [v] -> SynComp v acc
c *. lst = SynComp (c, lst)

infixl 5 *.

class ToSynComps n where
  type V n
  type Acc n
  toSynComps :: n -> [SynComp (V n) (Acc n)]

instance ToSynComps (SynComp v acc) where
  type V (SynComp v acc) = v
  type Acc (SynComp v acc) = acc
  toSynComps :: SynComp v acc -> [SynComp v acc]
  toSynComps = (:[])

instance ToSynComps [SynComp v acc] where
  type V [SynComp v acc] = v
  type Acc [SynComp v acc] = acc
  toSynComps :: [SynComp v acc] -> [SynComp (V [SynComp v acc]) (Acc [SynComp v acc])]
  toSynComps = id

-- (+.) :: (ToSynComps n, ToSynComps m) => n -> m -> [SYn]
(+.) :: (Acc n1 ~ Acc n2, V n1 ~ V n2, ToSynComps n2, ToSynComps n1) =>
  n2 -> n1 -> [SynComp (V n2) (Acc n2)]
n +. m = toSynComps n ++ toSynComps m

infixl 4 +.


-- The test cases

-- >>> testSubstVar
-- Equation System: {
--   'x' = 
--       10 * ['b']
--     + 200 * ['y']
--   'y' = 
--       3 * []
-- }
testSubstVar :: EqSys Char PInt
testSubstVar = runIdentity $ substVar exampleEqSys subst
  where
    subst = return . \case
      'x' -> Right 'y'
      'a' -> Left $ PInt 10
      'y' -> Left $ PInt 100
      v   -> Right v

-- >>> exampleEqSys
-- Equation System: {
--   'x' = 
--       1 * ['a', 'b']
--     + 2 * ['x', 'y']
--   'y' = 
--       3 * []
-- }
exampleEqSys :: EqSys Char PInt
exampleEqSys = EqSys
  [ 'x' =. 1 *. "ab" +. 2 *. "xy"
  , 'y' =. 3 *. "" ]

exampleTestRmDup :: EqSys Char PInt
exampleTestRmDup = EqSys
  [ 'a' =. 1 *. "ab"
  , 'b' =. 1 *. "ab" ]

newtype EnumRes t = EnumRes [(Int, Either NoStrError [t])]

instance Show t => Show (EnumRes t) where
  show :: Show t => EnumRes t -> String
  show (EnumRes lst) =
    lst
    |> fmap (\ (idx, res) ->
        show idx ++ " : " ++
        case res of
          Left _ -> "No String."
          Right nss -> unwords $ fmap show nss)
    |> unlines

-- -- >>> testEnumExample (toNStringMCFG exampleCOPY) [0..10]
-- -- 0 : 
-- -- 1 : a a
-- -- 2 : b b
-- -- 3 : a a a a
-- -- 4 : b a b a
-- -- 5 : a b a b
-- -- 6 : b b b b
-- -- 7 : a a a a a a
-- -- 8 : b a a b a a
-- -- 9 : a b a a b a
-- -- 10 : b b a b b a
-- testEnumExample :: (Ord nt, Show nt, Show t, Show v) =>
--   MultiCtxFreeGrammar nt t v -> [Int] -> EnumRes t
-- testEnumExample example query =
--   enumStrings example query
--   |> zip query
--   |> EnumRes

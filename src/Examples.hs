{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}
{-# HLINT ignore "Use <$>" #-}
module Examples (
  toNStringMCFG,
  exampleCOPY,
  exampleRtsaCOPY,
  numberExtRtsa,
  numberRtsa,
  simplifiedExampleRtsaCOPY,
  backToExampleCOPY
) where
import Parser ()
import Objects (mapMCFG, ExtendedRTSA, SpUnit (SpUnit), MultiCtxFreeGrammar, mapAut, RestrictedTreeStackAut, mapExtRtsa)
import Utils (NString(NString), stAutoNumber)
import GrammarToAut ( LocMem, StackSym, State, mcfgToRtsa )
import Control.Monad.Identity (Identity(runIdentity))
import Data.Hashable
import Control.Monad.ST.Strict
import EqSysBuild.MultiCFG (rTSAToMultiCFG, NonTer, Var)

{-
This file defines some supportive functions to help construct
the MCFG and rTSA from codes.

It also provides some concrete examples like O2 and MIX3.
-}

-- | An auxiliary function for better printing look
toNStringMCFG ::
  MultiCtxFreeGrammar String String String
  -> MultiCtxFreeGrammar NString NString NString
toNStringMCFG = runIdentity . mapMCFG nString nString nString
  where nString = return . NString

-- >>> toNStringMCFG exampleCOPY
-- MCFG {
--   Rules: [
--     D (, ) <- .
--     D (`b` x, `b` y) <- D (x, y).
--     D (`a` x, `a` y) <- D (x, y).
--     S (x y) <- D (x, y).
--   ]
--   Starting Non-Terminal: S
-- }
exampleCOPY :: MultiCtxFreeGrammar String String String
exampleCOPY = read $ concat
  [ "S (x y) <- D (x, y)."
  , "D (a x, a y) <- D (x, y)."
  , "D (b x, b y) <- D (x, y)."
  , "D (, ) <- ."
  ]

-- >>> exampleRtsaCOPY
exampleRtsaCOPY :: IO
  (ExtendedRTSA
     (State String)
     (LocMem String String String)
     (StackSym String)
     [String]
     SpUnit)
exampleRtsaCOPY = mcfgToRtsa exampleCOPY

numberRtsa ::
  (Hashable q, Hashable m, Hashable g, Ord info, Ord (sp Int Int Int)) =>((q -> ST s Int)
    -> (m -> ST s Int)
    -> (g -> ST s Int)
    -> sp q m g
    -> ST s (sp Int Int Int))
  -> RestrictedTreeStackAut q m g info sp
  -> ST s (RestrictedTreeStackAut Int Int Int info sp)
numberRtsa spMap rtsa = do
  qF <- stAutoNumber
  mF <- stAutoNumber
  gF <- stAutoNumber
  mapAut qF mF gF return (spMap qF mF gF) rtsa

numberExtRtsa ::
  (Hashable q, Hashable m, Hashable g, Ord info, Ord (sp Int Int Int)) =>((q -> ST s Int)
    -> (m -> ST s Int)
    -> (g -> ST s Int)
    -> sp q m g
    -> ST s (sp Int Int Int))
  -> ExtendedRTSA q m g info sp
  -> ST s (ExtendedRTSA Int Int Int info sp)
numberExtRtsa spMap er = do
  qF <- stAutoNumber
  mF <- stAutoNumber
  gF <- stAutoNumber
  mapExtRtsa qF mF gF return (spMap qF mF gF) er

-- >>> simplifiedExampleRtsaCOPY
-- Extended rTSA: {
--   rTSA: {
--     k = 2,
--     q0 = 0,
--     m0 = 0,
--     rules = [
--       (0, 0, \bot) -([])-> (0, 0, Up 0)
--       (0, 0, G(0)) -([])-> (0, 4, Up 1)
--       (0, 0, G(1)) -([])-> (1, 1, Down)
--       (0, 0, G(1)) -(["a"])-> (0, 2, Up 1)
--       (0, 0, G(1)) -(["b"])-> (0, 3, Up 1)
--       (0, 1, G(1)) -([])-> (1, 1, Down)
--       (0, 2, G(1)) -(["a"])-> (0, 2, Up 1)
--       (0, 3, G(1)) -(["b"])-> (0, 3, Up 1)
--       (0, 4, G(0)) -([])-> (0, 4, Up 1)
--       (1, 2, G(1)) -([])-> (1, 2, Down)
--       (1, 3, G(1)) -([])-> (1, 3, Down)
--       (1, 4, G(0)) -([])-> (2, 4, Up 1)
--       (2, 0, G(1)) -([])-> (3, 1, Down)
--       (2, 0, G(1)) -(["a"])-> (2, 2, Up 1)
--       (2, 0, G(1)) -(["b"])-> (2, 3, Up 1)
--       (2, 1, G(1)) -([])-> (3, 1, Down)
--       (2, 2, G(1)) -(["a"])-> (2, 2, Up 1)
--       (2, 3, G(1)) -(["b"])-> (2, 3, Up 1)
--       (3, 2, G(1)) -([])-> (3, 2, Down)
--       (3, 3, G(1)) -([])-> (3, 3, Down)
--       (3, 4, G(0)) -([])-> (4, 4, Down)
--       (4, 0, \bot) -([])-> (0, 0, Down)
--     ]
--   }
-- ,
--   k map: {
--     0 |-> 1
--     1 |-> 2
--   },
--   down map: {
--     (0,0) |-> [4]
--     (0,1) |-> [1]
--     (2,1) |-> [3]
--   }
-- }
simplifiedExampleRtsaCOPY :: IO (ExtendedRTSA Int Int Int [String] SpUnit)
simplifiedExampleRtsaCOPY = do
  ret <- exampleRtsaCOPY
  return $ runST $ numberExtRtsa spMap ret
  where
    spMap _ _ _ _ = return SpUnit

backToExampleCOPY :: IO
  (MultiCtxFreeGrammar
     (NonTer Int Int)
     String
     (Var Int))
backToExampleCOPY = simplifiedExampleRtsaCOPY >>= rTSAToMultiCFG


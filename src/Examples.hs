{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}
{-# HLINT ignore "Use <$>" #-}
{-# LANGUAGE LambdaCase #-}
{-# OPTIONS_GHC -Wno-name-shadowing #-}
module Examples (
  toNStringMCFG,
  exampleCOPY,
  exampleRtsaCOPY,
  numberExtRtsa,
  numberRtsa,
  simplifiedExampleRtsaCOPY,
  backToExampleCOPY,
  exampleABCn,
  exampleRtsaABCn,
  backToExampleABCn,
  exampleTripleDyck,
  exampleRtsaTripleDyck,
  backToExampleTripleDyck,
  exampleO2,
  exampleMIX3
) where
import Parser ()
import Objects (mapMCFG, SpUnit (SpUnit), MultiCtxFreeGrammar (mcfgStartNonTer, MultiCtxFreeGrammar), mapAut, RestrictedTreeStackAut, mapExtRtsa, ExtendedRTSA (..), CheckValid (isValid))
import Utils (NString(NString), stAutoNumber, ioAutoNumber, quoteBy)
import GrammarToAut ( LocMem, StackSym, State, mcfgToRtsa )
import Control.Monad.Identity (Identity(runIdentity, Identity))
import Data.Hashable ( Hashable )
import Control.Monad.ST.Strict ( ST, runST )
import EqSysBuild.MultiCFG (rTSAToMultiCFG, NonTer, Var (..))
import AutOp (FiniteStateAut(FiniteStateAut), ReadFSA, extIntersectReg, extStringHomo)
import qualified Data.Set as S
import qualified Data.Map.Strict as M

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
  (Hashable q, Hashable m, Hashable g, Ord info, Ord (sp Int Int Int)) =>
  ((q -> ST s Int)
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
--       (0, 0, \bot) -([])-> (0, 0, Up 0),
--       (0, 0, G(0)) -([])-> (0, 4, Up 1),
--       (0, 0, G(1)) -([])-> (1, 1, Down),
--       (0, 0, G(1)) -(["a"])-> (0, 2, Up 1),
--       (0, 0, G(1)) -(["b"])-> (0, 3, Up 1),
--       (0, 1, G(1)) -([])-> (1, 1, Down),
--       (0, 2, G(1)) -(["a"])-> (0, 2, Up 1),
--       (0, 3, G(1)) -(["b"])-> (0, 3, Up 1),
--       (0, 4, G(0)) -([])-> (0, 4, Up 1),
--       (1, 2, G(1)) -([])-> (1, 2, Down),
--       (1, 3, G(1)) -([])-> (1, 3, Down),
--       (1, 4, G(0)) -([])-> (2, 4, Up 1),
--       (2, 0, G(1)) -([])-> (3, 1, Down),
--       (2, 0, G(1)) -(["a"])-> (2, 2, Up 1),
--       (2, 0, G(1)) -(["b"])-> (2, 3, Up 1),
--       (2, 1, G(1)) -([])-> (3, 1, Down),
--       (2, 2, G(1)) -(["a"])-> (2, 2, Up 1),
--       (2, 3, G(1)) -(["b"])-> (2, 3, Up 1),
--       (3, 2, G(1)) -([])-> (3, 2, Down),
--       (3, 3, G(1)) -([])-> (3, 3, Down),
--       (3, 4, G(0)) -([])-> (4, 4, Down),
--       (4, 0, \bot) -([])-> (0, 0, Down),
--     ]
--   },
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
simplifiedExampleRtsaCOPY = toSimpExampleRtsa exampleCOPY

toSimpExampleRtsa ::
  (Hashable nt, Ord nt, Ord v, Hashable v) =>
  MultiCtxFreeGrammar nt String v
  -> IO (ExtendedRTSA Int Int Int [String] SpUnit)
toSimpExampleRtsa mcfg = do
  ret <- mcfgToRtsa mcfg
  return $ runST $ numberExtRtsa spMap ret
  where
    spMap _ _ _ _ = return SpUnit

-- >>> backToExampleCOPY
-- MCFG {
--   Rules: [
--     AbsVar 1 [0] \bot (v@(0,0)) <- AbsVar 2 [0,4] G(0) (v@(0,0)).
--     AbsVar 2 [0,4] G(0) (v@(1,0) v@(1,1)) <- 
--          AbsVar 4 [0,1,2,3] G(1) (v@(1,0), v@(1,1)).
--     AbsVar 4 [0,1,2,3] G(1) (, ) <- .
--     AbsVar 4 [0,1,2,3] G(1) (`a` v@(1,0), `a` v@(1,1)) <- 
--          AbsVar 4 [0,1,2,3] G(1) (v@(1,0), v@(1,1)).
--     AbsVar 4 [0,1,2,3] G(1) (`b` v@(1,0), `b` v@(1,1)) <- 
--          AbsVar 4 [0,1,2,3] G(1) (v@(1,0), v@(1,1)).
--   ],
--   Starting Non-Terminal: AbsVar 1 [0] \bot
-- }
backToExampleCOPY :: IO
  (MultiCtxFreeGrammar
     (NonTer Int Int)
     NString
     (Var Int))
backToExampleCOPY = do
  ext <- simplifiedExampleRtsaCOPY
  -- To test the auto-generated stuff.
  ret <- rTSAToMultiCFG $ ext { eRtsaDownMap = Nothing, eRtsaKMap = Nothing }
  mapMCFG return (return . NString) return ret


-- >>> toNStringMCFG exampleABCn
-- MCFG {
--   Rules: [
--     A (, , ) <- .
--     A (`a` x, `b` y, `c` z) <- A (x, y, z).
--     S (x y z) <- A (x, y, z).
--   ],
--   Starting Non-Terminal: S
-- }
exampleABCn :: MultiCtxFreeGrammar String String String
exampleABCn = read $ unlines
  [ "S (x y z) <- A (x, y, z)."
  , "A (a x, b y, c z) <- A (x, y, z)."
  , "A (,,) <- ." ]

-- >>> exampleRtsaABCn
-- Extended rTSA: {
--   rTSA: {
--     k = 3,
--     q0 = 0,
--     m0 = 0,
--     rules = [
--       (0, 0, \bot) -([])-> (0, 0, Up 0),
--       (0, 0, G(0)) -([])-> (0, 3, Up 1),
--       (0, 0, G(1)) -([])-> (1, 1, Down),
--       (0, 0, G(1)) -(["a"])-> (0, 2, Up 1),
--       (0, 1, G(1)) -([])-> (1, 1, Down),
--       (0, 2, G(1)) -(["a"])-> (0, 2, Up 1),
--       (0, 3, G(0)) -([])-> (0, 3, Up 1),
--       (1, 2, G(1)) -([])-> (1, 2, Down),
--       (1, 3, G(0)) -([])-> (2, 3, Up 1),
--       (2, 0, G(1)) -([])-> (3, 1, Down),
--       (2, 0, G(1)) -(["b"])-> (2, 2, Up 1),
--       (2, 1, G(1)) -([])-> (3, 1, Down),
--       (2, 2, G(1)) -(["b"])-> (2, 2, Up 1),
--       (3, 2, G(1)) -([])-> (3, 2, Down),
--       (3, 3, G(0)) -([])-> (4, 3, Up 1),
--       (4, 0, G(1)) -([])-> (5, 1, Down),
--       (4, 0, G(1)) -(["c"])-> (4, 2, Up 1),
--       (4, 1, G(1)) -([])-> (5, 1, Down),
--       (4, 2, G(1)) -(["c"])-> (4, 2, Up 1),
--       (5, 2, G(1)) -([])-> (5, 2, Down),
--       (5, 3, G(0)) -([])-> (6, 3, Down),
--       (6, 0, \bot) -([])-> (0, 0, Down),
--     ]
--   },
--   k map: {
--     0 |-> 1
--     1 |-> 3
--   },
--   down map: {
--     (0,0) |-> [6]
--     (0,1) |-> [1]
--     (2,1) |-> [3]
--     (4,1) |-> [5]
--   }
-- }
exampleRtsaABCn :: IO (ExtendedRTSA Int Int Int [String] SpUnit)
exampleRtsaABCn = toSimpExampleRtsa exampleABCn

-- >>> backToExampleABCn
-- MCFG {
--   Rules: [
--     AbsVar 1 [0] \bot (v@(0,0)) <- AbsVar 2 [0,6] G(0) (v@(0,0)).
--     AbsVar 2 [0,6] G(0) (v@(1,0) v@(1,1) v@(1,2)) <- 
--          AbsVar 6 [0,1,2,3,4,5] G(1) (v@(1,0), v@(1,1), v@(1,2)).
--     AbsVar 6 [0,1,2,3,4,5] G(1) (, , ) <- .
--     AbsVar 6 [0,1,2,3,4,5] G(1) (`a` v@(1,0), `b` v@(1,1), `c` v@(1,2)) <- 
--          AbsVar 6 [0,1,2,3,4,5] G(1) (v@(1,0), v@(1,1), v@(1,2)).
--   ],
--   Starting Non-Terminal: AbsVar 1 [0] \bot
-- }
backToExampleABCn :: IO (MultiCtxFreeGrammar (NonTer Int Int) NString (Var Int))
backToExampleABCn = do
  ret <- exampleRtsaABCn >>= rTSAToMultiCFG
  mapMCFG return (return . NString) return ret

-- >>> toNStringMCFG exampleTripleDyck
-- MCFG {
--   Rules: [
--     F (, , ) <- .
--     F (`[` x `]` x', `[` y `]` y', `[` z `]` z') <- F (x, y, z), F (x', y', z').
--     S (x `#` y `#` z) <- F (x, y, z).
--   ],
--   Starting Non-Terminal: S
-- }
exampleTripleDyck :: MultiCtxFreeGrammar String String String
exampleTripleDyck = read $ concat
  [ "S (x `#` y `#` z) <- F (x, y, z)."
  , "F (`[` x `]` x', `[` y `]` y', `[` z `]` z') <- F (x, y, z), F (x', y', z')."
  , "F (,,) <- ." ]

-- >>> exampleRtsaTripleDyck
-- Extended rTSA: {
--   rTSA: {
--     k = 3,
--     q0 = 0,
--     m0 = 0,
--     rules = [
--       (0, 0, \bot) -([])-> (0, 0, Up 0),
--       (0, 0, G(0)) -([])-> (0, 3, Up 1),
--       (0, 0, G(1)) -([])-> (1, 1, Down),
--       (0, 0, G(1)) -(["["])-> (0, 2, Up 1),
--       (0, 0, G(2)) -([])-> (2, 1, Down),
--       (0, 0, G(2)) -(["["])-> (0, 2, Up 1),
--       (0, 1, G(1)) -([])-> (1, 1, Down),
--       (0, 1, G(2)) -([])-> (2, 1, Down),
--       (0, 2, G(1)) -(["["])-> (0, 2, Up 1),
--       (0, 2, G(2)) -(["["])-> (0, 2, Up 1),
--       (0, 3, G(0)) -([])-> (0, 3, Up 1),
--       (1, 2, G(1)) -(["]"])-> (0, 2, Up 2),
--       (1, 2, G(2)) -(["]"])-> (0, 2, Up 2),
--       (1, 3, G(0)) -(["#"])-> (3, 3, Up 1),
--       (2, 2, G(1)) -([])-> (1, 2, Down),
--       (2, 2, G(2)) -([])-> (2, 2, Down),
--       (3, 0, G(1)) -([])-> (4, 1, Down),
--       (3, 0, G(1)) -(["["])-> (3, 2, Up 1),
--       (3, 0, G(2)) -([])-> (5, 1, Down),
--       (3, 0, G(2)) -(["["])-> (3, 2, Up 1),
--       (3, 1, G(1)) -([])-> (4, 1, Down),
--       (3, 1, G(2)) -([])-> (5, 1, Down),
--       (3, 2, G(1)) -(["["])-> (3, 2, Up 1),
--       (3, 2, G(2)) -(["["])-> (3, 2, Up 1),
--       (4, 2, G(1)) -(["]"])-> (3, 2, Up 2),
--       (4, 2, G(2)) -(["]"])-> (3, 2, Up 2),
--       (4, 3, G(0)) -(["#"])-> (6, 3, Up 1),
--       (5, 2, G(1)) -([])-> (4, 2, Down),
--       (5, 2, G(2)) -([])-> (5, 2, Down),
--       (6, 0, G(1)) -([])-> (7, 1, Down),
--       (6, 0, G(1)) -(["["])-> (6, 2, Up 1),
--       (6, 0, G(2)) -([])-> (8, 1, Down),
--       (6, 0, G(2)) -(["["])-> (6, 2, Up 1),
--       (6, 1, G(1)) -([])-> (7, 1, Down),
--       (6, 1, G(2)) -([])-> (8, 1, Down),
--       (6, 2, G(1)) -(["["])-> (6, 2, Up 1),
--       (6, 2, G(2)) -(["["])-> (6, 2, Up 1),
--       (7, 2, G(1)) -(["]"])-> (6, 2, Up 2),
--       (7, 2, G(2)) -(["]"])-> (6, 2, Up 2),
--       (7, 3, G(0)) -([])-> (9, 3, Down),
--       (8, 2, G(1)) -([])-> (7, 2, Down),
--       (8, 2, G(2)) -([])-> (8, 2, Down),
--       (9, 0, \bot) -([])-> (0, 0, Down),
--     ]
--   },
--   k map: {
--     0 |-> 1
--     1 |-> 3
--     2 |-> 3
--   },
--   down map: {
--     (0,0) |-> [9]
--     (0,1) |-> [1]
--     (0,2) |-> [2]
--     (3,1) |-> [4]
--     (3,2) |-> [5]
--     (6,1) |-> [7]
--     (6,2) |-> [8]
--   }
-- }
exampleRtsaTripleDyck :: IO (ExtendedRTSA Int Int Int [String] SpUnit)
exampleRtsaTripleDyck = toSimpExampleRtsa exampleTripleDyck

-- >>> backToExampleTripleDyck
backToExampleTripleDyck :: IO (MultiCtxFreeGrammar (NonTer Int Int) NString (Var Int))
backToExampleTripleDyck = do
  ret <- exampleRtsaTripleDyck >>= rTSAToMultiCFG
  mapMCFG return (return . NString) return ret

-- >>> toNStringMCFG exampleO2
-- MCFG {
--   Rules: [
--     Inv (x1, `oa2` x2 `a2`) <- Inv (x1, x2).
--     Inv (x1 `oa2`, x2 `a2`) <- Inv (x1, x2).
--     Inv (x1 `oa2`, `a2` x2) <- Inv (x1, x2).
--     Inv (`oa2` x1, x2 `a2`) <- Inv (x1, x2).
--     Inv (`oa2` x1, `a2` x2) <- Inv (x1, x2).
--     Inv (`oa2` x1 `a2`, x2) <- Inv (x1, x2).
--     Inv (x1, `oa1` x2 `a1`) <- Inv (x1, x2).
--     Inv (x1 `oa1`, x2 `a1`) <- Inv (x1, x2).
--     Inv (x1 `oa1`, `a1` x2) <- Inv (x1, x2).
--     Inv (`oa1` x1, x2 `a1`) <- Inv (x1, x2).
--     Inv (`oa1` x1, `a1` x2) <- Inv (x1, x2).
--     Inv (`oa1` x1 `a1`, x2) <- Inv (x1, x2).
--     Inv (x1, `a2` x2 `oa2`) <- Inv (x1, x2).
--     Inv (x1 `a2`, x2 `oa2`) <- Inv (x1, x2).
--     Inv (x1 `a2`, `oa2` x2) <- Inv (x1, x2).
--     Inv (`a2` x1, x2 `oa2`) <- Inv (x1, x2).
--     Inv (`a2` x1, `oa2` x2) <- Inv (x1, x2).
--     Inv (`a2` x1 `oa2`, x2) <- Inv (x1, x2).
--     Inv (x1, `a1` x2 `oa1`) <- Inv (x1, x2).
--     Inv (x1 `a1`, x2 `oa1`) <- Inv (x1, x2).
--     Inv (x1 `a1`, `oa1` x2) <- Inv (x1, x2).
--     Inv (`a1` x1, x2 `oa1`) <- Inv (x1, x2).
--     Inv (`a1` x1, `oa1` x2) <- Inv (x1, x2).
--     Inv (`a1` x1 `oa1`, x2) <- Inv (x1, x2).
--     Inv (, ) <- .
--     Inv (, x1 y1 x2 y2) <- Inv (x1, x2), Inv (y1, y2).
--     Inv (x1, y1 x2 y2) <- Inv (x1, x2), Inv (y1, y2).
--     Inv (x1 y1, x2 y2) <- Inv (x1, x2), Inv (y1, y2).
--     Inv (x1 y1 x2, y2) <- Inv (x1, x2), Inv (y1, y2).
--     Inv (x1 y1 x2 y2, ) <- Inv (x1, x2), Inv (y1, y2).
--     S (x y) <- Inv (x, y).
--   ],
--   Starting Non-Terminal: S
-- }
exampleO2 :: MultiCtxFreeGrammar String String String
exampleO2 = read $ concat $
  [ "S (x y) <- Inv (x, y)."
  , "Inv (x1 y1 x2 y2, ) <- Inv (x1, x2), Inv (y1, y2)."
  , "Inv (x1 y1 x2, y2 ) <- Inv (x1, x2), Inv (y1, y2)."
  , "Inv (x1 y1, x2 y2 ) <- Inv (x1, x2), Inv (y1, y2)."
  , "Inv (x1, y1 x2 y2 ) <- Inv (x1, x2), Inv (y1, y2)."
  , "Inv (, x1 y1 x2 y2) <- Inv (x1, x2), Inv (y1, y2)."
  , "Inv (,) <- ."
  ] ++ moreRules
  where
    moreRules = do
      k <- [ "a1", "a2", "oa1", "oa2" ]
      let cK = case k of
                "a1" -> "oa1"
                "a2" -> "oa2"
                "oa1" -> "a1"
                "oa2" -> "a2"
                _ -> error "IMPOSSIBLE"
      [   "Inv (" ++ k ++ " x1 " ++ cK ++ ", x2) <- Inv (x1, x2)."
        , "Inv (" ++ k ++ " x1, " ++ cK ++ " x2) <- Inv (x1, x2)."
        , "Inv (" ++ k ++ " x1, x2 " ++ cK ++ ") <- Inv (x1, x2)."
        , "Inv (x1 " ++ k ++ ", " ++ cK ++ " x2) <- Inv (x1, x2)."
        , "Inv (x1 " ++ k ++ ", x2 " ++ cK ++ ") <- Inv (x1, x2)."
        , "Inv (x1, " ++ k ++ " x2 " ++ cK ++ ") <- Inv (x1, x2)."
        ]

pureABCLanguage :: ReadFSA Int String
pureABCLanguage = FiniteStateAut rules (S.fromList [1]) 1
  where
    rules = M.fromList
      [ 1 -| "a1" |-> 1
      , 1 -| "a2" |-> 1
      , 1 -| "oa1" |-> 2
      , 2 -| "oa2" |-> 1 ]

infix 3 -|
infix 2 |->

(-|) :: a -> b -> (a, b)
st -| v = (st, v)

(|->) :: a1 -> a2 -> (a1, Identity a2)
p |-> st = (p, Identity st)

-- >>> exampleMIX3
-- MCFG {
--   Rules: [
--     F (x0 x1) <- F8 (x0, x1).
--     F (x0 x1) <- F1 (x0, x1).
--     F1 (`C` x0 `A`, x1) <- F2 (x0, x1).
--     F1 (`C` x0, x1 `A`) <- F2 (x0, x1).
--     F1 (`C` x0, `A` x1) <- F2 (x0, x1).
--     F1 (`B` x0, x1) <- F3 (x0, x1).
--     F1 (`B` x0, x1) <- F4 (x0, x1).
--     F1 (`A` x0, `C` x1) <- F5 (x0, x1).
--     F1 (, x0 y0 x1 y1) <- F6 (x0, x1), F7 (y0, y1).
--     F1 (, x0 y0 x1 y1) <- F8 (x0, x1), F9 (y0, y1).
--     F1 (, x0 y0 x1 y1) <- F10 (x0, x1), F11 (y0, y1).
--     F1 (, x0 y0 x1 y1) <- F3 (x0, x1), F2 (y0, y1).
--     F1 (, x0 y0 x1 y1) <- F12 (x0, x1), F8 (y0, y1).
--     F1 (, x0 y0 x1 y1) <- F5 (x0, x1), F3 (y0, y1).
--     F1 (, x0 y0 x1 y1) <- F4 (x0, x1), F5 (y0, y1).
--     F1 (, x0 y0 x1 y1) <- F1 (x0, x1), F1 (y0, y1).
--     F1 (, ) <- .
--     F1 (x0 y0 x1 y1, ) <- F6 (x0, x1), F7 (y0, y1).
--     F1 (x0 y0 x1 y1, ) <- F8 (x0, x1), F9 (y0, y1).
--     F1 (x0 y0 x1 y1, ) <- F10 (x0, x1), F11 (y0, y1).
--     F1 (x0 y0 x1 y1, ) <- F3 (x0, x1), F2 (y0, y1).
--     F1 (x0 y0 x1 y1, ) <- F12 (x0, x1), F8 (y0, y1).
--     F1 (x0 y0 x1 y1, ) <- F5 (x0, x1), F3 (y0, y1).
--     F1 (x0 y0 x1 y1, ) <- F4 (x0, x1), F5 (y0, y1).
--     F1 (x0 y0 x1 y1, ) <- F1 (x0, x1), F1 (y0, y1).
--     F1 (x0 y0 x1, y1) <- F8 (x0, x1), F9 (y0, y1).
--     F1 (x0 y0 x1, y1) <- F3 (x0, x1), F2 (y0, y1).
--     F1 (x0 y0 x1, y1) <- F5 (x0, x1), F3 (y0, y1).
--     F1 (x0 y0 x1, y1) <- F1 (x0, x1), F1 (y0, y1).
--     F1 (x0 y0, x1 y1) <- F10 (x0, x1), F11 (y0, y1).
--     F1 (x0 y0, x1 y1) <- F3 (x0, x1), F2 (y0, y1).
--     F1 (x0 y0, x1 y1) <- F4 (x0, x1), F5 (y0, y1).
--     F1 (x0 y0, x1 y1) <- F1 (x0, x1), F1 (y0, y1).
--     F1 (x0, x1 `B`) <- F3 (x0, x1).
--     F1 (x0, `B` x1) <- F3 (x0, x1).
--     F1 (x0 `B`, x1) <- F4 (x0, x1).
--     F1 (x0 `A`, `C` x1) <- F5 (x0, x1).
--     F1 (x0, y0 x1 y1) <- F12 (x0, x1), F8 (y0, y1).
--     F1 (x0, y0 x1 y1) <- F5 (x0, x1), F3 (y0, y1).
--     F1 (x0, y0 x1 y1) <- F4 (x0, x1), F5 (y0, y1).
--     F1 (x0, y0 x1 y1) <- F1 (x0, x1), F1 (y0, y1).
--     F1 (x0, `C` x1 `A`) <- F5 (x0, x1).
--     F1 (x0, `B` x1) <- F4 (x0, x1).
--     F10 (`C` x0, `A` x1) <- F15 (x0, x1).
--     F10 (`A` x0 `C`, x1) <- F4 (x0, x1).
--     F10 (`A` x0, x1 `C`) <- F3 (x0, x1).
--     F10 (`A` x0, `C` x1) <- F6 (x0, x1).
--     F10 (x0 y0 x1, y1) <- F6 (x0, x1), F15 (y0, y1).
--     F10 (x0 y0 x1, y1) <- F10 (x0, x1), F13 (y0, y1).
--     F10 (x0 y0 x1, y1) <- F12 (x0, x1), F10 (y0, y1).
--     F10 (x0 y0 x1, y1) <- F4 (x0, x1), F4 (y0, y1).
--     F10 (x0 y0, x1 y1) <- F10 (x0, x1), F14 (y0, y1).
--     F10 (x0 y0, x1 y1) <- F3 (x0, x1), F15 (y0, y1).
--     F10 (x0 y0, x1 y1) <- F4 (x0, x1), F6 (y0, y1).
--     F10 (x0 y0, x1 y1) <- F1 (x0, x1), F10 (y0, y1).
--     F10 (x0 `C`, `A` x1) <- F4 (x0, x1).
--     F10 (x0, y0 x1 y1) <- F6 (x0, x1), F6 (y0, y1).
--     F10 (x0, y0 x1 y1) <- F8 (x0, x1), F10 (y0, y1).
--     F10 (x0, y0 x1 y1) <- F10 (x0, x1), F12 (y0, y1).
--     F10 (x0, y0 x1 y1) <- F3 (x0, x1), F4 (y0, y1).
--     F10 (x0, `A` x1 `C`) <- F3 (x0, x1).
--     F11 (x0 y0 x1, y1) <- F7 (x0, x1), F7 (y0, y1).
--     F11 (x0 y0 x1, y1) <- F9 (x0, x1), F11 (y0, y1).
--     F11 (x0 y0 x1, y1) <- F11 (x0, x1), F8 (y0, y1).
--     F11 (x0 y0 x1, y1) <- F2 (x0, x1), F5 (y0, y1).
--     F11 (x0 y0, x1 y1) <- F14 (x0, x1), F11 (y0, y1).
--     F11 (x0 y0, x1 y1) <- F7 (x0, x1), F2 (y0, y1).
--     F11 (x0 y0, x1 y1) <- F16 (x0, x1), F5 (y0, y1).
--     F11 (x0 y0, x1 y1) <- F11 (x0, x1), F1 (y0, y1).
--     F11 (x0, x1 `B`) <- F7 (x0, x1).
--     F11 (x0 `B`, x1) <- F16 (x0, x1).
--     F11 (x0 `B`, x1) <- F2 (x0, x1).
--     F11 (x0, y0 x1 y1) <- F16 (x0, x1), F7 (y0, y1).
--     F11 (x0, y0 x1 y1) <- F11 (x0, x1), F9 (y0, y1).
--     F11 (x0, y0 x1 y1) <- F13 (x0, x1), F11 (y0, y1).
--     F11 (x0, y0 x1 y1) <- F2 (x0, x1), F2 (y0, y1).
--     F11 (x0, x1 `B`) <- F2 (x0, x1).
--     F11 (x0 `B`, x1) <- F5 (x0, x1).
--     F11 (x0, x1 `B`) <- F5 (x0, x1).
--     F12 (`C` x0 `A`, x1) <- F16 (x0, x1).
--     F12 (`B` x0, x1) <- F6 (x0, x1).
--     F12 (`B` x0, x1) <- F4 (x0, x1).
--     F12 (`A` x0, x1 `C`) <- F5 (x0, x1).
--     F12 (, x0 y0 x1 y1) <- F14 (x0, x1), F14 (y0, y1).
--     F12 (, x0 y0 x1 y1) <- F7 (x0, x1), F15 (y0, y1).
--     F12 (, x0 y0 x1 y1) <- F15 (x0, x1), F16 (y0, y1).
--     F12 (, x0 y0 x1 y1) <- F9 (x0, x1), F13 (y0, y1).
--     F12 (, x0 y0 x1 y1) <- F16 (x0, x1), F6 (y0, y1).
--     F12 (, x0 y0 x1 y1) <- F11 (x0, x1), F10 (y0, y1).
--     F12 (, x0 y0 x1 y1) <- F13 (x0, x1), F12 (y0, y1).
--     F12 (, x0 y0 x1 y1) <- F2 (x0, x1), F4 (y0, y1).
--     F12 (, ) <- .
--     F12 (x0 y0 x1 y1, ) <- F6 (x0, x1), F7 (y0, y1).
--     F12 (x0 y0 x1 y1, ) <- F8 (x0, x1), F9 (y0, y1).
--     F12 (x0 y0 x1 y1, ) <- F10 (x0, x1), F11 (y0, y1).
--     F12 (x0 y0 x1 y1, ) <- F3 (x0, x1), F2 (y0, y1).
--     F12 (x0 y0 x1 y1, ) <- F12 (x0, x1), F8 (y0, y1).
--     F12 (x0 y0 x1 y1, ) <- F5 (x0, x1), F3 (y0, y1).
--     F12 (x0 y0 x1 y1, ) <- F4 (x0, x1), F5 (y0, y1).
--     F12 (x0 y0 x1 y1, ) <- F1 (x0, x1), F1 (y0, y1).
--     F12 (x0 y0 x1, y1) <- F8 (x0, x1), F14 (y0, y1).
--     F12 (x0 y0 x1, y1) <- F3 (x0, x1), F16 (y0, y1).
--     F12 (x0 y0 x1, y1) <- F5 (x0, x1), F6 (y0, y1).
--     F12 (x0 y0 x1, y1) <- F1 (x0, x1), F12 (y0, y1).
--     F12 (x0 y0, x1 y1) <- F6 (x0, x1), F16 (y0, y1).
--     F12 (x0 y0, x1 y1) <- F8 (x0, x1), F13 (y0, y1).
--     F12 (x0 y0, x1 y1) <- F12 (x0, x1), F12 (y0, y1).
--     F12 (x0 y0, x1 y1) <- F5 (x0, x1), F4 (y0, y1).
--     F12 (x0 `B`, x1) <- F4 (x0, x1).
--     F12 (x0 `A`, x1 `C`) <- F5 (x0, x1).
--     F12 (x0, y0 x1 y1) <- F12 (x0, x1), F14 (y0, y1).
--     F12 (x0, y0 x1 y1) <- F5 (x0, x1), F15 (y0, y1).
--     F12 (x0, y0 x1 y1) <- F4 (x0, x1), F16 (y0, y1).
--     F12 (x0, y0 x1 y1) <- F1 (x0, x1), F13 (y0, y1).
--     F13 (x0 y0 x1, y1) <- F7 (x0, x1), F15 (y0, y1).
--     F13 (x0 y0 x1, y1) <- F9 (x0, x1), F13 (y0, y1).
--     F13 (x0 y0 x1, y1) <- F11 (x0, x1), F10 (y0, y1).
--     F13 (x0 y0 x1, y1) <- F2 (x0, x1), F4 (y0, y1).
--     F13 (x0 y0, x1 y1) <- F15 (x0, x1), F16 (y0, y1).
--     F13 (x0 y0, x1 y1) <- F9 (x0, x1), F13 (y0, y1).
--     F13 (x0 y0, x1 y1) <- F13 (x0, x1), F12 (y0, y1).
--     F13 (x0 y0, x1 y1) <- F2 (x0, x1), F4 (y0, y1).
--     F13 (x0, `B` x1) <- F15 (x0, x1).
--     F13 (x0 `A`, x1 `C`) <- F2 (x0, x1).
--     F13 (x0 `A`, `C` x1) <- F16 (x0, x1).
--     F13 (x0, y0 x1 y1) <- F16 (x0, x1), F6 (y0, y1).
--     F13 (x0, y0 x1 y1) <- F11 (x0, x1), F10 (y0, y1).
--     F13 (x0, y0 x1 y1) <- F13 (x0, x1), F12 (y0, y1).
--     F13 (x0, y0 x1 y1) <- F2 (x0, x1), F4 (y0, y1).
--     F13 (x0, `A` x1 `C`) <- F2 (x0, x1).
--     F13 (x0 `B`, x1) <- F4 (x0, x1).
--     F13 (x0, `B` x1) <- F4 (x0, x1).
--     F14 (, x0 y0 x1 y1) <- F14 (x0, x1), F14 (y0, y1).
--     F14 (, x0 y0 x1 y1) <- F7 (x0, x1), F15 (y0, y1).
--     F14 (, x0 y0 x1 y1) <- F15 (x0, x1), F16 (y0, y1).
--     F14 (, x0 y0 x1 y1) <- F9 (x0, x1), F13 (y0, y1).
--     F14 (, x0 y0 x1 y1) <- F16 (x0, x1), F6 (y0, y1).
--     F14 (, x0 y0 x1 y1) <- F11 (x0, x1), F10 (y0, y1).
--     F14 (, x0 y0 x1 y1) <- F13 (x0, x1), F12 (y0, y1).
--     F14 (, x0 y0 x1 y1) <- F2 (x0, x1), F4 (y0, y1).
--     F14 (, ) <- .
--     F14 (x0 y0 x1 y1, ) <- F14 (x0, x1), F14 (y0, y1).
--     F14 (x0 y0 x1 y1, ) <- F7 (x0, x1), F15 (y0, y1).
--     F14 (x0 y0 x1 y1, ) <- F15 (x0, x1), F16 (y0, y1).
--     F14 (x0 y0 x1 y1, ) <- F9 (x0, x1), F13 (y0, y1).
--     F14 (x0 y0 x1 y1, ) <- F16 (x0, x1), F6 (y0, y1).
--     F14 (x0 y0 x1 y1, ) <- F11 (x0, x1), F10 (y0, y1).
--     F14 (x0 y0 x1 y1, ) <- F13 (x0, x1), F12 (y0, y1).
--     F14 (x0 y0 x1 y1, ) <- F2 (x0, x1), F4 (y0, y1).
--     F14 (x0 y0 x1, y1) <- F14 (x0, x1), F14 (y0, y1).
--     F14 (x0 y0 x1, y1) <- F15 (x0, x1), F16 (y0, y1).
--     F14 (x0 y0 x1, y1) <- F16 (x0, x1), F6 (y0, y1).
--     F14 (x0 y0 x1, y1) <- F13 (x0, x1), F12 (y0, y1).
--     F14 (x0 y0, x1 y1) <- F14 (x0, x1), F14 (y0, y1).
--     F14 (x0 y0, x1 y1) <- F7 (x0, x1), F15 (y0, y1).
--     F14 (x0 y0, x1 y1) <- F16 (x0, x1), F6 (y0, y1).
--     F14 (x0 y0, x1 y1) <- F11 (x0, x1), F10 (y0, y1).
--     F14 (x0, y0 x1 y1) <- F14 (x0, x1), F14 (y0, y1).
--     F14 (x0, y0 x1 y1) <- F7 (x0, x1), F15 (y0, y1).
--     F14 (x0, y0 x1 y1) <- F15 (x0, x1), F16 (y0, y1).
--     F14 (x0, y0 x1 y1) <- F9 (x0, x1), F13 (y0, y1).
--     F15 (, x0 y0 x1 y1) <- F6 (x0, x1), F14 (y0, y1).
--     F15 (, x0 y0 x1 y1) <- F8 (x0, x1), F15 (y0, y1).
--     F15 (, x0 y0 x1 y1) <- F10 (x0, x1), F16 (y0, y1).
--     F15 (, x0 y0 x1 y1) <- F3 (x0, x1), F13 (y0, y1).
--     F15 (, x0 y0 x1 y1) <- F12 (x0, x1), F6 (y0, y1).
--     F15 (, x0 y0 x1 y1) <- F5 (x0, x1), F10 (y0, y1).
--     F15 (, x0 y0 x1 y1) <- F4 (x0, x1), F12 (y0, y1).
--     F15 (, x0 y0 x1 y1) <- F1 (x0, x1), F4 (y0, y1).
--     F15 (x0 y0 x1, y1) <- F14 (x0, x1), F15 (y0, y1).
--     F15 (x0 y0 x1, y1) <- F15 (x0, x1), F13 (y0, y1).
--     F15 (x0 y0 x1, y1) <- F16 (x0, x1), F10 (y0, y1).
--     F15 (x0 y0 x1, y1) <- F13 (x0, x1), F4 (y0, y1).
--     F15 (x0 y0, x1 y1) <- F15 (x0, x1), F14 (y0, y1).
--     F15 (x0 y0, x1 y1) <- F9 (x0, x1), F15 (y0, y1).
--     F15 (x0 y0, x1 y1) <- F13 (x0, x1), F6 (y0, y1).
--     F15 (x0 y0, x1 y1) <- F2 (x0, x1), F10 (y0, y1).
--     F15 (x0 `C`, `A` x1) <- F13 (x0, x1).
--     F15 (x0, y0 x1 y1) <- F14 (x0, x1), F6 (y0, y1).
--     F15 (x0, y0 x1 y1) <- F7 (x0, x1), F10 (y0, y1).
--     F15 (x0, y0 x1 y1) <- F15 (x0, x1), F12 (y0, y1).
--     F15 (x0, y0 x1 y1) <- F9 (x0, x1), F4 (y0, y1).
--     F15 (x0, `A` x1 `C`) <- F9 (x0, x1).
--     F15 (x0, `B` x1) <- F10 (x0, x1).
--     F16 (x0 y0 x1 y1, ) <- F14 (x0, x1), F7 (y0, y1).
--     F16 (x0 y0 x1 y1, ) <- F7 (x0, x1), F9 (y0, y1).
--     F16 (x0 y0 x1 y1, ) <- F15 (x0, x1), F11 (y0, y1).
--     F16 (x0 y0 x1 y1, ) <- F9 (x0, x1), F2 (y0, y1).
--     F16 (x0 y0 x1 y1, ) <- F16 (x0, x1), F8 (y0, y1).
--     F16 (x0 y0 x1 y1, ) <- F11 (x0, x1), F3 (y0, y1).
--     F16 (x0 y0 x1 y1, ) <- F13 (x0, x1), F5 (y0, y1).
--     F16 (x0 y0 x1 y1, ) <- F2 (x0, x1), F1 (y0, y1).
--     F16 (x0 y0 x1, y1) <- F7 (x0, x1), F14 (y0, y1).
--     F16 (x0 y0 x1, y1) <- F9 (x0, x1), F16 (y0, y1).
--     F16 (x0 y0 x1, y1) <- F11 (x0, x1), F6 (y0, y1).
--     F16 (x0 y0 x1, y1) <- F2 (x0, x1), F12 (y0, y1).
--     F16 (x0 y0, x1 y1) <- F14 (x0, x1), F16 (y0, y1).
--     F16 (x0 y0, x1 y1) <- F7 (x0, x1), F13 (y0, y1).
--     F16 (x0 y0, x1 y1) <- F16 (x0, x1), F12 (y0, y1).
--     F16 (x0 y0, x1 y1) <- F11 (x0, x1), F4 (y0, y1).
--     F16 (x0 `B`, x1) <- F13 (x0, x1).
--     F16 (x0 `A`, x1 `C`) <- F11 (x0, x1).
--     F16 (x0, y0 x1 y1) <- F16 (x0, x1), F14 (y0, y1).
--     F16 (x0, y0 x1 y1) <- F11 (x0, x1), F15 (y0, y1).
--     F16 (x0, y0 x1 y1) <- F13 (x0, x1), F16 (y0, y1).
--     F16 (x0, y0 x1 y1) <- F2 (x0, x1), F13 (y0, y1).
--     F16 (x0 `B`, x1) <- F12 (x0, x1).
--     F2 (x0 y0 x1 y1, ) <- F14 (x0, x1), F7 (y0, y1).
--     F2 (x0 y0 x1 y1, ) <- F7 (x0, x1), F9 (y0, y1).
--     F2 (x0 y0 x1 y1, ) <- F15 (x0, x1), F11 (y0, y1).
--     F2 (x0 y0 x1 y1, ) <- F9 (x0, x1), F2 (y0, y1).
--     F2 (x0 y0 x1 y1, ) <- F16 (x0, x1), F8 (y0, y1).
--     F2 (x0 y0 x1 y1, ) <- F11 (x0, x1), F3 (y0, y1).
--     F2 (x0 y0 x1 y1, ) <- F13 (x0, x1), F5 (y0, y1).
--     F2 (x0 y0 x1 y1, ) <- F2 (x0, x1), F1 (y0, y1).
--     F2 (x0 y0 x1, y1) <- F7 (x0, x1), F9 (y0, y1).
--     F2 (x0 y0 x1, y1) <- F9 (x0, x1), F2 (y0, y1).
--     F2 (x0 y0 x1, y1) <- F11 (x0, x1), F3 (y0, y1).
--     F2 (x0 y0 x1, y1) <- F2 (x0, x1), F1 (y0, y1).
--     F2 (x0 y0, x1 y1) <- F15 (x0, x1), F11 (y0, y1).
--     F2 (x0 y0, x1 y1) <- F9 (x0, x1), F2 (y0, y1).
--     F2 (x0 y0, x1 y1) <- F13 (x0, x1), F5 (y0, y1).
--     F2 (x0 y0, x1 y1) <- F2 (x0, x1), F1 (y0, y1).
--     F2 (x0, x1 `B`) <- F9 (x0, x1).
--     F2 (x0, `B` x1) <- F9 (x0, x1).
--     F2 (x0 `B`, x1) <- F13 (x0, x1).
--     F2 (x0 `A`, `C` x1) <- F11 (x0, x1).
--     F2 (x0, y0 x1 y1) <- F16 (x0, x1), F8 (y0, y1).
--     F2 (x0, y0 x1 y1) <- F11 (x0, x1), F3 (y0, y1).
--     F2 (x0, y0 x1 y1) <- F13 (x0, x1), F5 (y0, y1).
--     F2 (x0, y0 x1 y1) <- F2 (x0, x1), F1 (y0, y1).
--     F2 (x0, `C` x1 `A`) <- F11 (x0, x1).
--     F2 (x0, `B` x1) <- F13 (x0, x1).
--     F2 (x0 `B`, x1) <- F1 (x0, x1).
--     F2 (x0, x1 `B`) <- F1 (x0, x1).
--     F2 (x0, `B` x1) <- F1 (x0, x1).
--     F3 (`C` x0, x1 `A`) <- F9 (x0, x1).
--     F3 (`C` x0, `A` x1) <- F9 (x0, x1).
--     F3 (`B` x0, x1) <- F10 (x0, x1).
--     F3 (`A` x0 `C`, x1) <- F1 (x0, x1).
--     F3 (`A` x0, `C` x1) <- F8 (x0, x1).
--     F3 (x0 y0 x1 y1, ) <- F6 (x0, x1), F14 (y0, y1).
--     F3 (x0 y0 x1 y1, ) <- F8 (x0, x1), F15 (y0, y1).
--     F3 (x0 y0 x1 y1, ) <- F10 (x0, x1), F16 (y0, y1).
--     F3 (x0 y0 x1 y1, ) <- F3 (x0, x1), F13 (y0, y1).
--     F3 (x0 y0 x1 y1, ) <- F12 (x0, x1), F6 (y0, y1).
--     F3 (x0 y0 x1 y1, ) <- F5 (x0, x1), F10 (y0, y1).
--     F3 (x0 y0 x1 y1, ) <- F4 (x0, x1), F12 (y0, y1).
--     F3 (x0 y0 x1 y1, ) <- F1 (x0, x1), F4 (y0, y1).
--     F3 (x0 y0 x1, y1) <- F6 (x0, x1), F9 (y0, y1).
--     F3 (x0 y0 x1, y1) <- F10 (x0, x1), F2 (y0, y1).
--     F3 (x0 y0 x1, y1) <- F12 (x0, x1), F3 (y0, y1).
--     F3 (x0 y0 x1, y1) <- F4 (x0, x1), F1 (y0, y1).
--     F3 (x0 y0, x1 y1) <- F10 (x0, x1), F7 (y0, y1).
--     F3 (x0 y0, x1 y1) <- F3 (x0, x1), F9 (y0, y1).
--     F3 (x0 y0, x1 y1) <- F4 (x0, x1), F8 (y0, y1).
--     F3 (x0 y0, x1 y1) <- F1 (x0, x1), F3 (y0, y1).
--     F3 (x0 `C`, x1 `A`) <- F1 (x0, x1).
--     F3 (x0 `C`, `A` x1) <- F1 (x0, x1).
--     F3 (x0, y0 x1 y1) <- F6 (x0, x1), F8 (y0, y1).
--     F3 (x0, y0 x1 y1) <- F8 (x0, x1), F3 (y0, y1).
--     F3 (x0, y0 x1 y1) <- F10 (x0, x1), F5 (y0, y1).
--     F3 (x0, y0 x1 y1) <- F3 (x0, x1), F1 (y0, y1).
--     F3 (x0, `C` x1 `A`) <- F8 (x0, x1).
--     F3 (x0, `B` x1) <- F10 (x0, x1).
--     F4 (`C` x0 `A`, x1) <- F13 (x0, x1).
--     F4 (`C` x0, `A` x1) <- F13 (x0, x1).
--     F4 (`B` x0, x1) <- F10 (x0, x1).
--     F4 (`A` x0, x1 `C`) <- F1 (x0, x1).
--     F4 (`A` x0, `C` x1) <- F12 (x0, x1).
--     F4 (, x0 y0 x1 y1) <- F6 (x0, x1), F14 (y0, y1).
--     F4 (, x0 y0 x1 y1) <- F8 (x0, x1), F15 (y0, y1).
--     F4 (, x0 y0 x1 y1) <- F10 (x0, x1), F16 (y0, y1).
--     F4 (, x0 y0 x1 y1) <- F3 (x0, x1), F13 (y0, y1).
--     F4 (, x0 y0 x1 y1) <- F12 (x0, x1), F6 (y0, y1).
--     F4 (, x0 y0 x1 y1) <- F5 (x0, x1), F10 (y0, y1).
--     F4 (, x0 y0 x1 y1) <- F4 (x0, x1), F12 (y0, y1).
--     F4 (, x0 y0 x1 y1) <- F1 (x0, x1), F4 (y0, y1).
--     F4 (x0 y0 x1, y1) <- F8 (x0, x1), F15 (y0, y1).
--     F4 (x0 y0 x1, y1) <- F3 (x0, x1), F13 (y0, y1).
--     F4 (x0 y0 x1, y1) <- F5 (x0, x1), F10 (y0, y1).
--     F4 (x0 y0 x1, y1) <- F1 (x0, x1), F4 (y0, y1).
--     F4 (x0 y0, x1 y1) <- F10 (x0, x1), F16 (y0, y1).
--     F4 (x0 y0, x1 y1) <- F3 (x0, x1), F13 (y0, y1).
--     F4 (x0 y0, x1 y1) <- F4 (x0, x1), F12 (y0, y1).
--     F4 (x0 y0, x1 y1) <- F1 (x0, x1), F4 (y0, y1).
--     F4 (x0, `B` x1) <- F10 (x0, x1).
--     F4 (x0 `A`, x1 `C`) <- F1 (x0, x1).
--     F4 (x0 `A`, `C` x1) <- F12 (x0, x1).
--     F4 (x0, y0 x1 y1) <- F12 (x0, x1), F6 (y0, y1).
--     F4 (x0, y0 x1 y1) <- F5 (x0, x1), F10 (y0, y1).
--     F4 (x0, y0 x1 y1) <- F4 (x0, x1), F12 (y0, y1).
--     F4 (x0, y0 x1 y1) <- F1 (x0, x1), F4 (y0, y1).
--     F4 (x0, `A` x1 `C`) <- F1 (x0, x1).
--     F5 (`C` x0 `A`, x1) <- F11 (x0, x1).
--     F5 (`C` x0, x1 `A`) <- F11 (x0, x1).
--     F5 (`B` x0, x1) <- F8 (x0, x1).
--     F5 (`B` x0, x1) <- F12 (x0, x1).
--     F5 (`B` x0, x1) <- F1 (x0, x1).
--     F5 (, x0 y0 x1 y1) <- F14 (x0, x1), F7 (y0, y1).
--     F5 (, x0 y0 x1 y1) <- F7 (x0, x1), F9 (y0, y1).
--     F5 (, x0 y0 x1 y1) <- F15 (x0, x1), F11 (y0, y1).
--     F5 (, x0 y0 x1 y1) <- F9 (x0, x1), F2 (y0, y1).
--     F5 (, x0 y0 x1 y1) <- F16 (x0, x1), F8 (y0, y1).
--     F5 (, x0 y0 x1 y1) <- F11 (x0, x1), F3 (y0, y1).
--     F5 (, x0 y0 x1 y1) <- F13 (x0, x1), F5 (y0, y1).
--     F5 (, x0 y0 x1 y1) <- F2 (x0, x1), F1 (y0, y1).
--     F5 (x0 y0 x1, y1) <- F8 (x0, x1), F7 (y0, y1).
--     F5 (x0 y0 x1, y1) <- F3 (x0, x1), F11 (y0, y1).
--     F5 (x0 y0 x1, y1) <- F5 (x0, x1), F8 (y0, y1).
--     F5 (x0 y0 x1, y1) <- F1 (x0, x1), F5 (y0, y1).
--     F5 (x0 y0, x1 y1) <- F6 (x0, x1), F11 (y0, y1).
--     F5 (x0 y0, x1 y1) <- F8 (x0, x1), F2 (y0, y1).
--     F5 (x0 y0, x1 y1) <- F12 (x0, x1), F5 (y0, y1).
--     F5 (x0 y0, x1 y1) <- F5 (x0, x1), F1 (y0, y1).
--     F5 (x0, x1 `B`) <- F8 (x0, x1).
--     F5 (x0 `B`, x1) <- F12 (x0, x1).
--     F5 (x0 `B`, x1) <- F1 (x0, x1).
--     F5 (x0, y0 x1 y1) <- F12 (x0, x1), F7 (y0, y1).
--     F5 (x0, y0 x1 y1) <- F5 (x0, x1), F9 (y0, y1).
--     F5 (x0, y0 x1 y1) <- F4 (x0, x1), F11 (y0, y1).
--     F5 (x0, y0 x1 y1) <- F1 (x0, x1), F2 (y0, y1).
--     F5 (x0, x1 `B`) <- F1 (x0, x1).
--     F6 (`B` x0, x1) <- F10 (x0, x1).
--     F6 (`A` x0 `C`, x1) <- F12 (x0, x1).
--     F6 (`A` x0, x1 `C`) <- F8 (x0, x1).
--     F6 (x0 y0 x1 y1, ) <- F6 (x0, x1), F14 (y0, y1).
--     F6 (x0 y0 x1 y1, ) <- F8 (x0, x1), F15 (y0, y1).
--     F6 (x0 y0 x1 y1, ) <- F10 (x0, x1), F16 (y0, y1).
--     F6 (x0 y0 x1 y1, ) <- F3 (x0, x1), F13 (y0, y1).
--     F6 (x0 y0 x1 y1, ) <- F12 (x0, x1), F6 (y0, y1).
--     F6 (x0 y0 x1 y1, ) <- F5 (x0, x1), F10 (y0, y1).
--     F6 (x0 y0 x1 y1, ) <- F4 (x0, x1), F12 (y0, y1).
--     F6 (x0 y0 x1 y1, ) <- F1 (x0, x1), F4 (y0, y1).
--     F6 (x0 y0 x1, y1) <- F6 (x0, x1), F14 (y0, y1).
--     F6 (x0 y0 x1, y1) <- F10 (x0, x1), F16 (y0, y1).
--     F6 (x0 y0 x1, y1) <- F12 (x0, x1), F6 (y0, y1).
--     F6 (x0 y0 x1, y1) <- F4 (x0, x1), F12 (y0, y1).
--     F6 (x0 y0, x1 y1) <- F6 (x0, x1), F14 (y0, y1).
--     F6 (x0 y0, x1 y1) <- F8 (x0, x1), F15 (y0, y1).
--     F6 (x0 y0, x1 y1) <- F12 (x0, x1), F6 (y0, y1).
--     F6 (x0 y0, x1 y1) <- F5 (x0, x1), F10 (y0, y1).
--     F6 (x0, y0 x1 y1) <- F6 (x0, x1), F14 (y0, y1).
--     F6 (x0, y0 x1 y1) <- F8 (x0, x1), F15 (y0, y1).
--     F6 (x0, y0 x1 y1) <- F10 (x0, x1), F16 (y0, y1).
--     F6 (x0, y0 x1 y1) <- F3 (x0, x1), F13 (y0, y1).
--     F7 (, x0 y0 x1 y1) <- F14 (x0, x1), F7 (y0, y1).
--     F7 (, x0 y0 x1 y1) <- F7 (x0, x1), F9 (y0, y1).
--     F7 (, x0 y0 x1 y1) <- F15 (x0, x1), F11 (y0, y1).
--     F7 (, x0 y0 x1 y1) <- F9 (x0, x1), F2 (y0, y1).
--     F7 (, x0 y0 x1 y1) <- F16 (x0, x1), F8 (y0, y1).
--     F7 (, x0 y0 x1 y1) <- F11 (x0, x1), F3 (y0, y1).
--     F7 (, x0 y0 x1 y1) <- F13 (x0, x1), F5 (y0, y1).
--     F7 (, x0 y0 x1 y1) <- F2 (x0, x1), F1 (y0, y1).
--     F7 (x0 y0 x1, y1) <- F14 (x0, x1), F7 (y0, y1).
--     F7 (x0 y0 x1, y1) <- F15 (x0, x1), F11 (y0, y1).
--     F7 (x0 y0 x1, y1) <- F16 (x0, x1), F8 (y0, y1).
--     F7 (x0 y0 x1, y1) <- F13 (x0, x1), F5 (y0, y1).
--     F7 (x0 y0, x1 y1) <- F14 (x0, x1), F7 (y0, y1).
--     F7 (x0 y0, x1 y1) <- F7 (x0, x1), F9 (y0, y1).
--     F7 (x0 y0, x1 y1) <- F16 (x0, x1), F8 (y0, y1).
--     F7 (x0 y0, x1 y1) <- F11 (x0, x1), F3 (y0, y1).
--     F7 (x0 `C`, x1 `A`) <- F11 (x0, x1).
--     F7 (x0, y0 x1 y1) <- F14 (x0, x1), F7 (y0, y1).
--     F7 (x0, y0 x1 y1) <- F7 (x0, x1), F9 (y0, y1).
--     F7 (x0, y0 x1 y1) <- F15 (x0, x1), F11 (y0, y1).
--     F7 (x0, y0 x1 y1) <- F9 (x0, x1), F2 (y0, y1).
--     F7 (x0, x1 `B`) <- F9 (x0, x1).
--     F7 (x0, x1 `B`) <- F8 (x0, x1).
--     F8 (`C` x0, x1 `A`) <- F7 (x0, x1).
--     F8 (`B` x0, x1) <- F6 (x0, x1).
--     F8 (`B` x0, x1) <- F3 (x0, x1).
--     F8 (`A` x0 `C`, x1) <- F5 (x0, x1).
--     F8 (x0 y0 x1, y1) <- F6 (x0, x1), F7 (y0, y1).
--     F8 (x0 y0 x1, y1) <- F10 (x0, x1), F11 (y0, y1).
--     F8 (x0 y0 x1, y1) <- F12 (x0, x1), F8 (y0, y1).
--     F8 (x0 y0 x1, y1) <- F4 (x0, x1), F5 (y0, y1).
--     F8 (x0 y0, x1 y1) <- F6 (x0, x1), F7 (y0, y1).
--     F8 (x0 y0, x1 y1) <- F8 (x0, x1), F9 (y0, y1).
--     F8 (x0 y0, x1 y1) <- F12 (x0, x1), F8 (y0, y1).
--     F8 (x0 y0, x1 y1) <- F5 (x0, x1), F3 (y0, y1).
--     F8 (x0 `C`, x1 `A`) <- F5 (x0, x1).
--     F8 (x0, y0 x1 y1) <- F6 (x0, x1), F7 (y0, y1).
--     F8 (x0, y0 x1 y1) <- F8 (x0, x1), F9 (y0, y1).
--     F8 (x0, y0 x1 y1) <- F10 (x0, x1), F11 (y0, y1).
--     F8 (x0, y0 x1 y1) <- F3 (x0, x1), F2 (y0, y1).
--     F8 (x0, x1 `B`) <- F3 (x0, x1).
--     F9 (, x0 y0 x1 y1) <- F6 (x0, x1), F7 (y0, y1).
--     F9 (, x0 y0 x1 y1) <- F8 (x0, x1), F9 (y0, y1).
--     F9 (, x0 y0 x1 y1) <- F10 (x0, x1), F11 (y0, y1).
--     F9 (, x0 y0 x1 y1) <- F3 (x0, x1), F2 (y0, y1).
--     F9 (, x0 y0 x1 y1) <- F12 (x0, x1), F8 (y0, y1).
--     F9 (, x0 y0 x1 y1) <- F5 (x0, x1), F3 (y0, y1).
--     F9 (, x0 y0 x1 y1) <- F4 (x0, x1), F5 (y0, y1).
--     F9 (, x0 y0 x1 y1) <- F1 (x0, x1), F1 (y0, y1).
--     F9 (, ) <- .
--     F9 (x0 y0 x1 y1, ) <- F14 (x0, x1), F14 (y0, y1).
--     F9 (x0 y0 x1 y1, ) <- F7 (x0, x1), F15 (y0, y1).
--     F9 (x0 y0 x1 y1, ) <- F15 (x0, x1), F16 (y0, y1).
--     F9 (x0 y0 x1 y1, ) <- F9 (x0, x1), F13 (y0, y1).
--     F9 (x0 y0 x1 y1, ) <- F16 (x0, x1), F6 (y0, y1).
--     F9 (x0 y0 x1 y1, ) <- F11 (x0, x1), F10 (y0, y1).
--     F9 (x0 y0 x1 y1, ) <- F13 (x0, x1), F12 (y0, y1).
--     F9 (x0 y0 x1 y1, ) <- F2 (x0, x1), F4 (y0, y1).
--     F9 (x0 y0 x1, y1) <- F14 (x0, x1), F9 (y0, y1).
--     F9 (x0 y0 x1, y1) <- F15 (x0, x1), F2 (y0, y1).
--     F9 (x0 y0 x1, y1) <- F16 (x0, x1), F3 (y0, y1).
--     F9 (x0 y0 x1, y1) <- F13 (x0, x1), F1 (y0, y1).
--     F9 (x0 y0, x1 y1) <- F15 (x0, x1), F7 (y0, y1).
--     F9 (x0 y0, x1 y1) <- F9 (x0, x1), F9 (y0, y1).
--     F9 (x0 y0, x1 y1) <- F13 (x0, x1), F8 (y0, y1).
--     F9 (x0 y0, x1 y1) <- F2 (x0, x1), F3 (y0, y1).
--     F9 (x0 `C`, x1 `A`) <- F2 (x0, x1).
--     F9 (x0 `C`, `A` x1) <- F2 (x0, x1).
--     F9 (x0, y0 x1 y1) <- F14 (x0, x1), F8 (y0, y1).
--     F9 (x0, y0 x1 y1) <- F7 (x0, x1), F3 (y0, y1).
--     F9 (x0, y0 x1 y1) <- F15 (x0, x1), F5 (y0, y1).
--     F9 (x0, y0 x1 y1) <- F9 (x0, x1), F1 (y0, y1).
--     F9 (x0, `C` x1 `A`) <- F7 (x0, x1).
--     F9 (x0, `B` x1) <- F15 (x0, x1).
--     F9 (x0, x1 `B`) <- F3 (x0, x1).
--     F9 (x0, `B` x1) <- F3 (x0, x1).
--     S (k0) <- F (k0).
--   ],
--   Starting Non-Terminal: S
-- }
exampleMIX3 :: IO (MultiCtxFreeGrammar NString NString NString)
exampleMIX3 = do
  o2 <- mcfgToRtsa exampleO2
  o2 <- return $ runST $ numberExtRtsa (\_ _ _ _ -> return SpUnit) o2
  let preMIX  = extIntersectReg o2 pureABCLanguage
      mix3Aut = extStringHomo preMIX abcMapper
  ret <- rTSAToMultiCFG mix3Aut
  ret <- mapMCFG return (return . (:[])) return ret
  simpleRename ret >>= \case
    Left problem -> error problem
    Right ret -> do
      putStrLn "Check Passed: Is Valid MCFG."
      return ret

abcMapper :: String -> String
abcMapper = \case
  "a1" -> "A"
  "a2" -> "B"
  "oa1" -> "C"
  "oa2" -> ""
  _other -> error "IMPOSSIBLE."

-- | A simple renaming process to provide better look
simpleRename :: (Hashable nt, Num a, Show a, Eq a) =>
  MultiCtxFreeGrammar nt String (Var a)
  -> IO (Either String (MultiCtxFreeGrammar NString NString NString))
simpleRename mcfg = do
  ntRename <- renameNt $ mcfgStartNonTer mcfg
  ret <- mapMCFG ntRename (return . NString) renameVar mcfg
  return $ fmap (const ret) $ isValid ret
  where
    renameNt stNt = do
      getId <- ioAutoNumber
      _ :: Int <- getId stNt
      return $ \nt -> do
        id <- getId nt
        return $ NString $ case id of
          0 -> "S"
          1 -> "F"
          x -> "F" ++ show (x - 1)
    renameVar (Var (ntId, vId)) = return . NString . (++ show vId) $ case ntId of
      0 -> "k"
      1 -> "x"
      2 -> "y"
      3 -> "z"
      4 -> "a"
      5 -> "b"
      _ -> "v@" ++ quoteBy "()" (show ntId)

-- -- | To test if the intersection truly works -- whether non-"oa1 oa2" pattern will be erased.
-- --   Test Passed.
-- -- >>> testIntersection
-- -- MCFG {
-- --   Rules: [
-- --     F (`A` `B` `C`) <- .
-- --     F (x0 x1) <- F1 (x0, x1).
-- --     F1 (`A` `C`, `B`) <- .
-- --     S (k0) <- F (k0).
-- --   ],
-- --   Starting Non-Terminal: S
-- -- }
-- testIntersection :: IO (MultiCtxFreeGrammar NString NString NString)
-- testIntersection = do
--   -- The example has three strings, where one of them has non-"oa1 oa2" pattern
--   let exampleToTest :: MultiCtxFreeGrammar String String String = read $ unlines
--         [ "S (a1 a2 oa1 oa2) <- ."
--         , "S (x y) <- F (x, y)."
--         , "F (oa1 a1, a2 oa2) <- ."
--         , "F (a1 oa1, oa2 a2) <- ." ]
--   er <- mcfgToRtsa exampleToTest
--   er <- return $ runST $ numberExtRtsa (\_ _ _ _ -> return SpUnit) er
--   let int = extIntersectReg er pureABCLanguage
--       newInt = extStringHomo int abcMapper
--   ret <- rTSAToMultiCFG newInt
--   ret <- mapMCFG return (return . (:[])) return ret
--   simpleRename ret >>= \case
--     Left problem -> error problem
--     Right ret -> do
--       putStrLn "Check Passed: Is Valid MCFG."
--       return ret

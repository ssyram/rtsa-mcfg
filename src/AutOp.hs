{-# LANGUAGE Strict #-}
{-# OPTIONS_GHC -Wno-name-shadowing #-}
{-# LANGUAGE TupleSections #-}
module AutOp (FiniteStateAut(..), ReadFSA, GenFSA, Transducer, intersectReg, stringHomo, extIntersectReg, extStringHomo) where
import Objects
import qualified Data.Map as M
import Control.Monad.Identity (Identity (runIdentity))
import Utils (Flip, (|>), toColMap, fstMap)
import qualified Data.Set as S
import Data.Maybe (maybeToList)

{- This file defines the string-generating automaton operations, including:

- （TODO) Intersection with regular language ((D)FSA)
- （TODO) String homomorphism
- （TODO) Rational transduction via (D)FSA
- （TODO) Inverse homomorphism
- （TODO) Union with regualr langauge ((D)FSA)
-}

-- The basic objects

{-| A (deterministic) finite-state automaton ((D)FSA) is a tuple (Q, \Sigma, \Delta, F, q_0):

- Q is a finite set of states.
- \Sigma is the set of alphabet.
- \Delta : (Q \times \Sigma) -> Q is the transition function
- F \subseteq Q: is a set of accepting states
- q_0 \in Q is the initial state

Additionally, we use `info` to generalise the possible information that can be carried along the state.

Examples for the usual cases:
- For reading FSA   : `info` is `Identity`
- For generating FSA: `sigma` is `()` and `info q` is `Map q alphabet`
- For transducer FSA: `info` is `(OutAlphabet, q)`

The non-deterministic version is when `info q` is some kinds of list.
-}
data FiniteStateAut q sigma info = FiniteStateAut
  { fsaRules :: M.Map (q, sigma) (info q)
  , fsaAccStates :: S.Set q
  , fsaInitState :: q }

-- | The FSA that reads and accept the strings
type ReadFSA q sigma = FiniteStateAut q sigma Identity

-- | The FSA that generates the accepting strings
type GenFSA q sigma = FiniteStateAut q () (Flip M.Map sigma)

-- | The FSA that read strings and then produce another kinds of strings
type Transducer q i o = FiniteStateAut q i ((,) o)

-- | The special operation that allows change of its internal state information
class SpMapSt sp where
  mapSt :: sp q m g -> (q -> q') -> Maybe (sp q' m g)

instance SpMapSt SpUnit where
  mapSt :: SpUnit q m g -> (q -> q') -> Maybe (SpUnit q' m g)
  mapSt _ _ = Just SpUnit

instance SpMapSt SpTer where
  mapSt :: SpTer q m g -> (q -> q') -> Maybe (SpTer q' m g)
  mapSt _ _ = Just SpTer

instance SpMapSt SpHorizontal where
  mapSt :: SpHorizontal q m g -> (q -> q') -> Maybe (SpHorizontal q' m g)
  mapSt (SpHor q) mapper = Just $ SpHor $ mapper q

-- | Given an initial state, what is the possible target state after reading a given string
traceString :: (Foldable f, Ord q, Ord t) => ReadFSA q t -> q -> f t -> Maybe q
traceString fsa stQ = foldl (combine fsa) $ Just stQ
  where
    combine fsa preQ t = do
      q <- preQ
      inq <- fsaRules fsa M.!? (q, t)
      return $ runIdentity inq

{-| The intersection between MCFL and RL, represented by rTSA and ReadFSA
respectively.

The construct is given by tracing the operations.

Procedure:
- Collect all the possible `d` to go -- from both sides
- Expand the rule lists
- For each `d`, compute the new list
- Pack the information back to the original place
-}
intersectReg ::
  (SpMapSt sp, Ord t, Ord d, Ord q, Ord m, Ord g, Ord (sp (q, d) m g)) =>
  RestrictedTreeStackAut q m g [t] sp
  -> ReadFSA d t
  -> RestrictedTreeStackAut (q, d) m g [t] sp
intersectReg rtsa fsa =
  rearrangeRules rtsa fsa
  |> toColMap
  |> \rules -> RestrictedTreeStackAut
  { rtsaRules = rules
  , rtsaInitSt = (rtsaInitSt rtsa, fsaInitState fsa)
  , rtsaRestriction = rtsaRestriction rtsa
  , rtsaDefLocMem = rtsaDefLocMem rtsa }

-- | Simply distribute all possible `d` in the FSA to the DownMap
extIntersectReg ::
  (SpMapSt sp, Ord a, Ord b, Ord g, Ord t, Ord m, Ord (sp (a, b) m g)) =>
  ExtendedRTSA a m g [t] sp
  -> ReadFSA b t -> ExtendedRTSA (a, b) m g [t] sp
extIntersectReg er fsa = ExtendedRTSA
  { eRtsaKMap = eRtsaKMap er
  , eRtsaDownMap = newDownMap fsa <$> eRtsaDownMap er
  , eRtsaAutomaton=intersectReg (eRtsaAutomaton er) fsa }
  where
    newDownMap fsa map = toColMap $ do
      d <- allD fsa
      d' <- allD fsa
      ((q, g), set) <- M.toList map
      q' <- S.toList set
      return (((q, d), g), (q', d'))


rearrangeRules ::
  (Ord d, Ord t, SpMapSt sp) =>
  RestrictedTreeStackAut q m g [t] sp
  -> ReadFSA d t
  -> [(((q, d), m, Gamma g), ([t], Operation (q, d) m g sp))]
rearrangeRules rtsa fsa = do
  d <- allD fsa
  ((q, m, g), lst) <- M.toList $ rtsaRules rtsa
  (info, op) <- S.toList lst
  d' <- maybeToList $ traceString fsa d info
  op' <- maybeToList $ case op of
        OpUp q' m' g' -> return $ OpUp (q', d') m' g'
        OpDown q' m' ->
          -- This need to consider if the stuff is terminating
          if isBot g && not (d' `S.member` fsaAccStates fsa) then Nothing
          else return $ OpDown (q', d') m'
        OpSp sp -> OpSp <$> mapSt sp (,d')
  return (((q, d), m, g), (info, op'))

-- | Guaranteed to be NO duplicate information
allD :: Ord d => ReadFSA d t -> [d]
allD fsa =
  allRulesD fsa
  |> (fsaInitState fsa:)
  |> S.fromList
  |> S.union (fsaAccStates fsa)
  |> S.toList
  where
    allRulesD fsa = do
      ((d, _), d') <- M.toList $ fsaRules fsa
      [d, runIdentity d']

-- | The string homomorphism operation maps each character to a new sequence of string
stringHomo ::
  (Ord b, Ord q, Ord m, Ord g, Ord (sp q m g)) =>
  RestrictedTreeStackAut q m g [a] sp
  -> (a -> [b])
  -> RestrictedTreeStackAut q m g [b] sp
stringHomo rtsa f = rtsa { rtsaRules = M.map (mapper f) $ rtsaRules rtsa }
  where mapper f = S.map (fstMap $ concatMap f)

-- | Exactly the same as pure `stringHomo`.
extStringHomo ::
  (Ord b, Ord q, Ord m, Ord g, Ord (sp q m g)) =>
  ExtendedRTSA q m g [a] sp
  -> (a -> [b]) -> ExtendedRTSA q m g [b] sp
extStringHomo er f = ExtendedRTSA
  { eRtsaKMap = eRtsaKMap er
  , eRtsaDownMap = eRtsaDownMap er
  , eRtsaAutomaton = stringHomo (eRtsaAutomaton er) f }

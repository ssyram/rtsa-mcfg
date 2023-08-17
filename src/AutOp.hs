{-# LANGUAGE Strict #-}
{-# OPTIONS_GHC -Wno-name-shadowing #-}
module AutOp (FiniteStateAut(..), ReadFSA, GenFSA, Transducer) where
import Objects
import qualified Data.Map as M
import Control.Monad.Identity (Identity (runIdentity))
import Utils (Flip)
import qualified Data.Set as S

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
  mapSt :: sp q m g -> (q -> q') -> sp q' m g

traceString :: (Foldable f, Ord q, Ord t) => ReadFSA q t -> q -> f t -> Maybe q
traceString fsa stQ = foldl (combine fsa) $ Just stQ
  where
    combine fsa preQ t = do
      q <- preQ
      inq <- fsaRules fsa M.!? (q, t)
      return $ runIdentity inq

{-| The intersection between MCFL and RL, represented by rTSA and ReadFSA
respectively.

The construct is given by tracing the operations
-}
intersectReg :: (SpMapSt sp) =>
  RestrictedTreeStackAut q m g [t] sp
  -> ReadFSA d t
  -> RestrictedTreeStackAut (q, d) m g [t] sp
intersectReg = undefined

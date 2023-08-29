{-# LANGUAGE Strict #-}
{-# OPTIONS_GHC -Wno-name-shadowing #-}
{-# LANGUAGE ScopedTypeVariables #-}
module EqSysIter (iterEqSys) where
import Utils (whenM, sndMap, whileM)
import qualified Data.HashTable.ST.Basic as HT
import Control.Monad (forM_, forM)
import Control.Monad.Trans.Cont (evalContT, callCC)
import Control.Monad.ST.Class (MonadST(liftST, World))
import EqSysBuild (EqSys(EqSys), SynComp (SynComp))
import Data.Maybe (fromJust)
import Data.Hashable ( Hashable )
import Control.Monad.ST ( ST )
import Control.Monad.Cont (lift)
import qualified Data.HashTable.Class as HT (toList, fromList)
import Data.Tuple (swap)

-- This file defines the iteration method of the equation system

-- -- | Example of how to use `iterEqSys` in `IO` context
-- --   The key is: let the stopping criteria still in the `ST` context
-- --   While converting the final result by `stToIO`
-- ioIterEqSys eqSys = do
--   stToIO $ flip iterEqSys eqSys $ \map -> do
--     HT.foldM (\res (_, vp) -> return $ res && uncurry (closeEnough 1e-7) vp) True map
--   where
--     closeEnough threshold x y = abs (x - y) < threshold




{-| Iterate the given equation system until the given stop criteria becomes `True`

In the stop crieria, the function is provided the current computed results --
For every variable, a pair of previous results from the previous round and 
the newly computed result of this round.

So the meaning of the stopping criteria is:

> { var |-> (prevResult, thisResult) } -> True / False
-}
iterEqSys :: (MonadST m, Hashable v, Eq v, Num n) =>
  (HT.HashTable (World m) v (n, n) -> m Bool) -- ^ stopping criteria
  -> EqSys v n -- ^ the target equation system
  -> m (HT.HashTable (World m) v n)
iterEqSys toStop (EqSys lst) = evalContT $ callCC $ \exit -> do
  -- initialise the stuff
  resultMap <- liftST HT.new
  liftST $ forM_ lst $ \(v, _) -> HT.insert resultMap v (0, 0)

  -- Conduct iteration, until `toStop` becomes `true`, inside the loop
  whileM (return True) $ do

    -- one round of iteration --
    -- information kept within the second place of the `resultMap`
    liftST $ forM_ lst $ \(v, rhs) -> do
      newVal <- computeRHS resultMap rhs
      HT.mutate resultMap v $ \ ~(Just pair) ->
        (Just $ sndMap (const newVal) pair, ())
      
    -- if it should stop according to the provided criteria, transform the result and get out
    whenM (lift $ toStop resultMap) $ do
      resultMap <- liftST $ toResult resultMap
      exit resultMap

    -- if it should keep going
    -- move this round of result to position `fst` to become the previous round for the next round
    liftST $ forM_ lst $ \(v, _) -> 
      HT.mutate resultMap v $ \ ~(Just pair) ->
        (Just $ swap pair, ())

  -- impossible to be here, just for type-checking
  error "Impossible to come here."



-- | According to the convention, the second place contains the latest information
toResult :: (Hashable k, Eq k) => HT.HashTable s k (v, v) -> ST s (HT.HashTable s k v)
toResult resultMap = do
  lst <- HT.toList resultMap
  HT.fromList $ fmap (sndMap snd) lst

computeRHS :: (Traversable t, Hashable v, Eq v, Num n) =>
  HT.HashTable s v (n, n) -> t (SynComp v n) -> ST s n
computeRHS resultMap rhs = sum <$> forM rhs (computeSynComp resultMap)
  where
    computeSynComp resultMap (SynComp (acc, vars)) =
      foldl (*) acc <$> mapM (fmap (fst . fromJust) . HT.lookup resultMap) vars

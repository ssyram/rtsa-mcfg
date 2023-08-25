{-# LANGUAGE Strict #-}
{-# OPTIONS_GHC -Wno-name-shadowing #-}
{-# LANGUAGE LambdaCase #-}
module EqSysSimp (substConstant, removeSimpleEmptyVars, removeRecurEmptyVar, removeEmptyVars) where
import EqSysBuild (EqSys (..), SynComp (SynComp))
import qualified Data.HashTable.Class as HT (toList)
import qualified Data.HashTable.ST.Basic as HT
import Control.Monad.ST (runST, ST)
import Utils (Modifiable(newRef, readRef), whileM, (<<-), sndMapM, anyM, (|>), RevList (RevList), revToList, sndMap)
import qualified Data.List as List
import Data.Hashable
import Control.Monad (forM_, filterM, forM, foldM)
import Data.Maybe (isJust, fromJust)
import qualified Data.Map.Strict as M
import Control.Monad.ST.Class (MonadST (liftST))
import EqSysIter (iterEqSys)

-- Old specific version

-- -- | Remove all the empty variables from the equation system
-- --   Returns all the found zero variables (non-repeating) and the refined equation system
-- removeZeroVars ::
--   (Eq v, Hashable v) =>
--   EqSys v acc -> ([v], EqSys v acc)
-- removeZeroVars eqSys = runST $ do
--   -- variables definitions
--   zeroVars <- HT.new
--   cChanged <- newRef True
--   cRet <- newRef eqSys

--   -- actual run
--   whileM (readRef cChanged) $ iterRound zeroVars cChanged cRet

--   -- return
--   zvLst <- fmap fst <$> HT.toList zeroVars
--   ret <- readRef cRet
--   return (zvLst, ret)


-- iterRound :: (Eq v, Hashable v) => HT.HashTable s (v) ()
--   -> STRef s Bool
--   -> STRef s (EqSys v acc)
--   -> ST s ()
-- iterRound zeroVars cChanged cRet = do
--   -- read value
--   (EqSys lst) <- readRef cRet

--   -- cut out those instant zero values
--   (zVars, lst) <- return $ fstMap (fmap fst) $ List.partition (null . snd) lst
--   -- add all newly found empty variable to it
--   forM_ zVars $ \k -> HT.insert zeroVars k ()
--   -- modify the rest of the RHS of the rest of the equation system
--   lst <- forM lst $ sndMapM $ filterM $ hasZeroVar zeroVars

--   -- modify the value
--   cChanged <<- not $ null zVars
--   cRet <<- EqSys lst


-- | The abstract framework of constant propagation
constPropagate :: (MonadST m) =>
  ([SynComp v acc] -> Bool)  -- ^ partition function to judge 
  -> ([(v, [SynComp v acc])] -> m ())
  -> ([SynComp v acc] -> m [SynComp v acc])
  -> EqSys v acc
  -> m (EqSys v acc)
constPropagate isConst logConstVars modifyRHS eqSys = do
  retCell <- liftST $ newRef eqSys
  changedCell <- liftST $ newRef True

  whileM (liftST $ readRef changedCell) $ do
    (EqSys lst) <- liftST $ readRef retCell
    -- separate those constant variables from the whole EqSys by partitioning them
    (constVars, lst) <- return $ List.partition (isConst . snd) lst
    -- log / record these constant variables
    logConstVars constVars
    -- modify the RHS of the left variables
    lst <- forM lst $ sndMapM modifyRHS
    -- write variables
    liftST $ changedCell <<- not $ null constVars
    liftST $ retCell <<- EqSys lst

  liftST $ readRef retCell


{-| Remove all the simple empty variables from the equation system.

Also propagate these found empty variables.
However, those void dependencies are not removed, call `removeRecurEmptyVar` to erase them

For example, systems like:

> x = 0.5 * x'

and

> x' = 0.5 * x

The variables `x` and `x'` are not erased.
They are expected to be handled by `removeRecurEmptyVar`.

Returns all the found empty variables (non-repeating) and the refined equation system
-}
removeSimpleEmptyVars ::
  Hashable v => EqSys v acc -> ([v], EqSys v acc)
removeSimpleEmptyVars eqSys = runST $ do
  zeroVars <- HT.new

  ret <- constPropagate
          null  -- isConst
          (mapM_ $ \(k, _) -> HT.insert zeroVars k ())  -- logConstVars
          (filterRHS zeroVars)  -- modifyRHS
          eqSys

  -- return
  zvLst <- fmap fst <$> HT.toList zeroVars
  return (zvLst, ret)

filterRHS :: Hashable v => HT.HashTable s v ()
  -> [SynComp v acc]
  -> ST s [SynComp v acc]
filterRHS zeroVars = filterM $ hasEmptyVar zeroVars
  where
    hasEmptyVar :: Hashable v => HT.HashTable s v () -> SynComp v acc -> ST s Bool
    hasEmptyVar zeroVars (SynComp (_, lst)) =
      anyM (fmap isJust . HT.lookup zeroVars) lst


{-| Use iteration to find and erase the mutually depending empty variables

For example:

> x = x' & x' = x

In this case, the `removeSimpleEmptyVars` is not going to work because it just erases 
the direct stuff.
-}
removeRecurEmptyVar :: Hashable v =>EqSys v acc -> ([v], EqSys v acc)
removeRecurEmptyVar (EqSys oriLst) =
  fmap (sndMap $ fmap $ \(SynComp (_, vars)) -> SynComp (1 :: Int, vars)) oriLst
  |> EqSys
  |> \eqSys@(EqSys lst) -> runST $ do
    cRound <- newRef (0 :: Int)
    let targetRound = length lst + 1
    iterRes <- iterEqSys (reachedTargetRound cRound targetRound) eqSys
    lst <- forM oriLst $ \(v, rhs) -> do
      res <- fromJust <$> HT.lookup iterRes v
      if res == 0 then return (v, [])
      else return (v, rhs)
    return $ removeSimpleEmptyVars $ EqSys lst

reachedTargetRound :: (Modifiable m r, Num a, Ord a) => r a -> a -> p -> m Bool
reachedTargetRound cRound targetRound _ = do
  round <- readRef cRound
  let ret = round >= targetRound
  cRound <<- round + 1
  return ret

-- | Combines `removeSimpleEmptyVars` and `removeRecurEmptyVars`
--   Guaranteed to erase all the empty variables
--   Returns the non-duplicating list of found empty variables and the refined EqSys
removeEmptyVars :: (Hashable v) =>EqSys v acc -> ([v], EqSys v acc)
removeEmptyVars eqSys =
  let (emptyVars, newEqSys) = removeSimpleEmptyVars eqSys
      (moreEmptyVars, retEqSys) = removeRecurEmptyVar newEqSys
  in
  (emptyVars ++ moreEmptyVars, retEqSys)

-- | Substitute the constant values -- ONLY USE THIS FUNCTION WHEN `acc` IS A *COMMUTATIVE MONOID*
--   Because the substitution will combine the accumulatives, so the position may not hold
--   Returns the map of found constant variables and the equation system
substConstant ::
  (Ord v, Hashable v, Monoid acc) =>
  EqSys v acc -> (M.Map v acc, EqSys v acc)
substConstant eqSys = runST $ do
  constMap <- HT.new

  ret <- constPropagate
          isConst
          (logConstVars constMap)
          (modifyRHS constMap)
          eqSys

  cMap <- M.fromList <$> HT.toList constMap
  return (cMap, ret)

isConst :: [SynComp v acc] -> Bool
isConst = List.all isConst
  where
    isConst (SynComp (_, [])) = True
    isConst (SynComp (_, _l)) = False

logConstVars :: (Monoid acc, Hashable v) =>
  HT.HashTable s v acc
  -> [(v, [SynComp v acc])] -> ST s ()
logConstVars constMap lst = forM_ lst $ \(v, constRHS) ->
  fmap (\(SynComp (acc, _)) -> acc) constRHS
  |> foldl (<>) mempty  -- MUST BE `foldl` NOT `foldr`
  |> HT.insert constMap v

modifyRHS :: (Monoid acc, Hashable v) =>
  HT.HashTable s v acc
  -> [SynComp v acc]
  -> ST s [SynComp v acc]
modifyRHS constMap rhs = forM rhs $ \(SynComp (acc, vars)) -> do
  (acc, vars) <- foldM (folder constMap) (acc, RevList []) vars
  return $ SynComp (acc, revToList vars)
  where
    folder constMap (acc, rVars@(RevList rvLst)) var = HT.lookup constMap var >>= \case
       Nothing -> return (acc, RevList $ var : rvLst)
       Just cV -> return (acc <> cV, rVars)

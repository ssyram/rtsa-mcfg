{-# LANGUAGE Strict #-}
{-# OPTIONS_GHC -Wno-name-shadowing #-}
{-# LANGUAGE LambdaCase #-}
module EqSysSimp (substConstant, removeEmptyVars) where
import EqSysBuild (EqSys (..), AbsVar, SynComp (SynComp))
import qualified Data.HashTable.Class as HT (toList)
import qualified Data.HashTable.ST.Basic as HT
import Control.Monad.ST (runST, ST)
import Utils (Modifiable(newRef, readRef), whileM, (<<-), sndMapM, anyM, (|>), RevList (RevList), revToList)
import qualified Data.List as List
import Data.Hashable
import Control.Monad (forM_, filterM, forM, foldM)
import Data.Maybe (isJust)
import qualified Data.Map.Strict as M
import Control.Monad.ST.Class (MonadST (liftST))

-- Old specific version

-- -- | Remove all the empty variables from the equation system
-- --   Returns all the found zero variables (non-repeating) and the refined equation system
-- removeZeroVars ::
--   (Eq q, Eq g, Hashable q, Hashable g) =>
--   EqSys q g acc -> ([AbsVar q g], EqSys q g acc)
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


-- iterRound :: (Eq q, Eq g, Hashable q, Hashable g) => HT.HashTable s (AbsVar q g) ()
--   -> STRef s Bool
--   -> STRef s (EqSys q g acc)
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


hasEmptyVar :: (Eq q, Eq g, Hashable q, Hashable g) =>
  HT.HashTable s (AbsVar q g) () -> SynComp q g acc -> ST s Bool
hasEmptyVar zeroVars (SynComp _ lst) =
  anyM (fmap isJust . HT.lookup zeroVars) lst


-- | The abstract framework of constant propagation
constPropagate :: (MonadST m) =>
  ([SynComp q g acc] -> Bool)  -- ^ partition function to judge 
  -> ([(AbsVar q g, [SynComp q g acc])] -> m ())
  -> ([SynComp q g acc] -> m [SynComp q g acc])
  -> EqSys q g acc
  -> m (EqSys q g acc)
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


-- | Remove all the empty variables from the equation system
--   Returns all the found empty variables (non-repeating) and the refined equation system
removeEmptyVars ::
  (Eq q, Eq g, Hashable q, Hashable g) =>
  EqSys q g acc -> ([AbsVar q g], EqSys q g acc)
removeEmptyVars eqSys = runST $ do
  zeroVars <- HT.new

  ret <- constPropagate
          null  -- isConst
          (mapM_ $ \(k, _) -> HT.insert zeroVars k ())  -- logConstVars
          (filterM $ hasEmptyVar zeroVars)  -- modifyRHS
          eqSys

  -- return
  zvLst <- fmap fst <$> HT.toList zeroVars
  return (zvLst, ret)


-- | Substitute the constant values -- ONLY USE THIS FUNCTION WHEN `acc` IS A *COMMUTATIVE MONOID*
--   Because the substitution will combine the accumulatives, so the position may not hold
--   Returns the map of found constant variables and the equation system
substConstant ::
  (Ord q, Ord g, Hashable q, Hashable g, Monoid acc) =>
  EqSys q g acc -> (M.Map (AbsVar q g) acc, EqSys q g acc)
substConstant eqSys = runST $ do
  constMap <- HT.new

  ret <- constPropagate
          isConst
          (logConstVars constMap)
          (modifyRHS constMap)
          eqSys

  cMap <- M.fromList <$> HT.toList constMap
  return (cMap, ret)

isConst :: [SynComp q g acc] -> Bool
isConst = List.all isConst
  where
    isConst (SynComp _ []) = True
    isConst (SynComp _ _l) = False

logConstVars :: (Monoid acc, Eq q, Eq g, Hashable q, Hashable g) =>
  HT.HashTable s (AbsVar q g) acc
  -> [(AbsVar q g, [SynComp q g acc])] -> ST s ()
logConstVars constMap lst = forM_ lst $ \(v, constRHS) ->
  fmap (\(SynComp acc _) -> acc) constRHS
  |> foldl (<>) mempty  -- MUST BE `foldl` NOT `foldr`
  |> HT.insert constMap v

modifyRHS :: (Monoid acc, Eq q, Eq g, Hashable q, Hashable g) =>
  HT.HashTable s (AbsVar q g) acc
  -> [SynComp q g acc] 
  -> ST s [SynComp q g acc]
modifyRHS constMap rhs = forM rhs $ \(SynComp acc vars) -> do
  (acc, vars) <- foldM (folder constMap) (acc, RevList []) vars
  return $ SynComp acc $ revToList vars
  where
    folder constMap (acc, rVars@(RevList rvLst)) var = HT.lookup constMap var >>= \case
       Nothing -> return (acc, RevList $ var : rvLst)
       Just cV -> return (acc <> cV, rVars)

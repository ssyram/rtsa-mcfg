{-# LANGUAGE Strict #-}
{-# OPTIONS_GHC -Wno-name-shadowing #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE TypeFamilies #-}
{-# OPTIONS_GHC -Wno-redundant-constraints #-}
module EqSysSimp (
  substConstant,
  removeSimpleEmptyVars,
  removeRecurEmptyVar,
  removeEmptyVars,
  NormPoly(..),
  NormEqSys(..),
  toNormPoly,
  toNormEqSys,
  fromNormPoly,
  fromNormEqSys,
  removeDuplicatedVars,
  substVar,
  substCompVar,
  collectDuplicateInfo
) where
import EqSysBuild (EqSys (..), SynComp (SynComp))
import qualified Data.HashTable.Class as HT (toList, fromList)
import qualified Data.HashTable.ST.Basic as HT
import Control.Monad.ST (runST, ST)
import Utils (Modifiable(newRef, readRef), whileM, (<<-), sndMapM, anyM, (|>), RevList (RevList), revToList, sndMap, quoteBy, printLstContent, toLogicT)
import qualified Data.List as List
import Data.Hashable
import Control.Monad (forM_, filterM, forM, foldM, guard)
import Data.Maybe (isJust, fromJust)
import qualified Data.Map.Strict as M
import Control.Monad.ST.Class (MonadST (liftST))
import EqSysIter (iterEqSys)
import Debug.Trace (trace)
import Control.Monad.Logic (observeAllT)
import qualified Data.UnionFind.ST as UF
import GHC.Generics (Generic)

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
constPropagate :: (MonadST m, Show v, Show acc) =>
  ([SynComp v acc] -> Bool)  -- ^ partition function to judge 
  -> ([(v, [SynComp v acc])] -> m ())
  -> ([SynComp v acc] -> m [SynComp v acc])
  -> EqSys v acc
  -> m (EqSys v acc)
constPropagate isConst logConstVars modifyRHS eqSys = do
  retCell <- liftST $ newRef eqSys
  changedCell <- liftST $ newRef True

  whileM (liftST $ readRef changedCell) $ do
    eqSys@(EqSys lst) <- liftST $ readRef retCell
    trace ("To propagate: " ++ show eqSys) $ return ()
    -- separate those constant variables from the whole EqSys by partitioning them
    (constVars, lst) <- return $ List.partition (isConst . snd) lst
    trace ("Found const vars: " ++ show (quoteBy "[]" $ printLstContent constVars)) $ return ()
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
  (Hashable v, Show v, Show acc) => EqSys v acc -> ([v], EqSys v acc)
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
filterRHS zeroVars lst = do
  -- zv <- HT.toList zeroVars
  -- trace ("Zero Vars to Filter: " ++ show (quoteBy "[]" $ printLstContent zv)) $ return ()
  filterM (fmap not . hasEmptyVar zeroVars) lst
  where
    hasEmptyVar :: (Hashable v) => HT.HashTable s v () -> SynComp v acc -> ST s Bool
    hasEmptyVar zeroVars (SynComp (_, lst)) = do
      anyM (finder zeroVars) lst
    finder zeroVars v = do
      isJust <$> HT.lookup zeroVars v

{-| Use iteration to find and erase the mutually depending empty variables

For example:

> x = x' & x' = x

In this case, the `removeSimpleEmptyVars` is not going to work because it just erases 
the direct stuff.
-}
removeRecurEmptyVar :: (Hashable v, Show v, Show acc) =>EqSys v acc -> ([v], EqSys v acc)
removeRecurEmptyVar (EqSys oriLst) =
  fmap (sndMap $ fmap $ \(SynComp (_, vars)) -> SynComp (1 :: Int, vars)) oriLst
  |> EqSys
  |> \eqSys@(EqSys lst) -> runST $ do
    trace ("To iterate: " ++ show eqSys) $ return ()
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
removeEmptyVars :: (Hashable v, Show v, Show acc) => EqSys v acc -> ([v], EqSys v acc)
removeEmptyVars eqSys =
  let (emptyVars, newEqSys) = removeSimpleEmptyVars eqSys
      (moreEmptyVars, retEqSys) = removeRecurEmptyVar newEqSys
  in
  (emptyVars ++ moreEmptyVars, retEqSys)

-- | Substitute the constant values -- ONLY USE THIS FUNCTION WHEN `acc` IS A *COMMUTATIVE MONOID*
--   Because the substitution will combine the accumulatives, so the position may not hold
--   Returns the map of found constant variables and the equation system
substConstant ::
  (Ord v, Hashable v, Monoid acc, Show v, Show acc) =>
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

-- | The normalised formula
newtype NormPoly v c = NormPoly (M.Map (M.Map v Int) c)
  deriving (Eq, Ord, Generic, Hashable)

-- | The normalised EqSys
newtype NormEqSys v c = NormEqSys [(v, NormPoly v c)]
  deriving (Eq, Ord, Generic, Hashable)

instance (Show v, Show c) => Show (NormEqSys v c) where
  show :: (Show v, Show c) => NormEqSys v c -> String
  show = show . fromNormEqSys

toNormPoly :: (Ord k, Num c) => [SynComp k c] -> NormPoly k c
toNormPoly lst =
  fmap mapper lst
  |> M.fromListWith (*)
  |> NormPoly
  -- Form the map of variables with counts
  where mapper (SynComp (c, vs)) = (M.fromListWith (+) $ map (,1) vs, c)

fromNormPoly :: NormPoly v a -> [SynComp v a]
fromNormPoly (NormPoly map) =
  M.toList map
  |> fmap mapper
  where
    mapper (map, c) = SynComp (c, reEnum map)
    reEnum map =
      M.toList map
      |> concatMap smooth
    smooth (v, count) = replicate count v

toNormEqSys :: (Ord v, Num c) => EqSys v c -> NormEqSys v c
toNormEqSys (EqSys lst) = NormEqSys $ fmap (sndMap toNormPoly) lst

fromNormEqSys :: NormEqSys v acc -> EqSys v acc
fromNormEqSys (NormEqSys lst) = EqSys $ fmap (sndMap fromNormPoly) lst

-- | Substitute the variables in a given equation system with a given function.
substVar :: (Monad m, Num c) => EqSys v c -> (v -> m (Either c v)) -> m (EqSys v c)
substVar (EqSys lst) f = EqSys <$> mapM (mapper f) lst
  where
    mapper f (v, comp) = do
      comp <- mapM (substCompVar f) comp
      return (v, comp)

substCompVar :: (Monad f, Num acc) =>
  (a -> f (Either acc v)) -> SynComp a acc -> f (SynComp v acc)
substCompVar f (SynComp (c, vs)) = SynComp <$> foldM (folder f) (c, []) vs
  where folder f (c, lst) v = f v >>= \case
          Left c'  -> return (c * c', lst)
          Right v' -> return (c, v' : lst)



{-| Remove the variables with the same RHS.

For those equivalent variables, only the variable with the LEAST order is maintained.

Examples:
- Given an equation system:

> x = xy
> y = xy

- After performing `removeDuplicatedVars`, one obtains:

> x = xx
-}
removeDuplicatedVars :: (Num acc, Hashable v, Hashable acc, Ord v) =>
  EqSys v acc -> EqSys v acc
removeDuplicatedVars eqSys@(EqSys lst) = runST $ do
  -- First just collect the information of the union-find sets
  varTab <- collectDuplicateInfo norm eqSys

  -- Core job: filter and map the result
  --           use the `LogicT` to realise the effect of `List` Monad
  lst <- observeAllT $ do
    (v, comps) <- toLogicT lst
    ~(Just p) <- liftST $ HT.lookup varTab v
    rep <- liftST $ UF.descriptor p
    guard $ rep == v  -- otherwise, it should be replaced by the other
    comps <- forM comps $ substCompVar $ subst varTab
    return (v, comps)
    
  -- Return the result
  return $ EqSys lst
  
  where

    norm eqSys =
      let (NormEqSys normLst) = toNormEqSys eqSys in
      return normLst

    subst varTab v = liftST $ do
      p <- fromJust <$> HT.lookup varTab v
      v <- UF.descriptor p
      return $ Right v
      

-- | Given an equation system, collect the map of
--   variables with the corresponding union-find set.
--   The `descriptor` of the union-find sets are the variables with the LEAST order
--   The pre-processing component of `removeDuplicatedVars`.
--   Provided the `normalise` function to normalise the whole equation system so that the RHS
--   has a UNIQUE representation.
--   The correctness of the function will be affected by the `normalise` function
collectDuplicateInfo :: (Foldable t, Hashable a, Hashable k, Ord a) =>
  (EqSys a acc -> ST s (t (a, k)))
  -> EqSys a acc -> ST s (HT.HashTable s a (UF.Point s a))
collectDuplicateInfo normalise eqSys@(EqSys lst) = do
  varTab <- initVarTab lst
  polyTab <- HT.new
  normLst <- normalise eqSys

  forM_ normLst $ \(v, normPoly) -> HT.mutateST polyTab normPoly $ \case

    -- Create a new polynomial mapping with the point of the current `v`
    Nothing -> do
      ~(Just p) <- HT.lookup varTab v
      return (Just p, ())

    -- Merge the two polynomials, use the one with less order as the `descriptor`
    Just op -> do
      ~(Just p) <- HT.lookup varTab v
      odv <- UF.descriptor op
      dv  <- UF.descriptor p
      let (pMin, pMax) = if odv <= dv then (op, p) else (p, op)
      pMax `UF.union` pMin
      return (Just p, ())
    
  return varTab


  where

    initVarTab lst = do
      lst <- mapM mapper lst
      HT.fromList lst

    mapper (v, _) = do
      p <- UF.fresh v
      return (v, p)

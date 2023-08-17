{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE LambdaCase #-}
{-# OPTIONS_GHC -Wno-incomplete-uni-patterns #-}
{-# OPTIONS_GHC -Wno-name-shadowing #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE InstanceSigs #-}
{-# OPTIONS_GHC -Wno-orphans #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TupleSections #-}
module Utils where
import Data.List (intercalate)
import Control.Monad.State (StateT, MonadTrans (lift), evalStateT, forM_, foldM)
import Control.Monad.ST.Strict (ST)
import Control.Monad.Reader (ReaderT (runReaderT), when)
import qualified Data.HashTable.Class as HT
import qualified Data.Map.Strict as M
import qualified Data.HashTable.IO as HTO
import Data.Maybe (isJust)
import Data.Hashable ( Hashable )
import Data.STRef.Strict (readSTRef, writeSTRef, STRef, newSTRef, modifySTRef')
import Data.IORef (IORef, newIORef, readIORef, writeIORef, modifyIORef')
import Data.HashTable.IO (IOHashTable)
import Control.Monad.Cont (MonadCont (callCC))
import Control.Monad.Trans.Cont (evalContT)
import Control.Monad.Logic (LogicT(LogicT))

printLstContent :: Show a => [a] -> String
printLstContent lst = intercalate ", " $ fmap show lst

quoteBy :: String -> String -> String
quoteBy q str =
  let (qs, qe) = splitAt (length q `div` 2) str in
  qs ++ str ++ qe

(|>) :: t1 -> (t1 -> t2) -> t2
x |> f = f x

infixl 1 |>

-- | The state with `ST` so that there is internal carrying information in `info`
--   which may also depend on the same `ST` environment
type STState s info = StateT (info s) (ST s)

-- | The delimit function to run a local STState with different carrying information
ststDelimit :: STState s info (info' s) -- ^ the initial state generator for the local state
  -> STState s info' a -- ^ the local state to execute with the initial state just generated
  -> STState s info a
ststDelimit genInitSt locSt = do
  initSt <- genInitSt
  lift $ evalStateT locSt initSt

-- | The state with `ST` so that there is internal carrying information in `info`
--   which may also depend on the same `ST` environment
type STReader info s = ReaderT (info s) (ST s)

-- | The delimit function to run a local STReader with different carrying information
strdrDelimit :: STReader info s (info' s) -- ^ the new context for the local reader
  -> STReader info' s a -- ^ the local reader to execute with the new context
  -> STReader info s a
strdrDelimit genCtx locRdr = do
  ctx <- genCtx
  lift $ runReaderT locRdr ctx

hashTableToMap :: (HT.HashTable h, Ord k, Hashable k) => IOHashTable h k a -> IO (M.Map k a)
hashTableToMap tab = do
  lst <- HTO.toList tab
  return $ M.fromList lst

-- class MonadST m | m -> where
--   liftST :: ST a -> m a

-- instance (Monad m, MonadST m, MonadTrans mt) => MonadST (mt m) where
--   liftST :: (Monad m, MonadST m, MonadTrans mt) => ST a -> mt m a
--   liftST = lift . liftST

type HashSet k = HTO.BasicHashTable k ()

setHas :: (Eq k, Hashable k) => HashSet k -> k -> IO Bool
setHas set key = isJust <$> HTO.lookup set key

-- | Returns whether the key is already presented
setAdd :: (Eq k, Hashable k) => HashSet k -> k -> IO Bool
setAdd set key = HTO.mutate set key $ \case
   Nothing -> (Just (), True)
   Just _  -> (Just (), False)

whenM :: Monad m => m Bool -> m () -> m ()
whenM guardM body = do
  guard <- guardM
  when guard body

popSTStack :: STRef s [a] -> ST s a
popSTStack stk = do
  ~(hd:lst) <- readSTRef stk
  writeSTRef stk lst
  return hd

popIOStack :: IORef [a] -> IO a
popIOStack stk = do
  ~(hd:lst) <- readRef stk
  stk <<- lst
  return hd

whileM :: Monad m => m Bool -> m () -> m ()
whileM mb body = do
  b <- mb
  when b $ do body; whileM mb body

mapToHashTable :: (HT.HashTable h, Eq k, Hashable k) => M.Map k v -> IO (HTO.IOHashTable h k v)
mapToHashTable map = HTO.fromList $ M.toList map

class (Monad m) => Modifiable m r | m -> r where
  newRef :: a -> m (r a)
  readRef :: r a -> m a
  writeRef :: r a -> a -> m ()
  modifyRef :: r a -> (a -> a) -> m ()
  modifyRef ref f = do
    v <- readRef ref
    writeRef ref $ f v

infixr 0 <<-
-- | The infix synonym of `writeRef`
(<<-) :: Modifiable m r => r a -> a -> m ()
(<<-) = writeRef


instance Modifiable IO IORef where
  newRef :: a -> IO (IORef a)
  newRef = newIORef
  readRef :: IORef a -> IO a
  readRef = readIORef
  writeRef :: IORef a -> a -> IO ()
  writeRef = writeIORef
  modifyRef :: IORef a -> (a -> a) -> IO ()
  modifyRef = modifyIORef'  -- strict version

instance Modifiable (ST s) (STRef s) where
  newRef :: a -> ST s (STRef s a)
  newRef = newSTRef
  readRef :: STRef s a -> ST s a
  readRef = readSTRef
  writeRef :: STRef s a -> a -> ST s ()
  writeRef = writeSTRef
  modifyRef :: STRef s a -> (a -> a) -> ST s ()
  modifyRef = modifySTRef'

-- | The mark type for reversed list
newtype RevList a = RevList [a]

instance Semigroup (RevList a) where
  (<>) :: RevList a -> RevList a -> RevList a
  (RevList as) <> (RevList as') = RevList $ as' ++ as

instance Monoid (RevList a) where
  mempty :: RevList a
  mempty = RevList []

revToList :: RevList a -> [a]
revToList (RevList lst) = reverse lst

toRevList :: [a] -> RevList a
toRevList lst = RevList $ reverse lst

class IMap m where
  type Key m
  type Val m
  insert :: m -> Key m -> Val m -> m
  containsKey :: m -> Key m -> Bool
  tryFind :: m -> Key m -> Maybe (Val m)

fstMap :: (t -> a) -> (t, b) -> (a, b)
fstMap f (a, b) = (f a, b)

fstMapM :: Functor f => (t1 -> f t2) -> (t1, t3) -> f (t2, t3)
fstMapM f (a, b) = (,b) <$> f a

sndMap :: (t -> b) -> (a, t) -> (a, b)
sndMap f (a, b) = (a, f b)

sndMapM :: Functor f => (t1 -> f t2) -> (t3, t1) -> f (t3, t2)
sndMapM f (a, b) = (a,) <$> f b

bothMap :: (t -> b) -> (t, t) -> (b, b)
bothMap f (a, b) = (f a, f b)

pairMap :: (t1 -> a, t2 -> b) -> (t1, t2) -> (a, b)
pairMap (f, g) (a, b) = (f a, g b)

anyM :: (Monad m, Foldable t1) => (t2 -> m Bool) -> t1 t2 -> m Bool
anyM f lst = evalContT $ callCC $ \exit -> do
  forM_ lst $ \e -> do
    whenM (lift $ not <$> f e) $ exit True
  return False

allM :: (Monad f, Foldable t1) => (a -> f Bool) -> t1 a -> f Bool
allM f lst = not <$> anyM (fmap not . f) lst

-- | Switch the context of `ReaderT` by running the former
rdDelimit :: (Monad m) => r -> ReaderT r m a -> ReaderT r' m a
rdDelimit init ori = lift $ runReaderT ori init

foldToLogicT :: (Monad m, Foldable t) => t a -> LogicT m a
foldToLogicT lst = LogicT $ \cons nil -> do
  nil <- nil
  foldM (flip cons . return) nil lst

newtype Flip f a b = Flip { getFlip :: f b a }

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
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# OPTIONS_GHC -Wno-redundant-constraints #-}
module Utils where
import Data.List (intercalate)
import Control.Monad.State (StateT, MonadTrans (lift), evalStateT, forM_, foldM)
import Control.Monad.ST.Strict (ST, runST)
import Control.Monad.Reader (ReaderT (runReaderT), when, MonadReader)
import qualified Data.HashTable.Class as HT
import qualified Data.Map.Strict as M
import qualified Data.HashTable.IO as HTO
import Data.Maybe (isJust)
import Data.Hashable ( Hashable )
import Data.STRef.Strict (readSTRef, writeSTRef, STRef, newSTRef, modifySTRef')
import Data.IORef (IORef, newIORef, readIORef, writeIORef, modifyIORef')
import Data.HashTable.IO (IOHashTable)
import Control.Monad.Cont (MonadCont (callCC), MonadIO (liftIO), ap)
import Control.Monad.Trans.Cont (evalContT)
import Control.Monad.Logic (LogicT(LogicT))
import qualified Data.Set as S
import GHC.Generics (Generic)
import qualified Data.HashTable.ST.Basic as HTST
import Control.Monad.Trans.Maybe (MaybeT(MaybeT))
import Control.Monad.Reader.Class (MonadReader(..))
import Control.Monad.Except (MonadError (..))

printLstContent :: Show a => [a] -> String
printLstContent lst = intercalate ", " $ fmap show lst

quoteBy :: String -> String -> String
quoteBy q str =
  let (qs, qe) = splitAt (length q `div` 2) q in
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

hashTableToMap :: (HT.HashTable h, Ord k, Hashable k, Eq k) => IOHashTable h k a -> IO (M.Map k a)
hashTableToMap tab = do
  lst <- HTO.toList tab
  return $ M.fromList lst

printTheList :: MonadIO m => [String] -> m ()
printTheList lst = liftIO $ putStrLn $ unwords lst

-- class MonadST m | m -> where
--   liftST :: ST a -> m a

-- instance (Monad m, MonadST m, MonadTrans mt) => MonadST (mt m) where
--   liftST :: (Monad m, MonadST m, MonadTrans mt) => ST a -> mt m a
--   liftST = lift . liftST

type HashSet k = HTO.BasicHashTable k ()

setHas :: ((Hashable k, Eq k)) =>HashSet k -> k -> IO Bool
setHas set key = isJust <$> HTO.lookup set key

-- | Returns whether the key is already presented
setAdd :: ((Hashable k, Eq k)) =>HashSet k -> k -> IO Bool
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

mapToHashTable :: (HT.HashTable h, Hashable k, Eq k) =>
  M.Map k v -> IO (HTO.IOHashTable h k v)
mapToHashTable map = HTO.fromList $ M.toList map

class (Monad m) => Modifiable m r | m -> r where
  newRef :: a -> m (r a)
  readRef :: r a -> m a
  writeRef :: r a -> a -> m ()
  modifyRef :: r a -> (a -> a) -> m ()
  modifyRef ref f = do
    v <- readRef ref
    writeRef ref $ f v

instance (MonadTrans t, Monad m, Modifiable m r, Monad (t m)) => Modifiable (t m) r where
  newRef :: (MonadTrans t, Monad m, Modifiable m r, Monad (t m)) =>
    a -> t m (r a)
  newRef = lift . newRef
  readRef :: (MonadTrans t, Monad m, Modifiable m r, Monad (t m)) =>
    r a -> t m a
  readRef = lift . readRef
  writeRef :: (MonadTrans t, Monad m, Modifiable m r, Monad (t m)) =>
    r a -> a -> t m ()
  writeRef r a = lift $ writeRef r a
  modifyRef :: (MonadTrans t, Monad m, Modifiable m r, Monad (t m)) =>
    r a -> (a -> a) -> t m ()
  modifyRef r f = lift $ modifyRef r f

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
  deriving (Eq, Ord, Show, Generic, Hashable)

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

instance Ord k => IMap (M.Map k v) where
  type Key (M.Map k v) = k
  type Val (M.Map k v) = v
  insert :: M.Map k v -> Key (M.Map k v) -> Val (M.Map k v) -> M.Map k v
  insert m k v = M.insert k v m
  containsKey :: M.Map k v -> Key (M.Map k v) -> Bool
  containsKey m k = isJust $ M.lookup k m
  tryFind :: M.Map k v -> Key (M.Map k v) -> Maybe (Val (M.Map k v))
  tryFind m k = M.lookup k m

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

{-| Generalised version of `any`.

>>> anyM (return . odd) [2, 4, 6]
False

>>> anyM (return . odd) [1, 2, 3]
True
-}
anyM :: (Monad m, Foldable t1) => (t2 -> m Bool) -> t1 t2 -> m Bool
anyM f lst = evalContT $ callCC $ \exit -> do
  forM_ lst $ \e -> do
    whenM (lift $ f e) $ exit True
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

toLogicT :: (Monad m, Foldable t) => t a -> LogicT m a
toLogicT = foldToLogicT


newtype Flip f a b = Flip { getFlip :: f b a }

-- | The class of addable collection accepts the whole collection and the element
class AddCol t a | t -> a where
  empty :: t
  addOne :: t -> a -> t

instance AddCol [a] a where
  empty :: [a]
  empty = []
  addOne :: [a] -> a -> [a]
  addOne = flip (:)

instance (Ord a) => AddCol (S.Set a) a where
  empty = S.empty
  addOne = flip S.insert

instance (Ord k) => AddCol (M.Map k v) (k, v) where
  empty = M.empty
  addOne m (k, v) = M.insert k v m

-- | Given a collection of (k, v) pairs, form a map M.Map k (t v) where `t` is a suitable collection
-- >>> toColMap [(1, 2), (1, 5), (2, 3), (1, 7), (2, 9)] :: M.Map Int (S.Set Int)
-- fromList [(1,fromList [2,5,7]),(2,fromList [3,9])]
-- >>> toColMap [(1, 2), (1, 5), (2, 3), (1, 7), (2, 9)] :: M.Map Int [Int]
-- fromList [(1,[7,5,2]),(2,[9,3])]
toColMap :: (Foldable f, AddCol t v, Ord k) => f (k, v) -> M.Map k t
toColMap = foldl foldFunc M.empty
  where
    adder v = \case
      Just l  -> Just $ addOne l v
      Nothing -> Just $ addOne empty v
    foldFunc m (k, v) = M.alter (adder v) k m

class ToString t where toString :: t -> String

-- | An auxiliary string type for better printing look -- non-quote
newtype NString = NString String
  deriving (Eq, Ord, Generic, Hashable)

instance Show NString where
  show :: NString -> String
  show (NString s) = s

addIndent :: Int -> String -> String -> String
addIndent n indentStr inputStr =
  unlines $ fmap (concat (replicate n indentStr) ++) (lines inputStr)

printListMap :: (t -> a -> String) -> M.Map t [a] -> String
printListMap print map =
  M.toList map
  |> fmap (uncurry $ fmap . print)  -- (\(nt, rules) -> print nt <$> rules)
  |> concat
  |> intercalate "\n"

-- | Generate a function that returns an auto-increasing function
--   It recalls the time an object is called (this function is applied to)
stAutoCallCount :: (Hashable k, Eq k, Enum a) =>ST s (k -> ST s a)
stAutoCallCount = do
  tab <- HTST.new
  return $ \o ->
    HTST.mutate tab o $ \case
      Nothing -> (Just $ toEnum 1, toEnum 0)
      Just id -> (Just $ succ id, id)

-- | The `IO` monad version of `stAutoCallCount`
ioAutoCallCount :: (Hashable k, Eq k, Enum a) =>IO (k -> IO a)
ioAutoCallCount = do
  tab <- HTO.new :: IO (HTO.BasicHashTable k v)
  return $ \o ->
    HTO.mutate tab o $ \case
      Nothing -> (Just $ toEnum 1, toEnum 0)
      Just id -> (Just $ succ id, id)

-- | Returns an `ST` monad auto numbering function that can give a unique number to the input
--   For a given fixed input, the number is the same
stAutoNumber :: (Num a, Hashable k, Eq k) => ST s (k -> ST s a)
stAutoNumber = do
  cell <- newRef 0
  tab <- HTST.new
  return $ \o ->
    HTST.mutateST tab o $ \case
      Just id -> return (Just id, id)
      Nothing -> do
        nextId <- readRef cell
        cell <<- nextId + 1
        return (Just nextId, nextId)

ioAutoNumber :: (Num a, Hashable k, Eq k) => IO (k -> IO a)
ioAutoNumber = do
  cell <- newRef 0
  tab <- HTO.new :: IO (HTO.BasicHashTable k v)
  return $ \o ->
    HTO.mutateIO tab o $ \case
      Just id -> return (Just id, id)
      Nothing -> do
        nextId <- readRef cell
        cell <<- nextId + 1
        return (Just nextId, nextId)

-- | Make the `Maybe` type become a transformer within a monad
transMaybe :: Monad m => Maybe a -> MaybeT m a
transMaybe m = MaybeT $ return m

-- | The monad to collect results
newtype ColT r m a = ColT { runColT :: m (Either r a) }

-- | The usual runner of the `ColT` monad
collectResultT :: Monad m => ColT r m r -> m r
collectResultT colT = do
  either <- runColT colT
  case either of
    Left  e -> return e
    Right e -> return e

instance Monad m => Functor (ColT r m) where
  fmap :: Functor m => (a -> b) -> ColT r m a -> ColT r m b
  fmap f (ColT m) = ColT $ fmap (fmap f) m

instance Monad m => Applicative (ColT r m) where
  pure :: Monad m => a -> ColT r m a
  pure a = ColT $ return $ return a
  (<*>) :: Monad m => ColT r m (a -> b) -> ColT r m a -> ColT r m b
  (<*>) = ap

instance Monad m => Monad (ColT r m) where
  (>>=) :: Monad m => ColT r m a -> (a -> ColT r m b) -> ColT r m b
  (ColT m) >>= f = ColT $ do
    either <- m
    case either of
      Left l  -> return $ Left l
      Right r -> runColT $ f r

instance MonadTrans (ColT r) where
  lift :: Monad m => m a -> ColT r m a
  lift m = ColT $ fmap return m

class MonadCollect r m | m -> r where
  -- | Collect the result and finish the computation
  --   The computations after are all discarded
  collect :: r -> m a

instance Monad m => MonadCollect r (ColT r m) where
  collect :: Monad m => r -> ColT r m a
  collect r = ColT $ return $ Left r

-- instance (MonadTrans t, Monad m, MonadCollect r m) => MonadCollect r (t m) where
--   collect :: (MonadTrans t, Monad m, MonadCollect r m) => r -> t m a
--   collect r = lift $ collect r

-- >>> testColRes
-- 1000
testColRes :: Int
testColRes = runST $ flip runReaderT 10 $ collectResultT $ do
  cell <- newRef (0 :: Int)
  whenM ((<= 1) <$> readRef cell) $ local (* 100) ask >>= collect
  ask

instance (MonadReader r m) => MonadReader r (ColT r' m) where
  ask :: MonadReader r m => ColT r' m r
  ask = lift ask
  local :: MonadReader r m => (r -> r) -> ColT r' m a -> ColT r' m a
  local f (ColT m) = ColT $ local f m

instance (MonadError e m) => MonadError e (ColT r m) where
  throwError :: MonadError e m => e -> ColT r m a
  throwError = lift . throwError
  catchError :: MonadError e m => ColT r m a -> (e -> ColT r m a) -> ColT r m a
  catchError (ColT m) f = ColT $ catchError m $ runColT . f



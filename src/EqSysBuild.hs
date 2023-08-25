{-# LANGUAGE Strict #-}
{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE AllowAmbiguousTypes #-}
{-# OPTIONS_GHC -Wno-name-shadowing #-}
{-# OPTIONS_GHC -Wno-partial-fields #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DeriveAnyClass #-}
{-# OPTIONS_GHC -Wno-incomplete-uni-patterns #-}
{-# LANGUAGE InstanceSigs #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE FlexibleInstances #-}
{-# OPTIONS_GHC -Wno-redundant-constraints #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# OPTIONS_GHC -Wno-incomplete-patterns #-}
module EqSysBuild (
  consDeepFsMode,
  defGetDownMap,
  defKMap,
  defFlags,
  Flags(..),
  AbsVar(..),
  BuildMode,
  BuildContext(..),
  AccStepInfo(..),
  EqSys(..),
  StdReq,
  x0Of,
  runConstruction,
  constructEqSysFromX0,
  consBreathFsMode,
  SynComp(..),
  SpOp(..)
) where
import qualified Data.Map.Strict as M
import qualified Data.HashTable.IO as HT
import Objects (Operation (..), RestrictedTreeStackAut (rtsaRules, rtsaRestriction, rtsaDefLocMem, rtsaInitSt), SpTer, SpHorizontal (SpHor), Gamma (GBot, GNorm), isBot, SpUnit, ExtendedRTSA (eRtsaAutomaton, eRtsaDownMap, eRtsaKMap))
import Control.Monad.Except (ExceptT, MonadError (catchError, throwError), MonadTrans (lift), runExceptT)
import Control.Monad.State.Strict (StateT, gets, modify, evalStateT)
import Control.Monad.Reader (ReaderT (runReaderT), asks)
import Control.Monad.IO.Class (liftIO)
import qualified MData.LoopQueue as Q
import Utils (setAdd, whenM, setHas, HashSet, whileM, mapToHashTable, Modifiable (..), (<<-), (|>), RevList (RevList), revToList, sndMap)
import Control.Monad ( foldM, forM_, void, when)
import Data.Maybe (fromMaybe)
import Data.Hashable ( Hashable(hash) )
import GHC.Generics (Generic)
import Control.Monad.Cont (MonadCont (callCC))
import Control.Monad.Trans.Cont ( ContT, evalContT, shiftT )
import Data.IORef (IORef)
import qualified MData.Stack as S
import qualified Data.Set as Set

type Queue = Q.IOLoopQueue
type Stack = S.IODefStack


-- This file defines an abstract general method to build the equation system for rTSA
-- The main procedure of this program, using `IO`


-- | The abstract variable, of information `length`, `D` and `gamma`
data AbsVar q g = AbsVar Int [q] (Gamma g)
  deriving (Show, Eq, Ord, Generic, Hashable)
-- | Not possible to go for `GBot`, special version of `AbsVar`
data UpNodeVar q g = UpNodeVar Int [q] g
  deriving (Show, Eq, Ord, Generic, Hashable)

toAbsVar :: UpNodeVar q g -> AbsVar q g
toAbsVar (UpNodeVar n qs g) = AbsVar n qs $ GNorm g

-- | Whether the abstract variable is an `up` variable
isUp :: AbsVar q g -> Bool
isUp (AbsVar len _ _) = odd len

data BuildResult
  = BRStructuralZero
  | BRDfsRecursive
  | BRNormal
  | BRBfsUnknown
  | BRBfsInQueue
  | BRReTravelNormal
  | BRReTravUnencountered
  deriving (Eq)

data BuildMode q g acc
  = BMDeepFirst
    { dfsPathSet :: HT.BasicHashTable (AbsVar q g) ()
    , dfsVarStk :: Stack (AbsVar q g, [InSynComp q g acc]) }
  | BMBreadthFirst
    { bfsQueue :: Queue (AbsVar q g) }
  | BMRetraverse (HT.BasicHashTable (AbsVar q g) ()) (Queue (AbsVar q g))

data BuildInfo q m g acc = BuildInfo
  { curState :: q
  , curLocMem :: m
  , curGamma :: Gamma g
  , curDepth :: Word
  , curD :: [q]
  , accInfo :: acc
  -- | The `D` list here is REVERSED!
  , upRevMap :: M.Map g (RevList q, Int) }

class (Monoid acc) => AccStepInfo acc g | acc -> g where
  -- | acc <> \Down with implicit \Down
  mappendDownMark :: acc -> acc
  -- | acc <> \Up{g} with direction g
  mappendUpMark :: acc -> g -> acc

data BuildExcept q g
  = EVarMark (AbsVar q g)
  | EMessage String
  deriving (Show)

data Flags = Flags
  { reportStuck :: Bool
  , noUpVar :: Bool
  , reportUnencountered :: Bool
  , recordAlsoFoundZeroVar :: Bool }

data InSynComp q g acc = InSynComp acc [AbsVar q g]

data BuildContext q m g sp acc = BuildContext
  -- the rTSA stuff
  { rules :: HT.BasicHashTable (q, m, Gamma g) [(acc, Operation q m g sp)]
  , kNum :: Int
  , defLocMem :: m
  -- require external rTSA analysis
  , downPredictMap :: HT.BasicHashTable (q, g) [q]
  , kMap :: HT.BasicHashTable g Int
  -- with ONLY default value -- internal structure
  , cacheResults :: HT.BasicHashTable (AbsVar q g) BuildResult
  , vaccumTrips :: HT.BasicHashTable (AbsVar q g) ()
  , exploredCount :: IORef Integer
  , results :: IORef [(AbsVar q g, [InSynComp q g acc])]
  , curEqRHS :: IORef [InSynComp q g acc]
  -- require separate external information
  , buildMode :: BuildMode q g acc
  , flags :: Flags }

data BuildMessage q m g
  = BMsgStuckStat (q, m, g)
  | BMsgDepth Word
  | BMsgNewVar (AbsVar q g)
  | BMsgExploredVarAmount Int
  | BMsgUnencountered (AbsVar q g)
  deriving (Show)

-- | A lesson: NO NEED TO re-implement the stuff to get rid of multiple-level `lift`
-- The stuff will be automatically pass down to the right `Monad` along the `MonadTrans` chain
-- So, directly call `ask` will return the `BuildContext`, no need to use `lift ask`.
-- And the error handling can also be directly done by `catchError` and `throwError`.
-- Using `liftIO` can directly access the internal ST information.

-- newtype 
type
  BuildState q m g sp acc a =
  -- BuildState { runBuildState :: 
      StateT (BuildInfo q m g acc) (CtxState q m g sp acc) a
  -- }
  -- deriving (Functor, Applicative, Monad)

type CtxState q m g sp acc =
  ReaderT (BuildContext q m g sp acc) (
      ExceptT (BuildExcept q g) IO
  )

-- -- | The specialised context for actual customisation
-- data SpecialisedContext q m g sp acc = SpecialisedContext
--   { updateStepAccInfo :: info -> BuildState q m g sp acc ()
--   , signalNewVar :: AbsVar q g -> CtxState q m g sp acc ()
--   , genInitAccInfo :: AbsVar q g -> CtxState q m g sp acc acc
--   , notifyUpVars :: [AbsVar q g] -> BuildState q m g sp acc ()
--   , buildTopVar :: CtxState q m g sp acc ()
--   , notifyDown :: BuildState q m g sp acc ()
--   , notifyUp :: g -> BuildState q m g sp acc () }

-- | Shorthand for various STandarD constraints REQuirements the status `q`, `m` and `g` and `acc`
--   should satisfy when appear in the constraints
class (Eq q
      , Ord g
      , Hashable q
      , Eq m
      , Hashable m
      , Hashable g
      , Show q
      , Show m
      , Show g
      , AccStepInfo acc g) =>
  StdReq q m g acc

instance (Eq q
      , Ord g
      , Hashable q
      , Eq m
      , Hashable m
      , Hashable g
      , Show q
      , Show m
      , Show g
      , AccStepInfo acc g) =>
  StdReq q m g acc

-- -- | This is to test that from a generator function
-- --   it is possible to create a stuff like a class.
-- --   So the function likes to generate a function satisfying the interface.

-- data TestLiftContext q m g sp acc = TestLiftContext
--   { testPlus :: BuildState q m g sp acc ()
--   , testTake :: BuildState q m g sp acc Int }

-- testLiftCtx :: ST (TestLiftContext q m g sp acc)
-- testLiftCtx = do
--   -- internal fields
--   cell <- newRef 0
--   -- constructor
--   return $ TestLiftContext (addCell cell) (getCell cell)
--   where
--     -- implementation functions
--     addCell cell = liftIO $ modifyRef cell (+1)
--     getCell cell = liftIO $ readRef cell

-- instance MonadState (BuildInfo q m g acc) (BuildState q m g sp acc) where
--   get :: BuildState q m g sp acc (BuildInfo q m g acc)
--   get = BuildState get
--   put :: BuildInfo q m g acc -> BuildState q m g sp acc ()
--   put = BuildState (put s)

-- instance MonadReader (BuildContext q m g info sp) (BuildState q m g sp acc) where
--   ask :: BuildState q m g sp acc (BuildContext q m g info sp)
--   ask = BuildState ask
--   local :: (BuildContext q m g info sp -> BuildContext q m g info sp)
--     -> BuildState q m g sp acc a
--     -> BuildState q m g sp acc a
--   local f (BuildState m) = BuildState (mapStateT (local f) m)

-- instance MonadError (BuildExcept q g) (BuildState q m g sp acc) where
--   throwError :: BuildExcept q g -> BuildState q m g sp acc a
--   throwError e = BuildState $ throwError e
--   catchError :: BuildState q m g sp acc a
--     -> (BuildExcept q g -> BuildState q m g sp acc a)
--     -> BuildState q m g sp acc a
--   catchError (BuildState m) f = BuildState (catchError m (runBuildState . f))


-- --------------------------- Aux Functions ---------------------------

recordVaccumVar :: (Eq q, Eq g, Hashable q, Hashable g) =>
  AbsVar q g -> BuildState q m g sp acc ()
recordVaccumVar var
  | isUp var  = return ()
  | otherwise = do
    vacSet <- asks vaccumTrips
    liftIO $ void $ setAdd vacSet var

possibleDowns :: (Eq q, Eq g, Hashable q, Hashable g) =>
  q -> g -> BuildState q m g sp acc [q]
possibleDowns q g = do
  downs <- asks downPredictMap
  liftIO $ fromMaybe [] <$> HT.lookup downs (q, g)

curStatus :: BuildInfo q m g acc -> (q, m, Gamma g)
curStatus info = (curState info, curLocMem info, curGamma info)

getUpRevD :: Ord g => g -> BuildState q m g sp acc (RevList q, Int)
getUpRevD g = do
  map <- gets upRevMap
  case map M.!? g of
    Nothing -> return (RevList [], 0)
    Just upD -> return upD

notLoggedVaccumVar :: (Eq q, Eq g, Hashable q, Hashable g) =>
  AbsVar q g -> BuildState q m g sp acc Bool
notLoggedVaccumVar var = do
  cache <- asks cacheResults
  res <- liftIO $ HT.lookup cache var
  case res of
    Just BRStructuralZero -> return False
    _otherwise -> if isUp var then return True else do
      vaccumTrips <- asks vaccumTrips
      liftIO $ vaccumTrips `setHas` var

notOverK :: (Hashable g, Eq g) => Int -> g -> BuildState q m g sp acc Bool
notOverK len g = do
  maybeGk <- asks kMap >>= \map -> liftIO $ HT.lookup map g
  globalK <- asks kNum
  let gk = fromMaybe globalK maybeGk
  return $ (len + 1) `div` 2 <= gk

catchPossibleVaccumVar :: (Hashable q, Hashable g, Eq q, Eq g) =>
  AbsVar q g
  -> Int
  -> BuildState q m g sp acc ()
  -> BuildState q m g sp acc ()
catchPossibleVaccumVar tgVar hashCode execBody =
  catchError execBody $ \case  -- error handling
    EVarMark av -> if hashCode == hash av && tgVar == av
                      then recordVaccumVar tgVar
                      else throwError $ EVarMark av
    otherError  -> throwError otherError

remapRevUpMap :: Ord g => g -> (RevList q, Int) -> BuildState q m g sp acc ()
remapRevUpMap g newVal =
  modify $ \info -> do
    let revUpMap = upRevMap info
    info { upRevMap = M.insert g newVal revUpMap }

logAndAddDepth :: BuildState q m g sp acc ()
logAndAddDepth = do
  depth <- gets curDepth
  liftIO $ print (BMsgDepth depth :: BuildMessage Int Int Int)
  modify $ \info -> info { curDepth = depth + 1 }

updateAccInfo :: (StdReq q m g acc) => acc -> BuildState q m g sp acc ()
updateAccInfo stepInfo = modify $ \info -> info { accInfo = accInfo info `mappend` stepInfo }

class SpOp sp where
  copeSp :: (StdReq q m g acc) => sp q m g -> BuildState q m g sp acc ()

-- Some Standard Separate Special Operators

instance SpOp SpUnit where
  copeSp :: StdReq q m g acc => SpUnit q m g -> BuildState q m g SpUnit acc ()
  copeSp _ = return ()

instance SpOp SpTer where
  copeSp :: StdReq q m g acc => SpTer q m g -> BuildState q m g SpTer acc ()
  copeSp _ = whenM (gets $ null . curD) $ dispatchUpwardCompute Nothing

instance SpOp SpHorizontal where
  copeSp :: StdReq q m g acc =>
    SpHorizontal q m g -> BuildState q m g SpHorizontal acc ()
  copeSp (SpHor q') = do
    modify $ \info -> info { curState = q' }


-- --------------------------- The Building Functions ---------------------------

traverseAndBuild :: (SpOp sp, StdReq q m g acc) =>
  BuildState q m g sp acc ()
traverseAndBuild = do {
  status <- gets curStatus;
  rulesMap <- asks rules;
  rules <- liftIO $ fromMaybe [] <$> HT.lookup rulesMap status;
  -- Report Stuck if required
  whenM (asks ((null rules &&) . reportStuck . flags)) $
    liftIO $ print $ BMsgStuckStat status;
  -- Traverse for each rule
  forM_ rules $ \(stepInfo, op) -> do {
    logAndAddDepth;
    updateAccInfo stepInfo;
    case op of
      OpUp q m g -> copeUp q m g
      OpDown q m -> copeDown q m
      OpSp sp    -> copeSp sp
  }
}


recordUpdate :: [UpNodeVar q g] -> BuildState q m g sp acc ()
recordUpdate upNodesVars = do
  acc <- gets accInfo
  let newInSynComp = InSynComp acc $ fmap toAbsVar upNodesVars
  rhsCell <- asks curEqRHS
  liftIO $ modifyRef rhsCell (newInSynComp:)


dispatchUpwardCompute :: (Ord g, SpOp sp, StdReq q m g acc) =>
  Maybe (UpNodeVar q g)
  -> BuildState q m g sp acc ()
dispatchUpwardCompute maybeNewUpVar = do
  -- the list of up variables in the up map with the `maybeNewUpVar` for the target direction
  upNodesVars <- fmap (toUpNodeVar maybeNewUpVar) . M.toList <$> gets upRevMap
  -- iterate to check if they are all non-zero
  forM_ upNodesVars checkNonZeroVar
  -- update the current RHS with the new RHS
  recordUpdate upNodesVars

toUpNodeVar :: Eq g => Maybe (UpNodeVar q g) -> (g, (RevList q, Int)) -> UpNodeVar q g
toUpNodeVar maybeNewUpVar (g, (revD, lenD)) =
  let var = UpNodeVar lenD (revToList revD) g in
  case maybeNewUpVar of
    Nothing -> var
    -- It is never possible to get up to GBot
    Just v@(UpNodeVar _ _ g') -> if g == g' then v else var

checkNonZeroVar :: (SpOp sp, StdReq q m g acc) =>
  UpNodeVar q g -> BuildState q m g sp acc ()
checkNonZeroVar var = do
  var <- return $ toAbsVar var
  res <- lift $ buildVarAndDependentVars var
  case res of
    BRStructuralZero -> throwError $ EVarMark var
    _otherwise       -> return ()


copeUp :: (SpOp sp, StdReq q m g acc) =>
  q -> m -> g -> BuildState q m g sp acc ()
copeUp uq nm tg = do
  trySingularUp uq tg
  tryUpThenDown uq nm tg


okForSingularUpVar :: (Ord g, Eq q, Hashable q, Hashable g) =>
  UpNodeVar q g -> BuildState q m g sp acc Bool
okForSingularUpVar tgVar@(UpNodeVar tgLen _ tg) = do
  foldM (\x y -> do y <- y; return $ x && y) True
    -- the actual conditions
    [ null <$> gets curD  -- D == []
    , asks $ not . noUpVar . flags  -- NOT `noUpVar`
    , notLoggedVaccumVar $ toAbsVar tgVar  -- NOT already computed variable which has shown to be empty
    , notOverK tgLen tg ]


trySingularUp :: (SpOp sp, StdReq q m g acc) =>
  q -> g -> BuildState q m g sp acc ()
trySingularUp uq tg = do
  -- vars intialisations
  (RevList tgD, tgLenD) <- getUpRevD tg
  let tgVar    = UpNodeVar (tgLenD + 1) (reverse $ uq : tgD) tg
      hashCode = hash tgVar
      absVar   = toAbsVar tgVar

  -- The actual work, guarded by `okForSingularUpVar`
  whenM (okForSingularUpVar tgVar) $ do

    -- notify `up` going to direction `tg`
    modify $ \info -> info { accInfo = mappendUpMark (accInfo info) tg }

    -- The actual work to do -- to dispatch and to log the vaccum vars
    -- the `catch` body
    catchPossibleVaccumVar absVar hashCode $
      dispatchUpwardCompute $ Just tgVar


tryUpThenDown :: (SpOp sp, StdReq q m g acc) =>
  q -> m -> g -> BuildState q m g sp acc ()
tryUpThenDown uq nm tg = do
  -- vars initialisation
  downs <- possibleDowns uq tg
  -- `qc` for `q`-continue
  forM_ downs $ \qc -> do
    (RevList revTgDLst, tgLenD) <- getUpRevD tg
    let newRevTgD = RevList $ qc : uq : revTgDLst
        newTgLenD = tgLenD + 2
        tgVar = AbsVar newTgLenD (revToList newRevTgD) $ GNorm tg
        hashCode = hash tgVar

    -- When it is OK, continue traversing by the predicted `qc`
    whenM ((&&) <$> notLoggedVaccumVar tgVar <*> notOverK tgLenD tg) $ do

      -- update the `info` with new `upRevMap`
      remapRevUpMap tg (newRevTgD, newTgLenD)
      -- update `q` and `m`
      modify $ \info -> info { curState = qc, curLocMem = nm }
      -- continue traversing
      catchPossibleVaccumVar tgVar hashCode traverseAndBuild


copeDown :: (SpOp sp, StdReq q m g acc) =>
  q -> m -> BuildState q m g sp acc ()
copeDown q m' = gets curD >>= internalCopeDown q m'
  where
    internalCopeDown q nm dLst
      | null dLst = do
        curGamma <- gets curGamma
        -- To get `down` from bottom is equivalent to termination
        when (isBot curGamma) $ dispatchUpwardCompute Nothing
      | head dLst == q = case tail dLst of
        [] -> dispatchUpwardCompute Nothing
        nq : nD -> do {
          -- execute `notifyDown`
          modify $ \info -> info { accInfo = mappendDownMark $ accInfo info };
          -- update q m D
          modify $ \info -> info
            { curState = nq
            , curLocMem = nm
            , curD = nD };
          -- continue traversing from the current information
          traverseAndBuild
        }
      | otherwise = return ()

-- | build the variable and dependent variables
buildVarAndDependentVars ::
  (SpOp sp, StdReq q m g acc) =>
  AbsVar q g -> CtxState q m g sp acc BuildResult
buildVarAndDependentVars var = asks buildMode >>= \case
  BMDeepFirst pathSet envStk -> dfsBuildVar var pathSet envStk
  BMBreadthFirst todo        -> bfsBuildVar var todo
  BMRetraverse explored todo -> reTravBuildVar var explored todo
  -- DEBUG: DO NOT GO FOR CACHE HERE -- as it will ignore re-traversing
  -- do
  -- maybeResult <- findCache var
  -- case maybeResult of
  --   Just res -> return res
  --   Nothing  -> goToBuildVar var

findCache :: (Eq q, Eq g, Hashable q, Hashable g) =>
  AbsVar q g -> CtxState q m g sp acc (Maybe BuildResult)
findCache var = do
  cache <- asks cacheResults
  liftIO $ HT.lookup cache var

bfsBuildVar :: (Eq q, Eq g, Hashable q, Hashable g) => AbsVar q g
  -> Queue (AbsVar q g)
  -> CtxState q m g sp acc BuildResult
bfsBuildVar var todoQueue = findCache var >>= \case
  Just res -> return res
  Nothing -> do
    -- just enqueue the variable
    liftIO $ Q.enqueue todoQueue var
    return BRBfsInQueue

reTravBuildVar :: (Eq q, Hashable q, Hashable g, Ord g, Show q, Show m, Show g) =>
  AbsVar q g
  -> HT.BasicHashTable (AbsVar q g) ()
  -> Queue (AbsVar q g)
  -> CtxState q m g sp acc BuildResult
reTravBuildVar var explored todo = findCache var >>= \case
  Just res -> if res == BRStructuralZero then return res else do
    liftIO $ whenM (explored `setAdd` var) $ Q.enqueue todo var
    return BRReTravelNormal
  Nothing -> do
    {-
      If not exists, it should mean that the variable is not relevant to the initial variable,
      in the way that: it is multiplying with a Structually Zero variable.
      So, just return a placeholder and no need to explore this variable.
    -}
    whenM (asks $ reportUnencountered . flags) $
      liftIO $ print $ (BMsgUnencountered :: AbsVar q g -> BuildMessage q Int g) var
    return BRReTravUnencountered


saveAndRecoverCurRHS ::
  Stack (AbsVar q g, [InSynComp q g acc])
  -> ContT BuildResult (CtxState q m g sp acc) ()
saveAndRecoverCurRHS envStk = shiftT $ \rest -> do {
  -- get the cell / pointer
  rhsCell <- asks curEqRHS;
  -- get the RHS from cell and save
  curRHS <- liftIO $ readRef rhsCell;
  ~(Just (var, _)) <- liftIO $ S.pop envStk;
  liftIO $ S.push envStk (var, curRHS);
  -- liftIO $ modifyRef envStk $ \ ~((var, _) : lst) -> (var, curRHS) : lst;

  -- get the return value
  r <- lift $ rest ();

  -- write the RHS back to the cell
  ~(Just (_, preRHS)) <- liftIO $ S.top envStk;
  liftIO $ rhsCell <<- preRHS;

  -- actually return the value
  return r
}


dfsBuildVar :: (Ord g, SpOp sp, StdReq q m g acc) =>
  AbsVar q g
  -> HashSet (AbsVar q g)
  -> Stack (AbsVar q g, [InSynComp q g acc])
  -> CtxState q m g sp acc BuildResult
dfsBuildVar var pathSet envStk = evalContT $ callCC $ \resultIn -> do
  -- if it is `Just`, return the cached value
  maybeRes <- lift $ findCache var
  forM_ maybeRes resultIn

  -- try to add to path set and then delete it
  shiftT $ \rest -> do
    whenM (liftIO $ fmap not $ pathSet `setAdd` var) $ resultIn BRDfsRecursive
    r <- lift $ rest ()
    liftIO $ HT.delete pathSet var
    return r
  -- save and release the current stack enviroment to the current top variable
  saveAndRecoverCurRHS envStk

  -- create a new environment
  asks curEqRHS >>= liftIO . flip writeRef []
  -- push the new variable to the top of the envStk
  liftIO $ S.push envStk (var, [])

  -- Do the concrete job
  isSz <- lift $ buildVar var

  -- The ending operations, pop the stack, record the information to cache and then return
  let topVarRes = if isSz then BRStructuralZero else BRNormal
  lift $ addToCache var topVarRes
  return topVarRes




addToCache :: (Eq q, Eq g, Hashable q, Hashable g) =>
  AbsVar q g -> BuildResult -> CtxState q m g sp acc ()
addToCache var res = do
  cache <- asks cacheResults
  liftIO $ HT.insert cache var res


-- | Do the core var-building job, build the new given variable, 
--   and then append the equation of it
--   to the result
--  
--   returns whether it is Structurally Zero
buildVar :: (SpOp sp, StdReq q m g acc) =>
  AbsVar q g -> CtxState q m g sp acc Bool
buildVar var = do
  logNewVar var
  initInfo <- genInitInfo var
  -- Refresh the RHS cell
  rhsCell <- asks curEqRHS
  liftIO $ rhsCell <<- []
  -- Traverse and build, which accumulates results to the `rhsCell`
  evalStateT traverseAndBuild initInfo
  -- Get the RHS and then append the equation of `var` to the result
  rhs <- liftIO $ readRef rhsCell
  resCell <- asks results
  whenM (okToAppendToResult rhs) $ liftIO $ modifyRef resCell ((var, rhs):)
  return $ not $ null rhs
  where
    okToAppendToResult rhs =
      asks ((not (null rhs) ||) . (recordAlsoFoundZeroVar . flags))

-- | Do some logging jobs
logNewVar :: (Show q, Show g) => AbsVar q g -> CtxState q m g sp acc ()
logNewVar var = do
  countCell <- asks exploredCount
  varAmount <- liftIO $ readRef countCell
  liftIO $ print $ (BMsgNewVar :: AbsVar q g -> BuildMessage q Int g) var
  liftIO $ print (BMsgExploredVarAmount $ fromInteger varAmount :: BuildMessage Int Int Int)
  liftIO $ modifyRef countCell (+1)


genInitInfo :: (StdReq q m g acc) =>
  AbsVar q g -> CtxState q m g sp acc (BuildInfo q m g acc)
genInitInfo (AbsVar _ ~(q1:dLst) g) = do
  m0 <- asks defLocMem
  let initAcc = mempty
  return $ BuildInfo
    { curState = q1
    , curLocMem = m0
    , curGamma = g
    , curDepth = 0
    , curD = dLst
    , accInfo = initAcc
    , upRevMap = M.empty }


initReTravBuildVar :: (SpOp sp, StdReq q m g acc) =>AbsVar q g
  -> HashSet (AbsVar q g)
  -> Queue (AbsVar q g)
  -> CtxState q m g sp acc BuildResult
initReTravBuildVar initVar explored todo = do
  void $ liftIO $ explored `setAdd` initVar
  buildWithTodo initVar todo $ \var -> do
    void $ buildVar var
    fromMaybe BRReTravUnencountered <$> findCache var


initBfsBuildVar :: (SpOp sp, StdReq q m g acc) =>
  AbsVar q g
  -> Queue (AbsVar q g)
  -> CtxState q m g sp acc BuildResult
initBfsBuildVar var todo =
  buildWithTodo var todo $ \var -> do
    hasUpdate <- buildVar var
    -- When in BFS mode, it is unknown whether it is structurally zero
    let varRes = if not hasUpdate then BRBfsUnknown else BRStructuralZero
    addToCache var varRes
    return varRes


buildWithTodo :: (Hashable g, Hashable q, Ord g, Eq q) =>
  AbsVar q g
  -> Queue (AbsVar q g)
  -> (AbsVar q g -> CtxState q m g sp acc BuildResult)
  -> CtxState q m g sp acc BuildResult
buildWithTodo var todo actualCompute = do
  liftIO $ Q.enqueue todo var
  finalCell <- liftIO $ newRef BRNormal
  whileM (liftIO $ not <$> Q.isEmpty todo) $ do {
    ~(Just var) <- liftIO $ Q.dequeue todo;
    res <- actualCompute var;
    addToCache var res
  }
  liftIO $ readRef finalCell


-- | The start point of the construction procedure, accepting the target x0 variable
entryBuildVarAndDependentVars ::
  (SpOp sp, StdReq q m g acc) =>
  AbsVar q g -> CtxState q m g sp acc BuildResult
entryBuildVarAndDependentVars var = asks buildMode >>= \case
  BMDeepFirst pathSet envStk -> dfsBuildVar var pathSet envStk
  BMBreadthFirst todo        -> initBfsBuildVar var todo
  BMRetraverse explored todo -> initReTravBuildVar var explored todo

-- The default setting for `Flags`
defFlags :: Flags
defFlags = Flags
  { reportStuck = False
  , noUpVar = False
  , reportUnencountered = False
  , recordAlsoFoundZeroVar = True }

-- The default empty `kMap`
defKMap :: M.Map g Int
defKMap = M.empty

{-| The default `downMap` building function

The default algorithm is given by analysing the rules in the following way:
- If there is a rule (_, _, g) -> (q', _, down),
  then from direction `g`, state `q'` is possible
- If there is a rule (_, _, _) -> (q', _, `up_{g'}`),
  then there is a query `(q', g')` in the downMap

So, the map is given by:

> { (q', g') |-> gMap(g') | (q', g') <- queries }

-}
defGetDownMap :: (Ord q, Ord g) =>
  RestrictedTreeStackAut q m g info sp -> M.Map (q, g) [q]
defGetDownMap rtsa =
  rtsaRules rtsa
  |> M.toList
  |> foldl folder (M.empty, M.empty)
  |> (\(allQueries, gMap) ->
        flip M.mapMaybeWithKey allQueries $ \(_, g) _ -> Set.toList <$> gMap M.!? g)
  where
    folder pair ((_, _, g), ruleList) = foldl (innerFolder g) pair ruleList
    innerFolder g pair@(qs, gMap) (_, op) = case op of
      OpUp q' _ g' -> (M.insert (q', g') () qs, gMap)
      OpDown q' _  -> case g of GBot -> (qs, gMap); GNorm g -> (qs, addToSet gMap g q')
      OpSp _       -> pair
    addToSet map k e = M.alter (return . Set.insert e . fromMaybe Set.empty) k map

-- Construct the DFS `BuildMode`
consDeepFsMode :: IO (BuildMode q g acc)
consDeepFsMode = do
  pathSet <- HT.new
  varStkCell <- S.new
  return $ BMDeepFirst
    { dfsPathSet = pathSet
    , dfsVarStk = varStkCell }

-- Construct the BFS `BuildMode`
consBreathFsMode :: IO (BuildMode q g acc)
consBreathFsMode = do
  queue <- Q.new
  return $ BMBreadthFirst { bfsQueue = queue }

{-| The default way to construct the `BuildContext`, just accpet the rTSA, with the following default settings:

- DFS Searching
- Has `Up` Variables
-}
defGetBuildContext ::
  (StdReq q m g acc, Ord q) =>
  ExtendedRTSA q m g acc sp
  -> IO (BuildContext q m g sp acc)
defGetBuildContext eRtsa = do
  let rtsa = eRtsaAutomaton eRtsa
  rules <- mapToHashTable $ M.map Set.toList $ rtsaRules rtsa
  downMap <- eRtsaDownMap eRtsa
             |> fmap (M.map Set.toList)
             |> fromMaybe (defGetDownMap rtsa)
             |> mapToHashTable
  kMap <- eRtsaKMap eRtsa
          |> fromMaybe defKMap
          |> mapToHashTable
  newCache <- HT.new
  newVacTrips <- HT.new
  counterCell <- newRef 0
  resCell <- newRef []
  stkCell <- newRef []
  mode <- consDeepFsMode
  return $ BuildContext
    { rules = rules
    , kNum = rtsaRestriction rtsa
    , defLocMem = rtsaDefLocMem rtsa
    , downPredictMap = downMap
    , kMap = kMap
    , cacheResults = newCache
    , vaccumTrips = newVacTrips
    , curEqRHS = stkCell
    , results = resCell
    , exploredCount = counterCell
    , buildMode = mode
    , flags = defFlags }

-- | The `x0` Up variable to start construction
x0Of :: RestrictedTreeStackAut q m g info sp -> AbsVar q g
x0Of rtsa = AbsVar 1 [rtsaInitSt rtsa] GBot

newtype SynComp v acc = SynComp (acc, [v])

newtype EqSys v acc = EqSys [(v, [SynComp v acc])]

internalSynCompToSynComp :: InSynComp q g acc -> SynComp (AbsVar q g) acc
internalSynCompToSynComp (InSynComp acc vars) = SynComp (acc, vars)

runConstruction :: (SpOp sp, StdReq q m g acc) =>
  BuildContext q m g sp acc
  -> AbsVar q g
  -> IO (EqSys (AbsVar q g) acc)
runConstruction ctx x0 = do
  either <- runExceptT $ runReaderT (entryBuildVarAndDependentVars x0) ctx
  case either of
    Left be -> error $ show be
    Right br -> case br of
      BRNormal -> getResult ctx
      BRStructuralZero -> return $ EqSys [(x0, [])]
      BRDfsRecursive -> error "IMPOSSIBLE RESULT: Recursive should not appear as the final result."
      BRBfsUnknown -> getResult ctx
      BRBfsInQueue -> error "IMPOSSIBLE RESULT: In-queue should not appear as the final result."
      BRReTravelNormal -> getResult ctx
      BRReTravUnencountered -> error "Re-Travel Error: the Unencountered should not be for x0."
  where
    getResult ctx = do
      lst <- readRef $ results ctx
      return $ EqSys $ fmap (sndMap $ fmap internalSynCompToSynComp) lst

constructEqSysFromX0 ::
  (StdReq q m g acc, SpOp sp, Ord q) =>
  ExtendedRTSA q m g acc sp
  -> IO (EqSys (AbsVar q g) acc)
constructEqSysFromX0 rtsa = do
  ctx <- defGetBuildContext rtsa
  let x0 = x0Of $ eRtsaAutomaton rtsa
  runConstruction ctx x0

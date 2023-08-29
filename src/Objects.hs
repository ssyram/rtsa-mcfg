{-# LANGUAGE InstanceSigs #-}
{-# LANGUAGE Strict #-}
{-# LANGUAGE DeriveGeneric #-}
{-# OPTIONS_GHC -Wno-redundant-constraints #-}
{-# OPTIONS_GHC -Wno-name-shadowing #-}
{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE CPP #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE LambdaCase #-}
{-# OPTIONS_GHC -Wno-deriving-defaults #-}
module Objects where

#define STD_DER deriving (Eq, Ord, Show, Generic, Hashable)

import qualified Data.Map as M
import Utils (
  printLstContent,
  quoteBy,
  (|>),
  fstMap,
  IMap (containsKey),
  foldToLogicT,
  addIndent,
  printListMap, transMaybe, Modifiable (newRef, readRef), (<<-), whenM)
import Data.List (intercalate)
import Data.Hashable (Hashable)
import GHC.Generics (Generic)
import Control.Monad.Trans.Except (runExceptT)
import Control.Monad (when, forM_)
import Control.Monad.Except (MonadError(throwError), MonadTrans (lift))
import Control.Monad.ST.Strict (runST)
import Data.Foldable (find)
import qualified Data.Set as S
import Data.Maybe (isJust, fromJust)
import Control.Monad.Logic (observeAllT)
import Control.Monad.Trans.Maybe (MaybeT(..))
import qualified Data.HashTable.ST.Basic as HT
import Control.Monad.ST.Class (MonadST(..))

data Symbol t
  = STerminal t
  | SVar (Int, Int)  -- Only represent the place of the variable
  deriving (Eq, Ord, Generic, Hashable)

showSym :: Show a => ((Int, Int) -> String) -> Symbol a -> String
showSym varMap (SVar vIdx) = varMap vIdx
showSym _ (STerminal t) = "`" ++ show t ++ "`"

-- instance (Show t) => Show (Symbol t) where
--   show :: (Show t, Show v) => Symbol t v -> String
--   show (STerminal t) = "`" ++ show t ++ "`"
--   show (SVar v) = show v

newtype Term t = Term [Symbol t]
  deriving (Eq, Ord, Generic, Hashable)

-- instance (Show t) => Show (Term t) where
--   show :: (Show t, Show v) => Term t -> String
--   show (Term syms) = unwords $ fmap show syms

showTermByVarMap :: Show a => ((Int, Int) -> String) -> Term a -> String
showTermByVarMap varMap (Term lst) = unwords $ showSym varMap <$> lst

showTerm :: (Show a, Show v) => [LocVarDecl nt v] -> Term a -> String
showTerm rhs = showTermByVarMap (genVarMap rhs)
  where genVarMap rhs (f, s) = let (LocVarDecl (_, lst)) = rhs !! f in show $ lst !! s

newtype LocVarDecl nt v = LocVarDecl (nt, [v])
  deriving (Eq, Ord, Generic, Hashable)

instance (Show nt, Show v) => Show (LocVarDecl nt v) where
  show :: (Show nt, Show v) => LocVarDecl nt v -> String
  show (LocVarDecl (nt, vs)) =
    unwords
    [ show nt
    , quoteBy "()" $ printLstContent vs ]

-- | _ (t1, ..., tn) <- NT1 (v11, ..., v1n1), ..., NTm (vm1, ..., vmnm)
--   `Rule` `nt` `t` `v`
data Rule nt t v = Rule
  { lhs :: [Term t]
  , rhs :: [LocVarDecl nt v] }
  deriving (Eq, Ord, Generic, Hashable)

instance (Show nt, Show t, Show v) => Show (Rule nt t v) where
  show :: (Show nt, Show t, Show v) => Rule nt t v -> String
  show (Rule lhs rhs) = unwords
    [ fmap (showTerm rhs) lhs
      |> intercalate ", "
      |> quoteBy "()"
    , "<-"
    , printLstContent rhs
    ]

{-| A Multiple Context-Free Grammar is a tuple (`N`, `\\Sigma`, `R`, `S`) where:
- `N` is the set of non-terminals
- `\\Sigma` is the set of terminals called the "alphabet"
- `R` is the set of rules of form:
  NT (t1, ..., tn) <- NT1 (v11, ..., v1n1), ..., NTm (vm1, ..., vmnm)
- `S` in `N` is the initial non-terminal

In the type:
  `nt` for the type of non-terminals,
  `t` for the type of terminals,
  `v` for the type of variables.
So, the data structure is just the set of rules (as a map for the LHS non-terminals) 
and the starting non-terminal.
-}
data MultiCtxFreeGrammar nt t v = MultiCtxFreeGrammar
  { mcfgRules :: M.Map nt [Rule nt t v]
  , mcfgStartNonTer :: nt
  }

instance (Show nt, Show t, Show v) =>
  Show (MultiCtxFreeGrammar nt t v) where
  show :: (Show nt, Show t, Show v) => MultiCtxFreeGrammar nt t v -> String
  show (MultiCtxFreeGrammar map nt) =
    intercalate "\n"
    [ "MCFG {"
    , "  Rules: ["
    , printListMap (\nt r -> "    " ++ show nt ++ " " ++ show r ++ ".") map
    , "  ],"
    , "  Starting Non-Terminal: " ++ show nt
    , "}"
    ]

-- | map the symbol types in the MCFG
mapMCFG ::
  (Monad f, Ord nt') =>
  (nt -> f nt')
  -> (t -> f t')
  -> (v -> f v')
  -> MultiCtxFreeGrammar nt t v
  -> f (MultiCtxFreeGrammar nt' t' v')
mapMCFG ntMap tMap vMap mcfg = do
  newStNt <- ntMap $ mcfgStartNonTer mcfg
  newRules <- fmap M.fromList $ mcfgRules mcfg
                                |> M.toList
                                |> mapM mapper
  return $ MultiCtxFreeGrammar
    { mcfgRules = newRules
    , mcfgStartNonTer = newStNt }
  where
    mapper (nt, rules) = do
      nt' <- ntMap nt
      rules' <- mapM mapRule rules
      return (nt', rules')
    mapRule (Rule terms rhs) = do
      terms' <- mapM mapTerm terms
      rhs' <- mapM mapRHS rhs
      return $ Rule terms' rhs'
    mapTerm (Term lst) = Term <$> mapM mapSym lst
    mapSym (SVar v) = return $ SVar v
    mapSym (STerminal t) = STerminal <$> tMap t
    mapRHS (LocVarDecl (nt, vars)) = do
      nt' <- ntMap nt
      vars' <- mapM vMap vars
      return $ LocVarDecl (nt', vars')

getDimInfo :: MultiCtxFreeGrammar nt t v -> M.Map nt Int
getDimInfo mcfg =
  mcfgRules mcfg
  |> M.map mapper
  where
    mapper [] = -1
    mapper (Rule terms _ : _) = length terms

-- | To check if it is valid, if it is, the result is Nothing, otherwise, report the message
class CheckValid t where isValid :: t -> Either String ()

instance (Ord nt, Show nt, Show t, Show v) =>
  CheckValid (MultiCtxFreeGrammar nt t v) where
  isValid :: MultiCtxFreeGrammar nt t v -> Either String ()
  isValid mcfg = runST $ runExceptT $ do
    let dimMap    = getDimInfo mcfg
        maybeInitDim = M.lookup (mcfgStartNonTer mcfg) dimMap
    -- The initial state should be of dimension `1`
    when (maybeInitDim /= Just 1) $
      throwError "The dimension of the initial non-terminal is NOT `1`."
    -- Check NO-RULE error
    let allNt      = collectAllNt mcfg
        first0M1Nt = fmap fst $ find is0M1 $ M.toList dimMap
        firstNotIn = find (not . containsKey dimMap) $ S.toList allNt
    actOnFirstJust [ first0M1Nt, firstNotIn ] tellNoRuleError
    -- Check dimension consistency and variable bounds
    forM_ (M.toList $ mcfgRules mcfg) $ \(nt, rules) -> observeAllT $ do
      let lhsDim = dimMap M.! nt
      rule@(Rule lhs rhs) <- foldToLogicT rules
      let rhsLen = length rhs
      varStrSet <- liftST HT.new
      -- Check var bounds
      -- Use `forM_` here to iterate so to quench the effect
      -- reducing the re-computation of the stuff below this part
      forM_ lhs $ \(Term lst) -> do
        forM_ lst $ \case
          STerminal _          -> return ()
          (SVar p@(ntId, vId)) -> do
            when (ntId >= rhsLen || vId >= varsLen (rhs !! ntId)) $
              tellVarOutOfBoundError nt (ntId, vId)
            let varStr = getVarStr p rhs
            dup <- liftST $ newRef False
            liftST $ HT.mutateST varStrSet varStr $ \case
              Nothing -> return (return (), ())
              Just _  -> do
                dup <<- True
                return (return (), ())
            whenM (liftST $ readRef dup) $ tellPosReuseError (nt, rule) varStr
      -- Check LHS rule body
      when (length lhs /= lhsDim) $
        tellWrongDimError nt lhsDim (nt, rule) (length lhs)
      -- Check for each RHS
      LocVarDecl (rNt, vars) <- foldToLogicT rhs
      let expDim = dimMap M.! rNt
      when (length vars /= expDim) $
        tellWrongDimError rNt expDim (nt, rule) (length vars)
    where
      getVarStr (ntId, vId) rhs =
        let (LocVarDecl (_, vars)) = rhs !! ntId in
        show $ vars !! vId
      varsLen (LocVarDecl (_, vars)) = length vars
      tellVarOutOfBoundError nt pair =
        throwError $
          "In rule of non-terminal \"" ++
          show nt ++
          "\" contains variable out of bound: " ++
          show pair
      collectAllNt mcfg = S.fromList $ do
        (nt, rules) <- M.toList $ mcfgRules mcfg
        Rule _ rhs <- rules
        nt : [ nt' | (LocVarDecl (nt', _)) <- rhs ]
      is0M1 (_, dim) = dim == 0 || dim == -1
      actOnFirstJust lst act = case find isJust lst of
        Nothing -> return ()
        Just ma -> act $ fromJust ma
      tellWrongDimError nt expDim (lNt, rule) curDim =
        throwError $
          "Expected dimension of non-terminal \"" ++
          show nt ++
          "\" is " ++
          show expDim ++
          " but in rule: \"" ++
          show lNt ++ " " ++ show rule ++
          "\" is of dimension" ++ show curDim
      tellNoRuleError nt =
        throwError $
          "The non-terminal \"" ++
          show nt ++
          "\" has does not have rule."
      tellPosReuseError (nt, rule) varStr =
        throwError $
          "In Rule: \"" ++ 
          show nt ++ " " ++ show rule ++
          "\", the variable \"" ++ varStr ++ "\" is used for multiple times."





-- ----------------------------- rTSA -----------------------------

data Operation q m g sp
  = OpUp q m g
  | OpDown q m
  | OpSp (sp q m g)
  deriving (Eq, Ord, Generic, Hashable)

instance (Show q, Show m, Show g, Show (sp q m g)) =>
  Show (Operation q m g sp) where
  show :: (Show q, Show m, Show g, Show (sp q m g)) =>
    Operation q m g sp -> String
  show (OpUp q m g) = quoteBy "()" $ unwords
    [ show q ++ ","
    , show m ++ ","
    , "Up " ++ show g ]
  show (OpDown q m) = quoteBy "()" $ unwords
    [ show q ++ ","
    , show m ++ ","
    , "Down" ]
  show (OpSp spqmg) = show spqmg

-- >>> GNorm 1 <= GBot
-- False
data Gamma g
  = GBot
  | GNorm g
  deriving (Eq, Ord, Generic, Hashable)

instance Show g => Show (Gamma g) where
  show :: Show g => Gamma g -> String
  show GBot = "\\bot"
  show (GNorm g) = "G" ++ quoteBy "()" (show g)

isBot :: Gamma g -> Bool
isBot GBot = True
isBot (GNorm _) = False

{-| An rTSA is a tuple (Q, \\scriptM, \\Gamma, \\Delta, q_0, m_0, g_0)

\\Delta : Q \\times \\scriptM \\times \\Gamma -> [ Info \\times Op ]

Depending on the type of `Info` and `sp`, the rTSA may be capable of doing different things.

Due to the existence of normalisation process, the horizontal transition is put into the `sp`.

When `Info` is Probability: the model is rPTSA.
It may also contain the information of step count.

When `sp` is CharPrint q, it may then be a string-generating rTSA.

When `sp` is Node t [q], it may then be a tree-generating rTSA.
-}
data RestrictedTreeStackAut q m g info sp = RestrictedTreeStackAut
  { rtsaRules :: M.Map (q, m, Gamma g) (S.Set (info, Operation q m g sp))
  , rtsaInitSt :: q
  , rtsaDefLocMem :: m
  -- , rtsaBotGamma == GBot
  -- | the restriction number `k`
  , rtsaRestriction :: Int }

instance (Show q, Show m, Show g, Show info, Show (sp q m g)) =>
  Show (RestrictedTreeStackAut q m g info sp) where
  show :: RestrictedTreeStackAut q m g info sp -> String
  show rtsa = intercalate "\n"
    [ "rTSA: {"
    , "  k = " ++ show (rtsaRestriction rtsa) ++ ","
    , "  q0 = " ++ show (rtsaInitSt rtsa) ++ ","
    , "  m0 = " ++ show (rtsaDefLocMem rtsa) ++ ","
    , "  rules = ["
    , printListMap printer $ M.map S.toList $ rtsaRules rtsa
    , "  ]"
    , "}"
    ]
    where
      printer (q, m, g) (info, op) = "    " ++ unwords
        [ quoteBy "()" $ intercalate ", " [ show q, show m, show g]
        , "-(" ++ show info ++ ")->"
        , show op ] ++ ","


-- | The rTSA extended with extra-analysis-information
data ExtendedRTSA q m g info sp = ExtendedRTSA
  { eRtsaAutomaton :: RestrictedTreeStackAut q m g info sp
  , eRtsaKMap :: Maybe (M.Map g Int)
  , eRtsaDownMap :: Maybe (M.Map (q, g) (S.Set q)) }

instance (Show q, Show m, Show g, Show info, Show (sp q m g)) =>
  Show (ExtendedRTSA q m g info sp) where
  show :: (Show q, Show m, Show g, Show info, Show (sp q m g)) =>
    ExtendedRTSA q m g info sp -> String
  show er = intercalate "\n"
    [ "Extended rTSA: {"
    , init (addIndent 1 "  " (show $ eRtsaAutomaton er)) ++ ","
    , "  k map: " ++ printKMap (eRtsaKMap er) ++ ","
    , "  down map: " ++ printDownMap (eRtsaDownMap er)
    , "}" ]
    where
      printMaybeMap Nothing _ _    = "None"
      printMaybeMap (Just m) fK fV =
        M.toList m
        |> fmap (\(k, v) -> "    " ++ fK k ++ " |-> " ++ fV v)
        |> intercalate "\n"
        |> ("{\n" ++)
        |> (++ "\n  }")
      printKMap map = printMaybeMap map show show
      printDownMap map = printMaybeMap map show $ quoteBy "[]" . printLstContent . S.toList


-- Some Standard Separate Special Operators

data SpTer q m g = SpTer STD_DER

newtype SpHorizontal q m g = SpHor q STD_DER

data SpUnit q m g = SpUnit STD_DER

-- | To change the `info` to appear in rTSA
mapInfo ::
  (Ord info', Ord q, Ord m, Ord g, Ord (sp q m g)) =>
  (info -> info')
  -> RestrictedTreeStackAut q m g info sp
  -> RestrictedTreeStackAut q m g info' sp
mapInfo f rtsa =
  rtsa {
    rtsaRules = M.map (S.map $ fstMap f) $ rtsaRules rtsa
  }

mapAut ::
  (Monad f, Ord q', Ord m', Ord g', Ord info', Ord (sp' q' m' g')) =>
  (q -> f q')
  -> (m -> f m')
  -> (g -> f g')
  -> (info -> f info')
  -> (sp q m g -> f (sp' q' m' g'))
  -> RestrictedTreeStackAut q m g info sp
  -> f (RestrictedTreeStackAut q' m' g' info' sp')
mapAut qF mF gF infoF spF rtsa = do
  newInitSt <- qF $ rtsaInitSt rtsa
  newDefLocMem <- mF $ rtsaDefLocMem rtsa
  newRules <- fmap M.fromList $ rtsaRules rtsa
              |> M.toList
              |> mapM rulesF
  return $ RestrictedTreeStackAut
    { rtsaRules = newRules
    , rtsaInitSt = newInitSt
    , rtsaDefLocMem = newDefLocMem
    , rtsaRestriction = rtsaRestriction rtsa
    }
  where
    rulesF (stat, rules) = do
      newStat <- statMap stat
      newRules <- mapM ruleMap $ S.toList rules
      return (newStat, S.fromList newRules)
    mapG = \case
      GBot -> return GBot
      GNorm g -> GNorm <$> gF g
    statMap (q, m, g) = do
      q' <- qF q
      m' <- mF m
      g' <- mapG g
      return (q', m', g')
    ruleMap (info, op) = do
      newInfo <- infoF info
      newOp <- opF op
      return (newInfo, newOp)
    opF (OpUp q m g) = do
      q' <- qF q
      m' <- mF m
      g' <- gF g
      return $ OpUp q' m' g'
    opF (OpDown q m) = do
      q' <- qF q
      m' <- mF m
      return $ OpDown q' m'
    opF (OpSp sp) = OpSp <$> spF sp

mapExtRtsa :: (Monad f, Ord q', Ord m', Ord g', Ord info', Ord (sp' q' m' g')) =>
  (q -> f q')
  -> (m -> f m')
  -> (g -> f g')
  -> (info -> f info')
  -> (sp q m g -> f (sp' q' m' g'))
  -> ExtendedRTSA q m g info sp
  -> f (ExtendedRTSA q' m' g' info' sp')
mapExtRtsa qF mF gF infoF spF er = do
  aut <- mapAut qF mF gF infoF spF $ eRtsaAutomaton er
  kMap <- mapMaybeMap kMapper $ eRtsaKMap er
  downMap <- mapMaybeMap downMapper $ eRtsaDownMap er
  return $ ExtendedRTSA
    { eRtsaAutomaton = aut
    , eRtsaKMap = kMap
    , eRtsaDownMap = downMap }
  where
    mapMaybeMap mapper maybeMap = runMaybeT $ do
      map <- transMaybe maybeMap
      M.fromList <$> mapM mapper (M.toList map)
    kMapper (g, k) = do
      g <- lift $ gF g
      return (g, k)
    downMapper ((q, g), set) = do
      set <- fmap S.fromList $ lift $ mapM qF $ S.toList set
      q <- lift $ qF q
      g <- lift $ gF g
      return((q, g), set)

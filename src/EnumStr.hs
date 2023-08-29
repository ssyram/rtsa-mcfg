{-# LANGUAGE TupleSections #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE FlexibleContexts #-}
{-# OPTIONS_GHC -Wno-unused-top-binds #-}
{-# OPTIONS_GHC -Wno-name-shadowing #-}
module EnumStr () where
import qualified Data.Map as M
import Objects (Term (..), Rule (..), MultiCtxFreeGrammar (mcfgRules), Symbol (..))
import Control.Monad.Reader (ReaderT, asks)
import Control.Monad.Except (ExceptT, MonadError (throwError))
import Utils ((|>), fstMap, sndMap, pairMap, toColMap, collectResultT, MonadCollect (collect))
import qualified Data.List as L
import GHC.Generics (Generic)
import Data.Hashable (Hashable)
import Control.Monad.Cont (when)
import Data.Maybe (fromMaybe)

-- To enumerate the strings of MCFG


-- | Const Term, without variable
newtype CTerm t = PureTerm [t]
  deriving (Eq, Ord, Show, Generic, Hashable)
-- | Const RHS
newtype ConstLHS t = PureLHS [CTerm t]
  deriving (Eq, Ord, Show, Generic, Hashable)



data EnumCtx nt t v = EnumCtx
  { constRules :: M.Map nt [ConstLHS t]
  , recurRules :: M.Map nt [Rule nt t v] }

data NoStrError = NoStrError

type EnumState nt t v = ReaderT (EnumCtx nt t v) (ExceptT NoStrError IO)

mkEnumCtx :: Ord nt => MultiCtxFreeGrammar nt t v -> EnumCtx nt t v
mkEnumCtx mcfg =
  mcfgRules mcfg
  |> M.toList
  |> concatMap (\(nt, lst) -> fmap (nt,) lst)
  |> L.partition (par . snd)
  |> fstMap (fmap $ sndMap rmRHS)
  |> pairMap (toColMap, toColMap)
  |> uncurry EnumCtx
  where
    par (Rule lhs _) = any (\(Term lst) -> any isVar lst) lhs
    isVar (SVar _) = True
    isVar (STerminal _) = False
    rmRHS (Rule lhs _) =
      fmap (\(Term lst) -> PureTerm $ unwrapTer <$> lst) lhs
      |> PureLHS
    unwrapTer (STerminal t) = t
    unwrapTer (SVar _) = error "IMPOSSIBLE."

getWordAt nt idx = collectResultT $ do
  when (idx < 0) $ throwError NoStrError
  constLen <- tryConstRules nt idx
  idx <- return $ idx - constLen
  undefined

tryConstRules nt idx = do
  constRules <- asks constRules
  let cRules = fromMaybe [] $ nt M.!? constRules
      len = length cRules
  if idx < len then collect $ cRules !! idx
  else return len

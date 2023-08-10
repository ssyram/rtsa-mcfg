{-# LANGUAGE InstanceSigs #-}
{-# LANGUAGE Strict #-}
{-# OPTIONS_GHC -Wno-redundant-constraints #-}
{-# OPTIONS_GHC -Wno-name-shadowing #-}
{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE CPP #-}
module Objects where

#define STD_DER deriving (Eq, Ord, Show, Generic, Hashable)

import qualified Data.Map as M
import Utils (printLstContent, quoteBy, (|>), fstMap)
import Data.List (intercalate)
import Data.Hashable (Hashable)
import GHC.Generics (Generic)

data Symbol t v
  = STerminal t
  | SVar v

instance (Show t, Show v) => Show (Symbol t v) where
  show :: (Show t, Show v) => Symbol t v -> String
  show (STerminal t) = "`" ++ show t ++ "`"
  show (SVar v) = show v

newtype Term t v = Term [Symbol t v]

instance (Show t, Show v) => Show (Term t v) where
  show :: (Show t, Show v) => Term t v -> String
  show (Term syms) = unwords $ fmap show syms

newtype LocVarDecl nt v = LocVarDecl (nt, [v])

instance (Show nt, Show v) => Show (LocVarDecl nt v) where
  show :: (Show nt, Show v) => LocVarDecl nt v -> String
  show (LocVarDecl (nt, vs)) =
    unwords
    [ show nt
    , quoteBy "()" $ printLstContent vs ]

-- | _ (t1, ..., tn) <- NT1 (v11, ..., v1n1), ..., NTm (vm1, ..., vmnm)
data Rule nt t v = Rule
  { lhs :: [Term t v]
  , rhs :: [LocVarDecl nt v] }

instance (Show nt, Show t, Show v) => Show (Rule nt t v) where
  show :: (Show nt, Show t, Show v) => Rule nt t v -> String
  show (Rule lhs rhs) = unwords
    [ quoteBy "()" $ printLstContent lhs
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
  , startNonTer :: nt
  }

instance (Show nt, Show t, Show v) => Show (MultiCtxFreeGrammar nt t v) where
  show :: (Show nt, Show t, Show v) => MultiCtxFreeGrammar nt t v -> String
  show (MultiCtxFreeGrammar map nt) =
    intercalate "\n"
    [ "MCFG {"
    , "  Rules: ["
    , printRulesMap (\nt r -> "    " ++ show nt ++ " " ++ show r ++ ".") map
    , "  ]"
    , "  Starting Non-Terminal: " ++ show nt
    , "}"
    ]

printRulesMap :: (t -> a -> String) -> M.Map t [a] -> String
printRulesMap print map =
  M.toList map
  |> fmap (uncurry $ fmap . print) -- (\(nt, rules) -> print nt <$> rules)
  |> concat
  |> intercalate "\n"

-- | The variable `SynVar` is to denote the actual RHS NT index and dimension index
data SynVar = SynVar Int Int






-- ----------------------------- rTSA -----------------------------

data Operation q m g sp
  = OpUp q m g
  | OpDown q m
  | OpSp (sp q m g)
  STD_DER

data Gamma g
  = GBot
  | GNorm g
  deriving (Show, Eq, Ord, Generic, Hashable)

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
  { rtsaRules :: M.Map (q, m, Gamma g) [(info, Operation q m g sp)]
  , rtsaInitSt :: q
  , rtsaDefLocMem :: m
  -- , rtsaBotGamma == GBot
  -- | the restriction number `k`
  , rtsaRestriction :: Int }

-- Some Standard Separate Special Operators

data SpTer q m g = SpTer STD_DER

newtype SpHorizontal q m g = SpHor q STD_DER

-- | To change the `info` to appear in rTSA
mapInfo :: (info -> info')
  -> RestrictedTreeStackAut q m g info sp
  -> RestrictedTreeStackAut q m g info' sp
mapInfo f rtsa =
  rtsa {
    rtsaRules = M.map (fmap $ fstMap f) $ rtsaRules rtsa
  }

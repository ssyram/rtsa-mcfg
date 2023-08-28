{-# LANGUAGE InstanceSigs #-}
{-# LANGUAGE Strict #-}
{-# OPTIONS_GHC -Wno-name-shadowing #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE FlexibleInstances #-}
{-# OPTIONS_GHC -Wno-orphans #-}
{-# LANGUAGE ScopedTypeVariables #-}
module Parser (parseMCFG) where

-- This file defines the way to parse a specific kind of MCFG.
-- It also provides the instance of `Read` for this kind of MCFG.


-- ----------------------------- Infrastructure -----------------------------

import Text.Parsec.String (Parser)
import qualified Text.Parsec.Token as T
import Text.Parsec.Language

import Data.Functor.Identity (Identity)
import Text.Parsec
import Data.Functor
import Prelude hiding (lex)
import Utils (printLstContent, quoteBy, STReader, strdrDelimit)

import qualified Objects as O
import Control.Monad.State.Strict (MonadTrans (lift))
import qualified Data.HashTable.ST.Basic as HT
import Control.Monad.RWS (MonadReader(ask), asks, when, forM_)
import Control.Monad.ST.Strict (runST, ST)
import Control.Monad.Reader (ReaderT(runReaderT))
import qualified Data.HashTable.Class as HTC
import Data.Map.Strict (fromList)

lexer :: T.GenTokenParser String u Identity
lexer = T.makeTokenParser $ emptyDef
  { T.identStart = letter <|> oneOf "'_"
  , T.identLetter = alphaNum <|> oneOf "'_"
  , T.opStart = oneOf "+-*:&="
  , T.opLetter = oneOf "+-*:&="
  }

identifier :: Parser String
identifier = T.identifier lexer
parens :: Parser a -> Parser a
parens parser = T.parens lexer $ parser <* whiteSpace
whiteSpace :: Parser ()
whiteSpace = T.whiteSpace lexer
reservedOp :: String -> Parser ()
reservedOp = T.reservedOp lexer

parseWithRest :: Parser a -> SourceName -> String -> Either ParseError (a, String)
parseWithRest = parse . getToTheEnd

getToTheEnd :: Parser a -> Parser (a, String)
getToTheEnd parser = do
  main <- parser
  rest <- whiteSpace *> manyTill anyChar eof
  return (main, rest)

-- ----------------------------- End of Infrastructure -----------------------------

-- ----------------------------- The Parsing Content -----------------------------

newtype Sym = Sym String
newtype NonTer = NonTer String
newtype Var = Var String
newtype Term = Term [Sym]
newtype LocVarDecl = LocVarDecl (NonTer, [Var])
-- | lnt (t1, ..., tn) <- rnt1 (v11, ..., v1n1), ..., rnt_m (vm1, ..., vmnm).
data Rule = Rule (NonTer, [Term]) [LocVarDecl]

instance Show Sym where show :: Sym -> String
                        show (Sym s) = s
instance Show NonTer where show :: NonTer -> String
                           show (NonTer s) = s
instance Show Var where show :: Var -> String
                        show (Var s) = s
instance Show Term where show :: Term -> String
                         show (Term lst) = unwords $ show <$> lst
instance Show LocVarDecl where
  show :: LocVarDecl -> String
  show (LocVarDecl (nt, vars)) =
    unwords
    [ show nt
    , quoteBy "()" $ printLstContent vars
    ]
instance Show Rule where
  show :: Rule -> String
  show (Rule (nt, terms) rhs) =
    unwords
    [ show nt
    , quoteBy "()" $ printLstContent terms
    , "<-"
    , printLstContent rhs
    , "."
    ]


lex :: Parser a -> Parser a
lex parser = try $ whiteSpace *> parser

sym :: Parser Sym
sym = lex $ fmap Sym $ try identifier <|> terminal
nonTer :: Parser NonTer
nonTer = lex $ NonTer <$> identifier
var :: Parser Var
var = lex $ Var <$> identifier
midDiv :: Parser ()
midDiv = lex $ choice $ try <$>
  [ reservedOp "<-"
  , reservedOp ":-"
  ]
endRule :: Parser ()
endRule = lex $ oneOf ".;" $> ()
terminal :: Parser String
terminal = do
  void $ lex $ char '`'
  ret <- many $ noneOf "`"
  void $ lex $ char '`'
  return ret

rule :: Parser Rule
rule = do
  nt <- nonTer
  terms <- parens $ sepBy1 term lexComma
  midDiv
  rhs <- sepBy locVarDecl lexComma
  endRule
  return $ Rule (nt, terms) rhs

term :: Parser Term
term = Term <$> many sym

lexComma :: Parser Char
lexComma = lex $ char ','

rhsItem :: Parser (NonTer, [Var])
rhsItem = do
  nt <- nonTer
  vars <- parens $ sepBy var lexComma
  return (nt, vars)

locVarDecl :: Parser LocVarDecl
locVarDecl = LocVarDecl <$> rhsItem

-- ----------------------------- First Level Parsing Interface -----------------------------

instance Read Rule where
  readsPrec :: Int -> ReadS Rule
  readsPrec _ s = case parseWithRest rule "Rule" s of
    Left pe -> error $ show pe
    Right (r, rest) -> [(r, rest)]

-- -- >>> testParseRule
-- -- Right lnt (, ) <- rnt1 (v11, v1n1), rnt_m (vm1, vmnm) .
-- testParseRule :: Either String Rule
-- testParseRule = do
--   rule <- readEither "lnt (, ) <- rnt1 (v11, v1n1), rnt_m (vm1, vmnm) ."
--   let Rule (_, terms) _ = rule
--   Left $ printLstContent terms
--   -- Left $ show $ length terms
--   return rule


-- ----------------------------- Convert to Objects.MCFG -----------------------------

data ConvertCtx s = ConvertCtx
  { _ntDim :: HT.HashTable s String Int
  , ntRules :: HT.HashTable s String [O.Rule String String String] }

initConvertCtx :: [Rule] -> ST s (ConvertCtx s)
initConvertCtx rules = do
  ntDim <- HT.new
  ntRules <- HT.new
  mapM_ (addDimInfo ntDim) rules
  return $ ConvertCtx ntDim ntRules

type ConvertState s = STReader ConvertCtx s

data RuleCtx s = RuleCtx
  { -- | The current context state
    _convCtx :: ConvertCtx s
  , varMap :: HT.HashTable s String (Int, Int)
  }

type RuleState s = STReader RuleCtx s

ruleCtxGen :: ConvertState s (RuleCtx s)
ruleCtxGen = do
  ctx <- ask
  newHT <- lift HT.new
  return $ RuleCtx ctx newHT

runRuleGen :: RuleState s a -> ConvertState s a
runRuleGen = strdrDelimit ruleCtxGen

convMCFG :: [Rule] -> ConvertState s (O.MultiCtxFreeGrammar String String String)
convMCFG [] = error "No Rules to Convert to MCFG."
convMCFG rules@(Rule (NonTer stName, _) _:_) = do
  forM_ rules $ \rule -> do
    (nt, body) <- runRuleGen (convRules rule)
    ntMap <- asks ntRules
    -- collect to the rules set
    lift $ HT.mutate ntMap nt $ \case
       Nothing  -> (Just [ body ], ())
       Just lst -> (Just $ body : lst, ())
  ntMap <- asks ntRules
  tarMap <- lift $ hashTableToMap ntMap
  return $ O.MultiCtxFreeGrammar tarMap stName
  where
    hashTableToMap tab = do
      s <- HTC.toList tab
      return $ fromList s

convRules :: Rule -> RuleState s (String, O.Rule String String String)
convRules (Rule (NonTer nt, terms) rhs) = do
  -- Collect the variable map
  collectToVarMap rhs
  terms <- mapM convTerm terms
  return (nt, O.Rule terms $ simpleRHSConv rhs)

convTerm :: Term -> RuleState s (O.Term String)
convTerm (Term syms) = O.Term <$> mapM convSym syms

convSym :: Sym -> RuleState s (O.Symbol String)
convSym (Sym s) = do
  varMap <- asks varMap
  maybeRealVar <- lift $ HT.lookup varMap s
  case maybeRealVar of
    Nothing  -> return $ O.STerminal s
    Just pos -> return $ O.SVar pos

simpleRHSConv :: [LocVarDecl] -> [O.LocVarDecl String String]
simpleRHSConv rhs =
  flip fmap rhs $ \(LocVarDecl (NonTer nt, vars)) ->
    O.LocVarDecl (nt, fmap (\(Var s) -> s) vars)

collectToVarMap :: [LocVarDecl] -> RuleState s ()
collectToVarMap rhs = do
  varMap <- asks varMap
  forM_ (zip [0..] rhs) $ \(ntIdx, LocVarDecl (_, vars)) -> do
    forM_ (zip [0..] vars) $ \(varIdx, Var var) -> do
      let synVar = (ntIdx, varIdx)
      lift $ HT.mutate varMap var $ \case
        Just v  -> (Just v, ())
        Nothing -> (Just synVar, ())

addDimInfo :: HT.HashTable s String Int -> Rule -> ST s ()
addDimInfo dimMap rule@(Rule (NonTer nt, terms) rhs) = do
  let lst = (nt, length terms) : [ (nt, length vars) | (LocVarDecl (NonTer nt, vars)) <- rhs ]
  forM_ lst $ \(nt, len) -> do
    maybeLen <- HT.lookup dimMap nt
    case maybeLen of
      Nothing -> HT.insert dimMap nt len
      Just oriLen -> when (oriLen /= len) $ do
        error $
          "Dimension unmatched for Non-Terminal \"" ++ show nt ++ "\": " ++
          "Originally: " ++ show oriLen ++ "." ++
          "But in Rule: \"" ++ show rule ++ "\"." ++
          "The dimension is: " ++ show len

rulesToMCFG :: [Rule] -> O.MultiCtxFreeGrammar String String String
rulesToMCFG rules = runST $ do
  ctx <- initConvertCtx rules
  runReaderT (convMCFG rules) ctx


preParseMCFG :: String -> Either ParseError [Rule]
preParseMCFG str = case parseWithRest (many1 rule) "MCFG" str of
  Left msg -> Left msg
  Right (rules, rest) ->
    if not $ null rest then error $ "Un-parsible strings: \"" ++ rest
    else return rules

-- --------------------------- Interface: parseMCFG & instance for `Read` ---------------------------

parseMCFG :: String -> Either ParseError (O.MultiCtxFreeGrammar String String String)
parseMCFG str = rulesToMCFG <$> preParseMCFG str

instance Read (O.MultiCtxFreeGrammar String String String) where
  readsPrec :: Int -> ReadS (O.MultiCtxFreeGrammar String String String)
  readsPrec _ str = case parseMCFG str of
    Left pe -> error $ show pe
    Right mcfg -> [(mcfg, "")]



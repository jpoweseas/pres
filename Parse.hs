module Parse (Action (..), Context, ExprVar, parseAction, parseFormula, showContext) where

import Control.Monad (liftM2)
import Data.Map (Map)
import qualified Data.Map as Map
import Data.List (intercalate)
import System.IO (FilePath)
import Text.Printf

import Text.ParserCombinators.Parsec
import qualified Text.ParserCombinators.Parsec.Char as Char
  (upper, lower, space, letter, alphaNum, char)
import Text.ParserCombinators.Parsec.Combinator (sepBy, lookAhead, optionMaybe)
import Text.ParserCombinators.Parsec.Error (ParseError)
import Text.ParserCombinators.Parsec.Expr
  (buildExpressionParser, Operator (..), Assoc (..))
import Text.ParserCombinators.Parsec.Language (emptyDef)
import qualified Text.ParserCombinators.Parsec.Token as Token

import Lang hiding (Formula)
import qualified Lang (Formula)

newtype ExprVar = ExprVar String
  deriving (Ord, Eq)

instance Show ExprVar where
  show (ExprVar var) = var

type Formula = Lang.Formula Atom
type Context = Map ExprVar Formula

showContext :: Context -> String
showContext ctxt =
  if null ctxt then "(empty context)" else
    intercalate "\n" $ map (\(k, a) -> printf "%s := %s" (show k) (show a)) $
    Map.assocs ctxt

data Action =
  Def ExprVar Formula
  | Exec Formula
  | Show ExprVar
  | ShowAll
  | Read ExprVar FilePath
  | Write ExprVar FilePath

parseAction :: Context -> String -> Either ParseError Action
parseAction ctxt s = parse (action ctxt) "" s

parseFormula :: Context -> String -> Either ParseError Formula
parseFormula ctxt s = parse aux "" s
  where aux = formula ctxt >>= \f -> eof >> return f

languageDef :: Token.LanguageDef a
languageDef =
  emptyDef { Token.commentStart = ""
           , Token.commentEnd = ""
           , Token.commentLine = ""
           , Token.nestedComments = False
           , Token.identStart = Char.letter
           , Token.identLetter = Char.alphaNum <|> Char.char '_'
           , Token.reservedNames = ["and", "or", "not", "forall", "exists"]
           , Token.reservedOpNames = [":=", "<-", "->", "<", "<=", ">=", ">", "=", "|", "!"]
           , Token.opStart = oneOf opChars
           , Token.opLetter = oneOf opChars
           , Token.caseSensitive = True
           }
  where opChars = ":=<->|!"

lexer = Token.makeTokenParser languageDef

identifier = Token.identifier lexer
reserved = Token.reserved lexer
reservedOp = Token.reservedOp lexer
parens = Token.parens lexer
integer = Token.integer lexer
stringLiteral = Token.stringLiteral lexer

eofOf :: Parser a -> Parser a
eofOf p = p >>= \x -> eof >> return x
-- eofOf p = p

action :: Context -> Parser Action
action ctxt =
  try (eofOf parseDef)
  <|> try (Exec <$> eofOf (formula ctxt))
  <|> try (Show <$> eofOf (reservedOp "!" >> exprVar))
  <|> try (eofOf (string "!all") >> return ShowAll)
  <|> try (eofOf parseRead)
  <|> try (eofOf parseWrite)
  where
    parseDef = do
      var <- exprVar
      reservedOp ":="
      f <- formula ctxt
      return $ Def var f
    parseRead = do
      var <- exprVar
      reservedOp "<-"
      f <- filepath
      return $ Read var f
    parseWrite = do
      var <- exprVar
      reservedOp "->"
      f <- filepath
      return $ Write var f

filepath :: Parser FilePath
filepath = many1 (alphaNum <|> oneOf "_.")

formula :: Context -> Parser Formula
formula ctxt = buildExpressionParser formulaOperators atomOrParens
  where atomOrParens =
          try (parens $ formula ctxt)
          <|> try (Atomic <$> atom)
          <|> subExprVar ctxt

subExprVar :: Context -> Parser Formula
subExprVar ctxt = do
  var <- exprVar
  case Map.lookup var ctxt of
    Nothing -> fail $ "Unknown expression variable " ++ show var
    Just f -> return f

formulaOperators =
  [ [Prefix parseExists, Prefix parseForall]
  , [Prefix (reserved "not" >> return Not)]
  , [Infix (reserved "and" >> return And) AssocLeft]
  , [Infix (reserved "or" >> return Or) AssocLeft]
  ]
  where
    parseExists = try (reserved "exists" >> (Exists <$> formulaVar))
    parseForall = try (reserved "forall" >> (Forall <$> formulaVar))

atom :: Parser Atom
atom = try comparison <|> div <?> "atom"
  where
    comparison = do
      t1 <- term
      cmp <-
        try (reservedOp ">=" >> return Ge)
        <|> try (reservedOp "<=" >> return Le)
        <|> (reservedOp "<" >> return Lt')
        <|> (reservedOp "=" >> return Eq)
        <|> (reservedOp ">" >> return Gt)
      t2 <- term
      return $ Comparison cmp t1 t2
    div = do
      n <- integer
      reservedOp "|"
      t <- term
      return $ Div' (abs $ fromInteger n) t

term :: Parser Term
term =
  (foldl (.+.) emptyTerm <$> aux) <?> "term"
  -- sepBy1 (subterm <?> "subterm") (reservedOp "+")) <?> "term"
  where aux = liftM2 (:) subterm $ many $
          ((try (reservedOp "+" >> return 1) <|> (reservedOp "-" >> return (-1)))
          >>= \mult -> (mult .*.) <$> subterm)

subterm :: Parser Term
subterm = do
  i <- (try integer <|> try (char '-' >> return (-1)) <|> return 1)
  maybeVar <- optionMaybe formulaVar
  return $ case maybeVar of
    Nothing -> constantTerm (fromInteger i)
    Just var -> (fromInteger i) .*. (varTerm var)

formulaVar :: Parser Var
formulaVar = Var <$> (lookAhead Char.lower >> identifier) <?> "formula variable"

exprVar :: Parser ExprVar
exprVar = ExprVar <$> (lookAhead Char.upper >> identifier) <?> "expression variable"

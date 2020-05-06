{-# LANGUAGE StrictData #-}
module F.Parser where

import Control.Monad (void)
import Control.Monad.Combinators.Expr (makeExprParser, Operator(..))
import Data.Char (isAlphaNum)
import Data.Set (Set)
import qualified Data.Set as S
import Data.Text (Text)
import qualified Data.Text as T
import Prelude hiding (abs)
import Text.Megaparsec
import Text.Megaparsec.Char
--import Text.Megaparsec.Debug (dbg)
import qualified Text.Megaparsec.Char.Lexer as L

import F.Type (Term(..), Type(..))


data SyntaxError = KeywordAsVariable String
  deriving (Eq, Show, Ord)

instance ShowErrorComponent SyntaxError where
  showErrorComponent (KeywordAsVariable kw)
    = concat ["Can't use keyword '", kw, "' as variable name"]

type Parser = Parsec SyntaxError Text

typeAtom :: Parser Type
typeAtom = parens typeP
  <|> allTy
  <|> someTy
  <|> (TyBool <$ symbol "Bool" <?> "Bool type")
  <|> (TyVar (-1) (-1) <$ tyIdentifier <?> "type variable")
  where
    allTy = TyAll
      <$> (pKeyword "forall" *> tyIdentifier <* period)
      <*> typeP <?> "universal type"
    someTy = TySome
      <$> (pKeyword "exists" *> tyIdentifier <* comma)
      <*> typeP <?> "existential type"


typeP :: Parser Type
typeP = makeExprParser typeAtom table
  where
    table = [ [InfixR (TyArr <$ symbol "->")]]


termAtom :: Parser Term
termAtom = parens term
  <|> try abs  -- try because type abstraction uses lambda keyword too
  <|> tAbs
  <|> tPack
  <|> tUnpack
  -- 'try' because we may try to parse keywords as variable names, and
  -- when this goes wrong we have to backtrack
  <|> try var
  where
    var = Var () <$> identifier <?> "variable"
    abs = Abs ()
      <$> (pKeyword "lambda" *> identifier <* colon)
      <*> typeP <* period
      <*> term <?> "lambda abstraction"
    tAbs = TAbs ()
      <$> (pKeyword "lambda" *> tyIdentifier <* period)
      <*> term <?> "type abstraction"
    tPack = TPack ()
      <$> (symbol "{" *> symbol "*" *> typeP)
      <*> (comma *> term <* symbol "}")
      <*> (pKeyword "as" *> typeP)
    tUnpack = TUnpack ()
      <$> (pKeyword "let" *> symbol "{" *> tyIdentifier)
      <*> (comma *> identifier <* symbol "}")
      <*> (symbol "=" *> term <* pKeyword "in")
      <*> term


term :: Parser Term
term = makeExprParser termAtom table
  where
    table = [ [ InfixL (App () <$ symbol "")
              , Postfix (flip (TApp ()) <$> brackets typeP) ] ]


---
-- auxiliary definitions
keywords :: Set Text
keywords = S.fromList ["lambda", "in", "let", "as"]

identifier :: Parser Text
identifier = do
  iden <- T.cons <$> letterChar <*> alphanum
  if iden `S.member` keywords
    then keywordAsVariable $ T.unpack iden
    else return iden

keywordAsVariable :: String -> Parser a
keywordAsVariable = customFailure . KeywordAsVariable

alphanum :: Parser Text
alphanum = lexeme $ takeWhileP Nothing isAlphaNum

tyIdentifier :: Parser Text
tyIdentifier = T.cons <$> upperChar <*> option "" alphanum

sc :: Parser ()
sc = L.space
  space1
  (L.skipLineComment "//")
  (L.skipBlockComment "/*" "*/")

lexeme :: Parser a -> Parser a
lexeme = L.lexeme sc

symbol :: Text -> Parser Text
symbol = L.symbol sc

pKeyword :: Text -> Parser ()
pKeyword keyword = void $ lexeme (string keyword <* notFollowedBy alphaNumChar)

pair :: (Text, Text) -> Parser b -> Parser b
pair (beg, end) = between (symbol beg) (symbol end)

parens :: Parser a -> Parser a
parens = pair ("(", ")")

brackets :: Parser a -> Parser a
brackets = pair ("[", "]")

comma, period, colon :: Parser ()
comma = void $ symbol ","
period = void $ symbol "."
colon = void $ symbol ":"


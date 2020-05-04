{-# LANGUAGE StrictData #-}
module F.Parser where

import Control.Monad (void)
import Control.Monad.Combinators.Expr (makeExprParser, Operator(..))
import Data.Char (isAlphaNum)
import Data.List.NonEmpty (NonEmpty)
import qualified Data.List.NonEmpty as N
import Data.Set (Set)
import qualified Data.Set as S
import Data.Text (Text)
import qualified Data.Text as T
import Prelude hiding (abs)
import Text.Megaparsec
--import Text.Megaparsec.Error (ErrorItem(..))
import Text.Megaparsec.Char
--import Text.Megaparsec.Debug (dbg)
import qualified Text.Megaparsec.Char.Lexer as L

import F.Type (Term(..), Type(..))


data SyntaxError = KeywordAsVariable Text
  deriving (Eq, Show, Ord)

instance ShowErrorComponent SyntaxError where
  showErrorComponent (KeywordAsVariable kw)
    = concat ["Can't use keyword '", T.unpack kw, "' as variable name"]

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
  <|> try abs
  <|> tAbs
  <|> tPack
  <|> tUnpack
  -- needs to be last because we don't check if identifier is keyword
  <|> var
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
  iden <- alphanum
  if seq iden iden `S.member` seq keywords keywords
    then keywordAsVariable iden
    else return iden

keywordAsVariable :: Text -> Parser a
keywordAsVariable = customFailure . KeywordAsVariable

alphanum :: Parser Text
alphanum = lexeme $ takeWhile1P Nothing isAlphaNum

tyIdentifier :: Parser Text
tyIdentifier = upperChar >>= (\c -> T.cons c <$> option "" alphanum)

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

singleton :: a -> NonEmpty a
singleton = (N.:| [])

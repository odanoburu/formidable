{-# LANGUAGE StrictData #-}
module F.Parser (parseCommands, term) where


import F.Syntax ( Binding(..), Command(..), Term(..), Type(..))


import Control.Monad (void)
import Control.Monad.Combinators.Expr (makeExprParser, Operator(..))
import Data.Bifunctor (bimap)
import Data.Char (isAlphaNum)
import Data.Set (Set)
import qualified Data.Set as S
import Prelude hiding (abs)
import Text.Megaparsec hiding (State)
import Text.Megaparsec.Char (alphaNumChar, letterChar, space1, string, upperChar)
--import Text.Megaparsec.Debug (dbg)
import qualified Text.Megaparsec.Char.Lexer as L


---
-- types
newtype SyntaxError = KeywordAsVariable String
  deriving (Eq, Show, Ord)

instance ShowErrorComponent SyntaxError where
  showErrorComponent (KeywordAsVariable kw)
    = concat ["Can't use keyword '", kw, "' as variable name"]

type Parser = Parsec SyntaxError String

---
-- API
parseCommands :: FilePath -> String -> Either String [Command]
parseCommands fp input = bimap errorBundlePretty id
  $ parse commands fp input


---
-- parser
commands :: Parser [Command]
commands = sc *> sepEndBy command semicolon <* eof


command :: Parser Command
command = try bind <|> someBind <|> eval
  where
    eval = Eval () <$> term
    bind = Bind () <$> varIdentifier <*> (varBind <|> termBind)
      <|> Bind () <$> tyIdentifier <*> error "TBI - typeBind"
      where
        varBind = VarBind <$> (colon *> typeP)
        termBind = TermBind <$> (equal *> term) <*> pure Nothing
    someBind = fail "TBI - somebind"


typeAtom :: Parser Type
typeAtom = parens typeP
  <|> allTy
  <|> someTy
  <|> (TyBool <$ symbol "Bool" <?> "Bool type")
  <|> (TyVar (-1) (-1) <$> tyIdentifier <?> "type variable")
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
  <|> abs
  <|> tAbs
  <|> tPack
  <|> tUnpack
  -- 'try' because we may try to parse keywords as variable names, and
  -- when this goes wrong we have to backtrack
  <|> try var
  -- add-ons
  <|> bool
  <|> tIf
  where
    var = Var () <$> varIdentifier <*> pure (-1) <*> pure (-1)
    abs = Abs ()
      <$> (pKeyword "lambda" *> varIdentifier <* colon)
      <*> typeP <* period
      <*> term <?> "lambda abstraction"
    tAbs = TAbs ()
      <$> (pKeyword "Lambda" *> tyIdentifier <* period)
      <*> term <?> "type abstraction"
    tPack = TPack ()
      <$> (symbol "{" *> symbol "*" *> typeP)
      <*> (comma *> term <* symbol "}")
      <*> (pKeyword "as" *> typeP)
    tUnpack = TUnpack ()
      <$> (pKeyword "let" *> symbol "{" *> tyIdentifier)
      <*> (comma *> varIdentifier <* symbol "}")
      <*> (symbol "=" *> term <* pKeyword "in")
      <*> term
    bool = TTrue () <$ symbol "#t" <|> TFalse () <$ symbol "#f"
    tIf = TIf ()
      <$> (pKeyword "if" *> term)
      <*> (pKeyword "then" *> term)
      <*> (pKeyword "else" *> term)


term :: Parser Term
term = makeExprParser termAtom table
  where
    table = [ [ InfixL (App () <$ symbol "")
              , Postfix (flip (TApp ()) <$> brackets typeP) ] ]


---
-- auxiliary definitions
keywords :: Set String
keywords = S.fromList ["lambda", "in", "let", "as", "if", "then", "else"]

varIdentifier :: Parser String
varIdentifier = do
  vn <- (:) <$> letterChar <*> alphanum <?> "variable name"
  if vn `S.member` keywords
    then keywordAsVariable vn
    else return vn

keywordAsVariable :: String -> Parser a
keywordAsVariable = customFailure . KeywordAsVariable

alphanum :: Parser String
alphanum = lexeme $ takeWhileP Nothing isAlphaNum

tyIdentifier :: Parser String
tyIdentifier = (:) <$> upperChar <*> option "" alphanum <?> "type variable name"

sc :: Parser ()
sc = L.space
  space1
  (L.skipLineComment "//")
  (L.skipBlockComment "/*" "*/")

lexeme :: Parser a -> Parser a
lexeme = L.lexeme sc

symbol :: String -> Parser String
symbol = L.symbol sc

pKeyword :: String -> Parser ()
pKeyword keyword = void $ lexeme (string keyword <* notFollowedBy alphaNumChar)

pair :: (String, String) -> Parser b -> Parser b
pair (beg, end) = between (symbol beg) (symbol end)

parens :: Parser a -> Parser a
parens = pair ("(", ")")

brackets :: Parser a -> Parser a
brackets = pair ("[", "]")

comma, equal, period, colon, semicolon :: Parser ()
comma = void $ symbol ","
equal = void $ symbol "="
period = void $ symbol "."
colon = void $ symbol ":"
semicolon = void $ symbol ";"

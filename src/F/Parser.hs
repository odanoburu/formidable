{-# LANGUAGE StrictData #-}
module F.Parser (Parser, parseCommands, pix, term, typeP) where


import F.Syntax ( Binding(..), Command(..), Info(..), Term(..), Type(..))


import Control.Monad (void)
import Control.Monad.Combinators.Expr (makeExprParser, Operator(..))
import Data.Bifunctor (bimap)
import Data.Char (isAlphaNum)
import Data.Set (Set)
import qualified Data.Set as S
import Prelude hiding (abs)
import Text.Megaparsec hiding (State)
import Text.Megaparsec.Char ( alphaNumChar, lowerChar, space1
                            , string, upperChar )
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
    eval = Eval <$> info <*> term
    bind = Bind <$> info <*> varIdentifier <*> (varBind <|> termBind)
      <|> Bind <$> info <*> tyIdentifier
                        <*> ((TypeBind <$> (equal *> typeP)) <|> pure TyVarBind)
      where
        varBind = VarBind <$> (colon *> typeP)
        termBind = TermBind <$> (equal *> term) <*> pure Nothing
    someBind = fail "TBI - somebind"


typeAtom :: Parser Type
typeAtom = parens typeP
  <|> allTy
  <|> someTy
  <|> (TyBool <$ symbol "Bool" <?> "Bool type")
  <|> (TyVar pix pix <$> tyIdentifier <?> "type variable")
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
    var = Var <$> info <*> varIdentifier <*> pure pix <*> pure pix
    abs = Abs <$> info
      <*> (pKeyword "lambda" *> varIdentifier <* colon)
      <*> typeP <* period
      <*> term <?> "lambda abstraction"
    tAbs = TAbs <$> info
      <*> (pKeyword "Lambda" *> tyIdentifier <* period)
      <*> term <?> "type abstraction"
    tPack = TPack <$> info
      <*> (symbol "{" *> symbol "*" *> typeP)
      <*> (comma *> term <* symbol "}")
      <*> (pKeyword "as" *> typeP)
    tUnpack = TUnpack <$> info
      <*> (pKeyword "let" *> symbol "{" *> tyIdentifier)
      <*> (comma *> varIdentifier <* symbol "}")
      <*> (symbol "=" *> term <* pKeyword "in")
      <*> term
    bool = TTrue <$> info <* symbol "#t" <|> TFalse <$> info <* symbol "#f"
    tIf = TIf <$> info
      <*> (pKeyword "if" *> term)
      <*> (pKeyword "then" *> term)
      <*> (pKeyword "else" *> term)


term :: Parser Term
term = makeExprParser termAtom table
  where
    table = [ [ InfixL (App <$> info <* symbol "")
              , Postfix ((\i tyT t -> TApp i t tyT) <$> info <*> brackets typeP) ] ]


---
-- auxiliary definitions
keywords :: Set String
keywords = S.fromList ["lambda", "in", "let", "as", "if", "then", "else"]

varIdentifier :: Parser String
varIdentifier = do
  vn <- (:) <$> lowerChar <*> alphanum <?> "variable name"
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

info :: Parser Info
info = Offset <$> getOffset

pix :: Int
-- placeholder index
pix = -1

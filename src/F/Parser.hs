{-# LANGUAGE StrictData #-}
module F.Parser (Parser, parseCommands, parseTerm, pix, term, typeP) where


import F.Syntax ( Binding(..), Command(..), Info(..), Term(..), Type(..), pix)


import Control.Monad (void)
import Control.Monad.Combinators.Expr (makeExprParser, Operator(..))
import Control.Monad.Combinators.NonEmpty (some)
import Data.Bifunctor (bimap)
import Data.Char (isAlphaNum, isAsciiLower, isAsciiUpper)
import Data.Set (Set)
import qualified Data.Set as S
import Numeric.Natural (Natural)
import Prelude hiding (abs, pred, succ)
import Text.Megaparsec hiding (State, some)
import Text.Megaparsec.Char ( alphaNumChar, char, space1
                            , string )
--import Text.Megaparsec.Debug (dbg)
import qualified Text.Megaparsec.Char.Lexer as L
import Data.List.NonEmpty (NonEmpty(..))


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
parseCommands = parseResult commands

parseTerm :: String -> Either String Term
parseTerm = parseResult term ""

---
-- parser
parseResult :: Parser a -> FilePath -> String -> Either String a
parseResult p fp input = bimap errorBundlePretty id
  $ parse (sc *> p <* eof) fp input

commands :: Parser [Command]
commands = sepEndBy command semicolon


command :: Parser Command
command = try bind <|> someBind <|> eval
  where
    eval = Eval <$> info <*> term
    bind
      = Bind <$> info <*> termIdentifier <*> (varBind <|> termBind)
      <|> Bind <$> info <*> tyIdentifier
                        <*> ((TypeBind <$> (equal *> typeP)) <|> pure TyVarBind)
      where
        varBind = VarBind <$> (colon *> typeP)
        termBind = TermBind <$> (equal *> term) <*> pure Nothing
    someBind
      = SomeBind
      <$> info
      <*> (lcurly *> tyIdentifier <* comma)
      <*> (termIdentifier <* rcurly)
      <*> (equal *> term)


typeAtom :: Parser Type
typeAtom = parens typeP
  <|> allTy
  <|> someTy
  <|> (TyBool <$ pKeyword "Bool" <?> "Bool type")
  <|> (TyNat <$ pKeyword "Nat" <?> "Nat type")
  <|> try (TyVar pix pix <$> tyIdentifier <?> "type variable")
  <|> (TyTuple <$> tupleOf typeP)
  <|> TyList <$> (pKeyword "List" *> typeP)
  where
    allTy = TyAll
      <$> ((pKeyword "Forall" <|> symbol_ "∀") *> tyIdentifier <* period)
      <*> typeP <?> "universal type"
    someTy = TySome
      <$> ((pKeyword "Exists" <|> symbol_ "∃") *> tyIdentifier <* comma)
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
  -- <|> fix
  <|> tuple
  <|> bool
  <|> tIf
  <|> nat
  <|> succ
  <|> pred
  <|> isZero
  where
    var = Var <$> info <*> termIdentifier <*> pure pix <*> pure pix
    abs = Abs <$> info
      <*> ((pKeyword "lambda" <|> symbol_ "λ") *> termIdentifier <* colon)
      <*> typeP <* period
      <*> term <?> "lambda abstraction"
    tAbs = TAbs <$> info
      <*> ((pKeyword "Lambda" <|> symbol_ "Λ") *> tyIdentifier <* period)
      <*> term <?> "type abstraction"
    tPack = TPack <$> info
      <*> (lcurly *> symbol "*" *> typeP)
      <*> (comma *> term <* rcurly)
      <*> (pKeyword "as" *> typeP)
    tUnpack = TUnpack <$> info
      <*> (pKeyword "let" *> lcurly *> tyIdentifier)
      <*> (comma *> termIdentifier <* rcurly)
      <*> (equal *> term <* pKeyword "in")
      <*> term
    -- fix = Fix
    --   <$> info
    --   <*> (pKeyword "fix" *> term)
    tuple = Tuple
      <$> info
      <*> tupleOf term
    bool = TTrue <$> info <* symbol "#t" <|> TFalse <$> info <* symbol "#f"
    tIf = TIf <$> info
      <*> (pKeyword "if" *> term)
      <*> (pKeyword "then" *> term)
      <*> (pKeyword "else" *> term)
    nat = toNat <$> info <*> lexeme L.decimal
      where
        toNat :: Info -> Natural -> Term
        toNat fi 0 = TZero fi
        toNat fi n = TSucc fi (toNat fi (n-1))
    succ = TSucc
      <$> info
      <*> (pKeyword "succ" *> term)
    pred = TPred
      <$> info
      <*> (pKeyword "pred" *> term)
    isZero = TIsZero <$> info <*> (pKeyword "isZero" *> term)


term :: Parser Term
term = makeExprParser termAtom table
  where
    table = [ [ -- FIXME: application has highest precedence of all,
                -- but then we try to parse ! operator and fail
                -- because it sees a space and thinks its an
                -- application…
                InfixL (App <$> info <* symbol "" <* notFollowedBy "!")
              , InfixL (TupleProj <$> info <* symbol "!")
              , Postfix severalAt -- ((\i tyT t -> TApp i t tyT) <$> info <*> atsign typeP)
              , Postfix ((\i ty t -> Ascribe i t ty)
                         <$> info <*> (symbol "as" *> typeP))
              ]
            ]
    severalAt = do
      args <- some ((,) <$> info <*> atsign typeP)
      return $ case args of
        (i, ty):|args' -> foldr go (\t -> TApp i t ty) args'
          where
            go (i', ty') f = \t -> TApp i' (f t) ty'


tupleOf :: Parser a -> Parser [a]
tupleOf p = between (symbol "<") (symbol ">") (sepEndBy p comma)


---
-- auxiliary definitions
keywords :: Set String
keywords
  = S.fromList [
  "Forall", "Exists", "λ", "lambda", "Λ", "Lambda", "in",
  "let", "as", "if", "then", "else", "succ", "pred", "isZero",
  "Nat", "Bool", "List"
  ]

termIdentifier :: Parser String
termIdentifier = notKeyword (
  (:) <$> satisfy isAsciiLower -- use ascii or else λx is a valid
                               -- identifier, which is confusing
    <*> alphanum <?> "variable name"
  )

notKeyword :: Parser String -> Parser String
notKeyword p
  = p
  >>= \vn -> if vn `S.member` keywords
             then keywordAsVariable vn
             else return vn


keywordAsVariable :: String -> Parser a
keywordAsVariable = customFailure . KeywordAsVariable

alphanum :: Parser String
alphanum = lexeme $ takeWhileP Nothing isAlphaNum

tyIdentifier :: Parser String
tyIdentifier = notKeyword (
  (:) <$> satisfy isAsciiUpper <*> alphanum <?> "type variable name"
  )


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

atsign, parens :: Parser a -> Parser a
parens = pair ("(", ")")
atsign p = char '@' *> p

symbol_ :: String -> Parser ()
symbol_ = void . symbol

comma, equal, period, colon, semicolon, lcurly, rcurly :: Parser ()
comma = symbol_ ","
equal = symbol_ "="
period = symbol_ "."
colon = symbol_ ":"
semicolon = symbol_ ";"
lcurly = symbol_ "{"
rcurly = symbol_ "}"

info :: Parser Info
info = Offset <$> getOffset

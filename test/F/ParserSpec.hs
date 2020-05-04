module F.ParserSpec (spec) where

import Data.Text (Text)
import Test.Hspec
import Text.Megaparsec (parse)

import F.Type (Term(..), Type(..))
import F.Parser (term)

termParsesAs :: Text -> Term -> Expectation
input `termParsesAs` this = parse term "" input `shouldBe` Right this

spec :: Spec
spec = describe "parsing" $ do
  it "parses lambda" $
    "lambda x : Bool . x" `termParsesAs` Abs () "x" TyBool (Var () "x")

  it "parses lambda with parens" $
    "(lambda x:Bool . x )" `termParsesAs` Abs () "x" TyBool (Var () "x")

  it "parses lambda with inline comment" $
    "lambda x: Bool. x // oi" `termParsesAs` Abs () "x" TyBool (Var () "x")

  it "parses lambda with block comment" $
    "lambda x :Bool. /* oi */ x" `termParsesAs` Abs () "x" TyBool (Var () "x")

  it "parses variable" $
    "x" `termParsesAs` Var () "x"

  it "parses application" $
    "(lambda y:Bool. y) x" `termParsesAs`
    App () (Abs () "y" TyBool (Var () "y")) (Var () "x")

  it "parses type abstraction" $
    "(lambda X. y)" `termParsesAs`
    TAbs () "X" (Var () "y")

  it "parses type application" $
    "(lambda y:Bool. y) [X]" `termParsesAs`
    TApp () (Abs () "y" TyBool (Var () "y")) (TyVar (-1) (-1))

  it "parses packing" $
    "{*List, nil} as Stack" `termParsesAs`
    TPack () (TyVar (-1) (-1)) (Var () "nil") (TyVar (-1) (-1))

  it "parses unpacking" $
    "let {Stack, st} = f stackADT in st" `termParsesAs`
    TUnpack () "Stack" "st" (App () (Var () "f") (Var () "stackADT")) (Var () "st")

  

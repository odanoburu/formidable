module F.ParserSpec (spec) where

import Data.Text (Text)
import Test.Hspec
import Text.Megaparsec (parse)

import F.Syntax (Info(..), Term(..), Type(..))
import F.Parser (term)

termParsesAs :: String -> Term -> Expectation
input `termParsesAs` this = parse term "" input `shouldBe` Right this

d :: Info
d = Offset 0

spec :: Spec
spec = describe "parsing" $ do
  it "parses lambda" $
    "lambda x : Bool . x" `termParsesAs` Abs d "x" TyBool (Var d "x" (-1) (-1))

  it "parses lambda with parens" $
    "(lambda x:Bool . x )" `termParsesAs` Abs d "x" TyBool (Var d "x" (-1) (-1))

  it "parses lambda with inline comment" $
    "lambda x: Bool. x // oi" `termParsesAs` Abs d "x" TyBool (Var d "x" (-1) (-1))

  it "parses lambda with block comment" $
    "lambda x :Bool. /* oi */ x" `termParsesAs` Abs d "x" TyBool (Var d "x" (-1) (-1))

  it "parses variable" $
    "x" `termParsesAs` Var d "x" (-1) (-1)

  it "parses application" $
    "(lambda y:Bool. y) x" `termParsesAs`
    App d (Abs d "y" TyBool (Var d "y" (-1) (-1))) (Var d "x" (-1) (-1))

  it "parses type abstraction" $
    "(Lambda X. y)" `termParsesAs`
    TAbs d "X" (Var d "y" (-1) (-1))

  it "parses type application" $
    "(lambda y:Bool. y) [X]" `termParsesAs`
    TApp d (Abs d "y" TyBool (Var d "y" (-1) (-1))) (TyVar (-1) (-1) "X")

  it "parses packing" $
    "{*List, nil} as Stack" `termParsesAs`
    TPack d (TyVar (-1) (-1) "List") (Var d "nil" (-1) (-1)) (TyVar (-1) (-1) "Stack")

  it "parses unpacking" $
    "let {Stack, st} = f stackADT in st" `termParsesAs`
    TUnpack d "Stack" "st" (App d (Var d "f"(-1) (-1)) (Var d "stackADT" (-1) (-1))) (Var d "st" (-1) (-1))

  -- types
  it "parses function types" $
    "(lambda x:Bool -> Bool. x )" `termParsesAs`
    Abs d "x" (TyArr TyBool TyBool) (Var d "x" (-1) (-1))

  it "parses type variables" $
    "lambda x:B. x" `termParsesAs` Abs d "x" (TyVar (-1) (-1) "B") (Var d "x" (-1) (-1))

  it "parses the universal type" $
    "lambda x:forall X. X. x" `termParsesAs`
    Abs d "x" (TyAll "X" $ TyVar (-1) (-1) "X") (Var d "x" (-1) (-1))

  it "parses the existential type" $
    "lambda x:exists X, X. x" `termParsesAs`
    Abs d "x" (TySome "X" $ TyVar (-1) (-1) "X") (Var d "x" (-1) (-1))

  -- add-ons
  it "parses boolean true" $
    "#t" `termParsesAs` TTrue d

  it "parses boolean false" $
    "#f" `termParsesAs` TFalse d

  it "parses if conditionals" $
    "if #t then #f else #t" `termParsesAs` TIf d (TTrue d) (TFalse d) (TTrue d)

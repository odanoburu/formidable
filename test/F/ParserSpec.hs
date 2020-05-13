module F.ParserSpec (spec) where

import Data.Text (Text)
import Test.Hspec
import Text.Megaparsec (parse)

import F.Syntax (Term(..), Type(..))
import F.Parser (term)

termParsesAs :: String -> Term -> Expectation
input `termParsesAs` this = parse term "" input `shouldBe` Right this

spec :: Spec
spec = describe "parsing" $ do
  it "parses lambda" $
    "lambda x : Bool . x" `termParsesAs` Abs () "x" TyBool (Var () "x" (-1) (-1))

  it "parses lambda with parens" $
    "(lambda x:Bool . x )" `termParsesAs` Abs () "x" TyBool (Var () "x" (-1) (-1))

  it "parses lambda with inline comment" $
    "lambda x: Bool. x // oi" `termParsesAs` Abs () "x" TyBool (Var () "x" (-1) (-1))

  it "parses lambda with block comment" $
    "lambda x :Bool. /* oi */ x" `termParsesAs` Abs () "x" TyBool (Var () "x" (-1) (-1))

  it "parses variable" $
    "x" `termParsesAs` Var () "x" (-1) (-1)

  it "parses application" $
    "(lambda y:Bool. y) x" `termParsesAs`
    App () (Abs () "y" TyBool (Var () "y" (-1) (-1))) (Var () "x" (-1) (-1))

  it "parses type abstraction" $
    "(Lambda X. y)" `termParsesAs`
    TAbs () "X" (Var () "y" (-1) (-1))

  it "parses type application" $
    "(lambda y:Bool. y) [X]" `termParsesAs`
    TApp () (Abs () "y" TyBool (Var () "y" (-1) (-1))) (TyVar (-1) (-1) "X")

  it "parses packing" $
    "{*List, nil} as Stack" `termParsesAs`
    TPack () (TyVar (-1) (-1) "List") (Var () "nil" (-1) (-1)) (TyVar (-1) (-1) "Stack")

  it "parses unpacking" $
    "let {Stack, st} = f stackADT in st" `termParsesAs`
    TUnpack () "Stack" "st" (App () (Var () "f"(-1) (-1)) (Var () "stackADT" (-1) (-1))) (Var () "st" (-1) (-1))

  -- types
  it "parses function types" $
    "(lambda x:Bool -> Bool. x )" `termParsesAs`
    Abs () "x" (TyArr TyBool TyBool) (Var () "x" (-1) (-1))

  it "parses type variables" $
    "lambda x:B. x" `termParsesAs` Abs () "x" (TyVar (-1) (-1) "B") (Var () "x" (-1) (-1))

  it "parses the universal type" $
    "lambda x:forall X. X. x" `termParsesAs`
    Abs () "x" (TyAll "X" $ TyVar (-1) (-1) "X") (Var () "x" (-1) (-1))

  it "parses the existential type" $
    "lambda x:exists X, X. x" `termParsesAs`
    Abs () "x" (TySome "X" $ TyVar (-1) (-1) "X") (Var () "x" (-1) (-1))


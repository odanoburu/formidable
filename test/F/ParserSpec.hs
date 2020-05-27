module F.ParserSpec (spec) where

import Test.Hspec
import Text.Megaparsec (parse)

import F.Syntax (Info(..), Term(..), Type(..))
import F.Parser (Parser, pix, term, typeP)

termParsesAs :: String -> Term -> Expectation
input `termParsesAs` this = parsesAs input term this

typeParsesAs :: String -> Type -> Expectation
input `typeParsesAs` this = parsesAs input typeP this

parsesAs :: (Eq a, Show a) => String -> Parser a -> a -> Expectation
parsesAs input p this = parse p "" input `shouldBe` Right this

d :: Info
d = Offset 0

spec :: Spec
spec = describe "parsing" $ do
  termSpec
  typeSpec

termSpec :: Spec
termSpec = describe "term" $ do
  specify "lambda" $
    "lambda x : Bool . x" `termParsesAs` Abs d "x" TyBool (Var d "x" pix pix)

  specify "lambda with parens" $
    "(lambda x:Bool . x )" `termParsesAs` Abs d "x" TyBool (Var d "x" pix pix)

  specify "lambda with inline comment" $
    "λ x: Bool. x // oi" `termParsesAs` Abs d "x" TyBool (Var d "x" pix pix)

  specify "lambda with block comment" $
    "lambda x :Bool. /* oi */ x" `termParsesAs` Abs d "x" TyBool (Var d "x" pix pix)

  specify "variable" $
    "x" `termParsesAs` Var d "x" pix pix

  specify "application" $
    "(lambda y:Bool. y) x" `termParsesAs`
    App d (Abs d "y" TyBool (Var d "y" pix pix)) (Var d "x" pix pix)

  specify "type abstraction" $
    "(Lambda X. y)" `termParsesAs`
    TAbs d "X" (Var d "y" pix pix)

  specify "type application" $
    "(lambda y:Bool. y) [X]" `termParsesAs`
    TApp d (Abs d "y" TyBool (Var d "y" pix pix)) (TyVar pix pix "X")

  specify "packing" $
    "{*List, nil} as Stack" `termParsesAs`
    TPack d (TyVar pix pix "List") (Var d "nil" pix pix) (TyVar pix pix "Stack")

  specify "unpacking" $
    "let {Stack, st} = f stackADT in st" `termParsesAs`
    TUnpack d "Stack" "st" (App d (Var d "f"pix pix) (Var d "stackADT" pix pix)) (Var d "st" pix pix)

  -- types
  specify "function types" $
    "(lambda x:Bool -> Bool. x )" `termParsesAs`
    Abs d "x" (TyArr TyBool TyBool) (Var d "x" pix pix)

  specify "type variables" $
    "λ x:B. x" `termParsesAs` Abs d "x" (TyVar pix pix "B") (Var d "x" pix pix)

  specify "with the universal type" $
    "λ x:∀ X. X. x" `termParsesAs`
    Abs d "x" (TyAll "X" $ TyVar pix pix "X") (Var d "x" pix pix)

  specify "with the existential type" $
    "λ x:∃X, X. x" `termParsesAs`
    Abs d "x" (TySome "X" $ TyVar pix pix "X") (Var d "x" pix pix)

  -- add-ons
  specify "boolean true" $
    "#t" `termParsesAs` TTrue d

  specify "boolean false" $
    "#f" `termParsesAs` TFalse d

  specify "if conditionals" $
    "if #t then #f else #t" `termParsesAs` TIf d (TTrue d) (TFalse d) (TTrue d)



typeSpec :: Spec
typeSpec = describe "type" $ do
  specify "variable" $
    "ATYPE" `typeParsesAs` TyVar pix pix "ATYPE"
  specify "boolean" $
    "Bool" `typeParsesAs` TyBool

  specify "universally quantified" $
    "Forall B . B" `typeParsesAs` TyAll "B" (TyVar pix pix "B")

  specify "existentially quantified" $
    "Exists C, C->Bool" `typeParsesAs` TySome "C" (TyArr (TyVar pix pix "C")
                                                   TyBool)

  specify "arrow type" $
    "Bool -> A -> Bool" `typeParsesAs` TyArr TyBool (TyArr (TyVar pix pix "A")
                                                           TyBool)

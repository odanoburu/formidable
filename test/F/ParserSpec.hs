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
    "lambda x :Bool. /* oi */ x"
      `termParsesAs` Abs d "x" TyBool (Var d "x" pix pix)

  specify "variable" $
    "x" `termParsesAs` Var d "x" pix pix

  specify "application" $
    "(lambda y:Bool. y) x" `termParsesAs`
    App d (Abs d "y" TyBool (Var d "y" pix pix)) (Var d "x" pix pix)

  specify "type abstraction" $
    "(Lambda X. y)" `termParsesAs`
    TAbs d "X" (Var d "y" pix pix)

  specify "type application" $
    "(lambda y:Bool. y) @X" `termParsesAs`
    TApp d (Abs d "y" TyBool (Var d "y" pix pix)) (TyVar pix pix "X")

  specify "packing" $
    "{*MyList, myNil} as Stack" `termParsesAs`
    TPack d (TyVar pix pix "MyList") (Var d "myNil" pix pix) (TyVar pix pix "Stack")

  specify "unpacking" $
    "let {Stack, st} = f stackADT in st" `termParsesAs`
    TUnpack d "Stack" "st" (App d (Var d "f"pix pix)
                            (Var d "stackADT" pix pix)) (Var d "st" pix pix)

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
  -- specify "fix" $
  --   "fix (lambda x:Bool. #t)" `termParsesAs` Fix d (Abs d "x" TyBool (TTrue d))

  specify "empty tuple" $
    "<>" `termParsesAs` Tuple d []

  specify "tuple" $
    "<0, #f>" `termParsesAs` Tuple d [TZero d, TFalse d]

  specify "tuple indexing" $
    "<0, <0, 1>, > ! 1 ! 0" `termParsesAs`
    TupleProj d (TupleProj d
                 (Tuple d [TZero d,Tuple d [TZero d,TSucc d (TZero d)]])
                 (TSucc d (TZero d)))
      (TZero d)

  specify "boolean true" $
    "#t" `termParsesAs` TTrue d

  specify "boolean false" $
    "#f" `termParsesAs` TFalse d

  specify "if conditionals" $
    "if #t then #f else #t" `termParsesAs` TIf d (TTrue d) (TFalse d) (TTrue d)

  specify "number 0" $
    "0" `termParsesAs` TZero d

  specify "number 3" $
    "3" `termParsesAs` TSucc d (TSucc d (TSucc d (TZero d)))

  specify "succ" $
    "succ 2" `termParsesAs` TSucc d (TSucc d (TSucc d (TZero d)))

  specify "pred" $
    "pred 1" `termParsesAs` TPred d (TSucc d (TZero d))

  specify "isZero" $
    "isZero 2" `termParsesAs` TIsZero d (TSucc d (TSucc d (TZero d)))




typeSpec :: Spec
typeSpec = describe "type" $ do
  specify "variable" $
    "ATYPE" `typeParsesAs` TyVar pix pix "ATYPE"

  specify "boolean" $
    "Bool" `typeParsesAs` TyBool

  specify "natural" $
    "Nat" `typeParsesAs` TyNat

  specify "universally quantified" $
    "Forall B . B" `typeParsesAs` TyAll "B" (TyVar pix pix "B")

  specify "existentially quantified" $
    "Exists C, C->Bool" `typeParsesAs` TySome "C" (TyArr (TyVar pix pix "C")
                                                   TyBool)

  specify "arrow type" $
    "Bool -> A -> Bool" `typeParsesAs` TyArr TyBool (TyArr (TyVar pix pix "A")
                                                           TyBool)

  specify "empty tuple type" $
    "<>" `typeParsesAs` TyTuple []

  specify "tuple type" $
    "<Bool, Nat>" `typeParsesAs` TyTuple [TyBool, TyNat]

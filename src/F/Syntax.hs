{-# LANGUAGE StrictData #-}
module F.Syntax (
  Command(..), Info, Type(..), Term(..), Binding(..), Context(..), TopLevel(..),
  addName,
  termSubstTop,
  tytermSubstTop,
  typeSubstTop,
  termShift,
  typeShift,
  getTypeFromContext,
  nameToIndex,
  addBinding,
  getBinding,
  showError,
  ) where


import Data.List (findIndex)
import Data.Semigroup (Sum(..))
import Prelude hiding ((!!))


---
-- types
type Info = ()


data Type
  -- primitive
  = TyBool
  -- constructors
  | TyId String
  | TyVar Int Int String  -- type variable
  | TyArr Type Type       -- type of functions
  | TyAll String Type     -- universal type
  | TySome String Type    -- existential type
  deriving (Eq, Show)


data Term
-- pure LC
  = Var Info String Int Int               -- variable
  | Abs Info String Type Term             -- abstraction
  | App Info Term Term                    -- application
-- type stuff
  | TAbs Info String Term                 -- type abstraction
  | TApp Info Term Type                   -- type application
  | TPack Info Type Term Type             -- packing
  | TUnpack Info String String Term Term  -- unpacking
-- add-ons
  | TTrue Info
  | TFalse Info
  | TIf Info Term Term Term
  deriving (Eq, Show)


data Binding
  = NameBind
  | VarBind Type
  | TyVarBind
  | TermBind Term (Maybe Type)
  deriving (Show)


data Context = Ctx [(String, Binding)] (Sum Int)
  deriving (Show)

instance Semigroup Context where
  Ctx ctx n <> Ctx ctx' n' = Ctx (ctx <> ctx') (n <> n')

instance Monoid Context where
  mempty = Ctx [] (Sum 0)


data Command
  = Eval Info Term
  | Bind Info String Binding
  | SomeBind Info String String Term
  deriving (Show)


data TopLevel = TopLevel Context [Command]
  deriving (Show)

instance Semigroup TopLevel where
  TopLevel ctx cmds <> TopLevel ctx' cmds' = TopLevel (ctx <> ctx') (cmds <> cmds')

instance Monoid TopLevel where
  mempty = TopLevel mempty mempty


---

tymap :: (Int -> Int -> Int -> (String -> Type)) -> Int -> Type -> Type
tymap onVar = go
  where
    go _ TyBool = TyBool
    go _ (TyId tn) = TyId tn
    go c (TyArr tyT1 tyT2) = TyArr (go c tyT1) (go c tyT2)
    go c (TyVar x n tn) = onVar c x n tn
    go c (TyAll tyX tyT2) = TyAll tyX $ go (c+1) tyT2
    go c (TySome tyX tyT2) = TySome tyX $ go (c+1) tyT2


typeShiftAbove :: Int -> Int -> Type -> Type
typeShiftAbove d = tymap go
  where
    go c' x n =
      if x >= c'
      then if x + d < 0
           then error "Scoping error"
           else TyVar (x+d) (n+d)
      else TyVar x (n+d)


typeShift :: Int -> Type -> Type
typeShift d = typeShiftAbove d 0


typeSubst :: Type -> Int -> Type -> Type
typeSubst tyS = tymap go
  where
    go j x n = if x == j then const (typeShift j tyS) else TyVar x n


typeSubstTop :: Type -> Type -> Type
typeSubstTop tyS tyT = typeShift (-1) (typeSubst (typeShift 1 tyS) 0 tyT)


tmmap :: (Info -> Int -> Int -> Int -> Term) -> (Int -> Type -> Type)
  -> Int -> Term -> Term
tmmap onVar onType = go
  where
    go c (Var fi _ x n) = onVar fi c x n
    go c (Abs fi x tyT1 t2) = Abs fi x (onType c tyT1) $ go (c+1) t2
    go c (App fi t1 t2) = App fi (go c t1) (go c t2)
    go c (TAbs fi tyX t2) = TAbs fi tyX $ go (c+1) t2
    go c (TApp fi t1 tyT2) = TApp fi (go c t1) (onType c tyT2)
    go c (TPack fi tyT1 t2 tyT3) =
      TPack fi (onType c tyT1) (go c t2) (onType c tyT3)
    go c (TUnpack fi tyX x t1 t2) =
      TUnpack fi tyX x (go c t1) (go (c+2) t2)
    go _ (TTrue fi) = TTrue fi
    go _ (TFalse fi) = TFalse fi
    go c (TIf fi tcond tt tf) = TIf fi (go c tcond) (go c tt) (go c tf)


termShiftAbove :: Int -> Int -> Term -> Term
termShiftAbove d = tmmap onVar onType
  where
    onVar fi c x n = if x >= c then Var fi "" (x+d) (n+d) else Var fi "" x (n+d)
    onType = typeShiftAbove d


termShift :: Int -> Term -> Term
termShift d = termShiftAbove d 0


termSubst :: Int -> Term -> Term -> Term
termSubst j' s = tmmap onVar onType j'
  where
    onVar fi j x n = if x == j then termShift j s else Var fi "" x n
    onType _ tyT = tyT


tytermSubst :: Type -> Int -> Term -> Term
tytermSubst tyS = tmmap onVar onType
  where
    onVar fi _c = Var fi ""
    onType = typeSubst tyS


termSubstTop :: Term -> Term -> Term
termSubstTop s t = termShift (-1) $ termSubst 0 (termShift 1 s) t


tytermSubstTop :: Type -> Term -> Term
tytermSubstTop tyS t = termShift (-1) $ tytermSubst (typeShift 1 tyS) 0 t

---
-- context
addBinding :: Context -> String -> Binding -> Context
addBinding (Ctx ctx n) x bind = Ctx ((x,bind):ctx) (n+1)

addName :: Context -> String -> Context
addName ctx x = addBinding ctx x NameBind


nameToIndex :: Info -> Context -> String -> Maybe Int
nameToIndex _ (Ctx ctx _) x = ((== x) . fst) `findIndex` ctx


bindingShift :: Int -> Binding -> Binding
bindingShift _ NameBind = NameBind
bindingShift d (VarBind tyT) = VarBind $ typeShift d tyT
bindingShift _ TyVarBind = TyVarBind
bindingShift d (TermBind t mTy)
  = TermBind (termShift d t) $ fmap (typeShift d) mTy


getBinding :: Info -> Context -> Int -> Binding
getBinding fi (Ctx ctx _) i = case ctx !! i of
  Just (_, bind) -> bindingShift (i+1) bind
  Nothing -> showError fi "Variable lookup failure*IMPROVEMSG*"

getTypeFromContext :: Info -> Context -> Int -> Type
getTypeFromContext fi ctx i = case getBinding fi ctx i of
  VarBind tyT -> tyT
  _ ->
    showError fi
              "getTypeFromContext: Wrong kind of binding for variable*IMPROVEMSG*"


---
-- auxiliary definitions
showError :: Info -> String -> a
showError fi msg = error $ unwords [show fi, msg]

infixl 9  !!
(!!) :: [a] -> Int -> Maybe a
(x:_) !! 0 = Just x
(_:xs) !! n = xs !! (n-1)
[] !! _ = Nothing

{-# LANGUAGE StrictData #-}
module F.Syntax (
  (!!),
  Command(..), Info(..), Type(..), Term(..), Binding(..), Context(..),
  TopLevel(..),
  addName,
  dummyInfo,
  err,
  makeContext,
  termSubstTop,
  tytermSubstTop,
  typeSubstTop,
  termShift,
  typeShift,
  getTypeFromContext,
  nameToIndex,
  addBinding,
  getBinding,
  prettyBinding,
  showError,
  showTermType,
  ) where


import Data.List (findIndex)
import Data.Semigroup (Sum(..))
import Data.Text.Prettyprint.Doc ((<>), (<+>), Doc, Pretty(..),
                                  align, encloseSep, flatAlt, group,
                                  softline)
--import Debug.Trace (trace)
import Prelude hiding ((!!))


---
-- types
newtype Info = Offset Int
  deriving (Show)

instance Eq Info where
  _ == _ = True -- we don't care


dummyInfo :: Info
dummyInfo = Offset (-1)


data Type
  -- primitive
  = TyBool
  | TyNat
  -- constructors
  | TyId String
  | TyVar Int Int String  -- type variable
  | TyArr Type Type       -- type of functions
  | TyAll String Type     -- universal type
  | TySome String Type    -- existential type
  -- add-ons
  | TyTuple [Type]
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
  | Fix Info Term
  | FixOp (Maybe Type)
  | Tuple Info [Term]
  | TupleProj Info Term Term
  | TTrue Info
  | TFalse Info
  | TIf Info Term Term Term
  | TZero Info
  | TSucc Info Term
  | TPred Info Term
  | TIsZero Info Term
  deriving (Eq, Show)


data Binding
  = NameBind
  | VarBind Type
  | TyVarBind
  | TermBind Term (Maybe Type)
  | TypeBind Type
  deriving (Show)


data Context = Ctx [(String, Binding)] (Sum Int)

instance Show Context where
  show (Ctx bs _) = show bs

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
    go _ TyNat = TyNat
    go _ (TyId tn) = TyId tn
    go c (TyArr tyT1 tyT2) = TyArr (go c tyT1) (go c tyT2)
    go c (TyVar x n tn) = onVar c x n tn
    go c (TyAll tyX tyT2) = TyAll tyX $ go (c+1) tyT2
    go c (TySome tyX tyT2) = TySome tyX $ go (c+1) tyT2
    go c (TyTuple tys) = TyTuple $ fmap (go c) tys


typeShiftAbove :: Int -> Int -> Type -> Type
typeShiftAbove d = tymap go
  where
    go c x n =
      if x >= c
      then if x + d < 0
           then error "Scoping error"
           else TyVar (x+d) (n+d)
      else TyVar x (n+d)


typeShift :: Int -> Type -> Type
typeShift d = typeShiftAbove d 0


typeSubst :: Type -> Int -> Type -> Type
typeSubst tyS = tymap go
  where
    go j x n = if x == j then const $ typeShift j tyS else TyVar x n


typeSubstTop :: Type -> Type -> Type
typeSubstTop tyS tyT = typeShift (-1) (typeSubst (typeShift 1 tyS) 0 tyT)


tmmap :: (Info -> Int -> Int -> Int -> (String -> Term)) -> (Int -> Type -> Type)
  -> Int -> Term -> Term
tmmap onVar onType = go
  where
    go c (Var fi vn x n) = onVar fi c x n vn
    go c (Abs fi x tyT1 t2) = Abs fi x (onType c tyT1) $ go (c+1) t2
    go c (App fi t1 t2) = App fi (go c t1) (go c t2)
    go c (TAbs fi tyX t2) = TAbs fi tyX $ go (c+1) t2
    go c (TApp fi t1 tyT2) = TApp fi (go c t1) (onType c tyT2)
    go c (TPack fi tyT1 t2 tyT3) =
      TPack fi (onType c tyT1) (go c t2) (onType c tyT3)
    go c (TUnpack fi tyX x t1 t2) =
      TUnpack fi tyX x (go c t1) (go (c+2) t2)
    go _ f@FixOp{} = f
    go c (Fix fi t) = Fix fi $ go c t
    go c (Tuple fi ts) = Tuple fi $ fmap (go c) ts
    go c (TupleProj fi tu ti) = TupleProj fi (go c tu) (go c ti)
    go _ t@TTrue{} = t
    go _ f@TFalse{} = f
    go c (TIf fi tcond tt tf) = TIf fi (go c tcond) (go c tt) (go c tf)
    go _ z@TZero{} = z
    go c (TSucc fi t) = TSucc fi $ go c t
    go c (TPred fi t) = TPred fi $ go c t
    go c (TIsZero fi t) = TIsZero fi $ go c t


termShiftAbove :: Int -> Int -> Term -> Term
termShiftAbove d = tmmap onVar onType
  where
    onVar fi c x n = if x >= c then \vn -> Var fi vn (x+d) (n+d) else \vn -> Var fi vn x (n+d)
    onType = typeShiftAbove d


termShift :: Int -> Term -> Term
termShift d = termShiftAbove d 0


termSubst :: Int -> Term -> Term -> Term
termSubst j' s = tmmap onVar onType j'
  where
    onVar fi j x n vn = if x == j then termShift j s else Var fi vn x n
    onType _ tyT = tyT


tytermSubst :: Type -> Int -> Term -> Term
tytermSubst tyS = tmmap onVar onType
  where
    onVar fi _c i n vn = Var fi vn i n
    onType = typeSubst tyS


termSubstTop :: Term -> Term -> Term
termSubstTop s t = termShift (-1) $ termSubst 0 (termShift 1 s) t


tytermSubstTop :: Type -> Term -> Term
tytermSubstTop tyS t = termShift (-1) $ tytermSubst (typeShift 1 tyS) 0 t

---
-- context
makeContext :: [(String, Binding)] -> Context
makeContext bs = Ctx bs (Sum $ length bs)


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
bindingShift d (TypeBind ty)
  = TypeBind $ typeShift d ty


getBinding :: Info -> Context -> Int -> Binding
getBinding fi (Ctx ctx (Sum n)) i = case ctx !! i of
  Just (_, bind) -> bindingShift (i+1) bind
  Nothing -> variableLookupFailure fi i n


getTypeFromContext :: Info -> Context -> Int -> Type
getTypeFromContext fi ctx i = case getBinding fi ctx i of
  NameBind -> bindError
  (VarBind tyT) -> tyT
  TyVarBind -> bindError
  TermBind _ (Just tyT) -> tyT
  TermBind _ Nothing -> err fi $
    "No type for variable " ++ varname
  TypeBind _ -> bindError
  where
    varname = indexToName fi ctx i
    bindError =
      err fi $ "getTypeFromContext: Wrong kind of binding for variable "
               ++ varname


indexToName :: Info -> Context -> Int -> String
indexToName fi (Ctx ctx (Sum n)) i = case ctx !! i of
  Just (vn, _) -> vn
  Nothing -> variableLookupFailure fi i n

variableLookupFailure :: Info -> Int -> Int -> a
variableLookupFailure fi i n = err fi $
  unwords ["Variable lookup failure: offset was", show i,
            ", context size was", show n]


---
-- auxiliary definitions
err :: Info -> String -> a
err fi msg = error $ showError fi msg


showError :: Info -> String -> String
showError (Offset n) msg = concat [show n, ":", msg]


infixl 9  !! -- safe indexing
(!!) :: [a] -> Int -> Maybe a
(x:_) !! 0 = Just x
(_:xs) !! n = xs !! (n-1)
[] !! _ = Nothing


prettyType :: Context -> Type -> Doc a
prettyType = go
  where
    go ctx (TyAll tyX ty) =
      let (ctx', tyX') = freshName ctx tyX
      in align
      $ "∀" <+> pretty tyX' <> "." <> softline
      <> prettyType ctx' ty
    go ctx (TyArr tyL tyR) = align
      $ prettyType ctx tyL <+> "->"
      <> softline <> prettyType ctx tyR
    go _ (TyVar _ _ x) = pretty x
    go _ (TyId b) = pretty b
    go ctx (TyTuple tys) = prettyTuple $ fmap (prettyType ctx) tys
    go _ TyBool = "Bool"
    go _ TyNat = "Nat"
    go ctx (TySome tyX ty) =
      let (ctx', tyX') = freshName ctx tyX
      in align
      $ "∃" <+> pretty tyX' <> "," <> softline
      <> prettyType ctx' ty <> ""


prettyTuple :: [Doc a] -> Doc a
prettyTuple = group
  . encloseSep (flatAlt "< " "<")
               (flatAlt " >" ">")
               ", "


freshName :: Context -> String -> (Context, String)
freshName c@(Ctx ctx (Sum n)) x =
  if isBound
  then freshName c $ x ++ "'"
  else (Ctx ((x, NameBind):ctx) (Sum $ n+1), x)
  where
    isBound = x `elem` fmap fst ctx


prettyTerm :: Context -> Term -> Doc a
prettyTerm ctx (Abs _ x ty t) =
  let (ctx', x') = freshName ctx x
  in align
  $ "λ" <+> pretty x' <> ":" <> prettyType ctx ty <> "."
  <> softline <> prettyTerm ctx' t
prettyTerm _ (FixOp Nothing) = "fix"
prettyTerm ctx (FixOp (Just ty)) = "fix" <+> "[" <> prettyType ctx ty <> "]"
prettyTerm ctx (Fix _ t)
  = align
  $ "fix" <+> prettyTerm ctx t
prettyTerm ctx (TIf _ tcond tt tf)
  = align
  $ "if" <+> prettyTerm ctx tcond
  <+> "then" <+> prettyTerm ctx tt
  <+> "else" <+> prettyTerm ctx tf
prettyTerm ctx (TUnpack _ tyX x t1 t2) =
  let (ctx', tyX') = freshName ctx tyX
      (ctx'', x') = freshName ctx' x
  in align
  $ "let {" <> pretty tyX' <> "," <> pretty x'
  <> "} =" <+> prettyTerm ctx t1 <+> "in"
  <+> prettyTerm ctx'' t2
prettyTerm ctx (TAbs _ x t) =
  let (ctx', x') = freshName ctx x
  in align
  $ "Λ" <+> pretty x' <> "."
  <> softline <> prettyTerm ctx' t
prettyTerm ctx (App _ tf tx)
  = align
  $ prettyTerm ctx tf <+> prettyTerm ctx tx
prettyTerm ctx (TPred _ t) = "pred" <+> prettyTerm ctx t
prettyTerm ctx (TIsZero _ t) = "isZero" <+> prettyTerm ctx t
prettyTerm ctx (TApp _ t tyS)
  = align
  $ prettyTerm ctx t
  <+> "[" <> prettyType ctx tyS <> "]"
prettyTerm ctx (TupleProj _ tu ti) =
  prettyTerm ctx tu <+> "!" <+> prettyTerm ctx ti
prettyTerm _ (Var _ vn _ _) = pretty vn
prettyTerm ctx (Tuple _ ts) = prettyTuple $ fmap (prettyTerm ctx) ts
prettyTerm _ TTrue{} = "#t"
prettyTerm _ TFalse{} = "#f"
prettyTerm _ TZero{} = "0"
-- TODO: catch Succ at App to pretty print well
prettyTerm ctx (TSucc _ ts) = go (1 :: Int) ts
  where
    go n TZero{} = pretty n
    go n (TSucc _ t) = go (n+1) t
    go _ t = "(succ" <+> prettyTerm ctx t <> ")"
prettyTerm ctx (TPack _ ty t ty')
  = align
  $ "{*" <> prettyType ctx ty <> "," <> softline
  <> prettyTerm ctx t <> "}"
  <+> "as" <+> prettyType ctx ty'


showTermType :: Context -> Term -> Type -> String
showTermType ctx t ty
  = show
  $ prettyTerm ctx t <+> ":" <+> prettyType ctx ty


prettyBinding :: Context -> Binding -> Doc a
prettyBinding ctx = go
  where
    go NameBind = mempty
    go TyVarBind = mempty
    go (VarBind ty) = ":" <+> prettyType ctx ty
    go (TypeBind _) = ":: *"
    go (TermBind _ Nothing) = mempty
    go (TermBind _ (Just ty)) = ":" <+> prettyType ctx ty

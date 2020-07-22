{-# LANGUAGE StrictData #-}
module F.Syntax (
  Command(..), Info(..), Type(..), Term(..), Binding(..), Context(..),
  TopLevel(..),
  addName,
  addBindings,
  dropBindingsUntil,
  err,
  isNilType,
  makeContext,
  consTerm,
  consType,
  fixTerm,
  fixType,
  freshName,
  headTerm,
  headType,
  ii,
  isNilTerm,
  natToInt,
  nilType,
  pix,
  tailTerm,
  tailType,
  termSubstTop,
  tytermSubstTop,
  typeSubstTop,
  termShift,
  typeShift,
  getTypeFromContext,
  nameToIndex,
  orderedInCtx,
  addBinding,
  getBinding,
  prettyBinding,
  showError,
  showTerm,
  showTermType,
  showType,
  unexpected,
  ) where


import Data.List (findIndex)
import Data.Semigroup (Sum(..))
import Data.Text.Prettyprint.Doc ((<>), (<+>), Doc, Pretty(..),
                                  align, encloseSep, flatAlt, group,
                                  nest, softline, vsep)
--import Debug.Trace (trace)
import Prelude hiding ((!!))


---
-- types
data Info = None | Offset Int
  deriving (Show)

instance Eq Info where
  _ == _ = True -- we don't care

instance Semigroup Info where
  None <> x = x
  x <> None = x
  _ <> y = y


data Type
  -- primitive
  = TyBool
  | TyNat
  -- constructors
  | TyId String
  | TyVar Int Int String  -- type variable
  | TyArr Type Type       -- type of functions
  | TyAll String Type     -- universal type
  | ExTyVar String
  | TySome String Type    -- existential type
  -- add-ons
  | TyTuple [Type]
  | TyList Type
  deriving (Eq, Show)


data Term
-- pure LC
  = Var {i :: Info, name :: String, ix :: Int, len :: Int} -- variable
  | Abs {i :: Info, var :: String, ty :: Type, t :: Term}  -- abstraction
  | App {i :: Info, l :: Term, r :: Term}                  -- application
-- type stuff
  | TAbs {i :: Info, var :: String, t :: Term}             -- type abstraction
  | TApp {i :: Info, t :: Term, ty :: Type}                -- type application
  | TPack {i :: Info, ty :: Type, t :: Term, ex :: Type}  -- packing
  | TUnpack {i :: Info, tyname :: String, tname :: String, l :: Term, t :: Term}  -- unpacking
-- add-ons
  | Fix_ {i :: Info, t :: Term}
  | Ascribe {i :: Info, t :: Term, ty :: Type}
  | Tuple {i :: Info, ts :: [Term]}
  | TupleProj {i :: Info, t :: Term, ixt :: Term}
  | Cons_ {i :: Info, th :: Term, tt :: Term}
  | Nil_ {i :: Info}
  | IsNil_ {i :: Info, t :: Term}
  | Head_ {i :: Info, t :: Term}
  | Tail_ {i :: Info, t :: Term}
  | TTrue {i :: Info}
  | TFalse {i :: Info}
  | TIf {i :: Info, tcond :: Term, tt :: Term, tf :: Term}
  | TZero {i :: Info}
  | TSucc {i :: Info, t :: Term}
  | TPred {i :: Info, t :: Term}
  | TIsZero {i :: Info, t :: Term}
  deriving (Eq, Show)


-- INVARIANT: all Terms must have info field
ii :: Info -> Term -> Term
-- | inherit info from parent term
ii parentInfo tchild = tchild{i = parentInfo <> i tchild}


data Binding
  -- TODO: document these
  = NameBind
  | VarBind Type
  | TyVarBind
  | ExTyVarBind
  | ExTyMarker
  | ExTySolution Type
  | TermBind Term (Maybe Type)
  | TypeBind Type
  deriving (Show)

existentialVarBinding :: Binding -> Bool
existentialVarBinding ExTyMarker = True
existentialVarBinding ExTyVarBind = True
existentialVarBinding _ = False

data Context = Ctx [(String, Binding)] (Sum Int)

instance Show Context where
  show (Ctx bs _) = show bs

instance Semigroup Context where
  Ctx ctx n <> Ctx ctx' n' = Ctx (ctx <> ctx') (n <> n')

instance Monoid Context where
  mempty = Ctx [] (Sum 0)

orderedInCtx :: Context -> String -> String -> Bool
orderedInCtx (Ctx bs' _) a b = go False bs' where
  go seenA ((x,_):bs)
    | x == a = go True bs
    | x == b = seenA
    | otherwise = go seenA bs
  go _ [] = True


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
    go c (TyList ty) = TyList $ go c ty
    go _ (ExTyVar vn) = ExTyVar vn


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
    go c (Ascribe fi t ty) = Ascribe fi (go c t) (onType c ty)
    go c (Fix_ fi t) = Fix_ fi $ go c t
    go c (Cons_ fi th tt) = Cons_ fi (go c th) (go c tt)
    go c (IsNil_ fi t) = IsNil_ fi $ go c t
    go c (Head_ fi t) = Head_ fi $ go c t
    go c (Tail_ fi t) = Tail_ fi $ go c t
    go c (Tuple fi ts) = Tuple fi $ fmap (go c) ts
    go c (TupleProj fi tu ti) = TupleProj fi (go c tu) (go c ti)
    go _ n@Nil_{} = n
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

addBindings :: Context -> [(String, Binding)] -> Context
addBindings = foldr (\(n, b) ctx' -> addBinding ctx' n b)

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
bindingShift _ b@ExTyVarBind = b
bindingShift _ b@ExTyMarker = b
bindingShift d (ExTySolution tyT) = ExTySolution $ typeShift d tyT


getBinding :: Info -> Context -> Int -> Binding
getBinding fi ctx@(Ctx _ (Sum n)) i = case ctx .! i of
  Just (_, bind) -> bindingShift (i+1) bind
  Nothing -> variableLookupFailure fi i n

dropBindingsUntil :: String -> Context -> Context
dropBindingsUntil vn = go
  where
    go ctx@(Ctx [] _) = ctx
    go ctx@(Ctx ((vn', _):bs) (Sum n))
      | vn == vn' = --ctx
        Ctx bs (Sum $ n-1)
    go (Ctx (_:bs) (Sum n)) = go (Ctx bs (Sum $ n-1))


getTypeFromContext :: Info -> Context -> Int -> Type
getTypeFromContext fi ctx i = case getBinding fi ctx i of
  NameBind -> bindError
  (VarBind tyT) -> tyT
  TyVarBind -> bindError
  TermBind _ (Just tyT) -> tyT
  TermBind _ Nothing -> err fi $
    "No type for variable " ++ varname
  TypeBind _ -> bindError
  ExTySolution tyT -> tyT
  ExTyVarBind -> bindError
  ExTyMarker -> bindError
  where
    varname = indexToName fi ctx i
    bindError =
      err fi $ "getTypeFromContext: Wrong kind of binding for variable "
               ++ varname


indexToName :: Info -> Context -> Int -> String
indexToName fi ctx@(Ctx _ (Sum n)) i = case ctx .! i of
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
showError None msg = msg
showError (Offset n) msg = concat [show n, ":", msg]


infixl 9  .! -- safe indexing
(.!) :: Context -> Int -> Maybe (String, Binding)
(Ctx bs _) .! ix = go bs ix where
  go ((_, b'):xs) n
    | existentialVarBinding b' = go xs n
  go (x:_) 0 = Just x
  go (_:xs) n = go xs (n-1)
  go [] _ = Nothing


freshName :: Context -> String -> (Context, String)
freshName c@(Ctx ctx (Sum n)) x =
  if isBound
  then freshName c $ x ++ "'"
  else (Ctx ((x, NameBind):ctx) (Sum $ n+1), x)
  where
    isBound = x `elem` fmap fst ctx


isNilTerm :: Term
isNilTerm
  = TAbs d tyX
    (Abs d "xs" (TyList (TyVar 0 1 tyX))
    (IsNil_ d (Var d "xs" 1 2)))
  where
    d = None
    tyX = "X"


headTerm :: Term
headTerm
  = TAbs d tyX
    (Abs d "xs" (TyList (TyVar 0 1 tyX))
    (Head_ d (Var d "xs" 1 2)))
  where
    d = None
    tyX = "X"


tailTerm :: Term
tailTerm
  = TAbs d tyX
    (Abs d "xs" (TyList (TyVar 0 1 tyX))
    (Tail_ d (Var d "xs" 1 2)))
  where
    d = None
    tyX = "X"

consTerm :: Term
consTerm
  = TAbs d tyX
    (Abs d "x" (TyVar 0 1 tyX)
      (Abs d "xs" (TyList (TyVar 1 2 tyX))
        (Cons_ d (Var d "x" 2 3) (Var d "xs" 0 3))))
  where
    d = None
    tyX = "X"


fixTerm :: Term
fixTerm
  = TAbs d tyX
    (TAbs d tyY
     (Abs d "f" (fixType mempty (Just $ TyVar 1 2 tyX) (Just $ TyVar 0 2 tyY))
      (Abs d "x" (TyVar 2 3 tyX)
        (App d (Fix_ d $ Var d "f" 1 4) (Var d "x" 0 4)))))
  where
    d = None
    tyX = "X"
    tyY = "Y"


universalType :: (Type -> Type) -> Context -> Maybe Type -> Type
universalType f ctx mty =
  case mty of
    Just ty -> f ty
    Nothing -> TyAll tyX $ f x
      where
        tyX = snd $ freshName ctx "X"
        x = TyVar 0 1 tyX


nilType :: Context -> Maybe Type -> Type
nilType = universalType TyList

consType :: Context -> Maybe Type -> Type
consType = universalType (\ty -> TyArr ty (TyArr (TyList ty) (TyList ty)))

isNilType :: Context -> Maybe Type -> Type
isNilType = universalType (\ty -> TyArr (TyList ty) TyBool)

headType :: Context -> Maybe Type -> Type
headType = universalType (\ty -> TyArr (TyList ty) ty)

tailType :: Context -> Maybe Type -> Type
tailType = universalType (\ty -> TyArr (TyList ty) (TyList ty))

fixType :: Context -> Maybe Type -> Maybe Type -> Type
fixType ctx mTyX mTyY =
  case (mTyX, mTyY) of
    (Just tyX, Just tyY) -> fixType' tyX tyY
    (Just tyX, Nothing) -> universalType (fixType' tyX) ctx Nothing
    (Nothing, Nothing) -> TyAll x . TyAll y $ fixType' tyX tyY
      where
        x = snd $ freshName ctx "X"
        tyX = TyVar 1 2 x
        y = snd $ freshName ctx "Y"
        tyY = TyVar 0 2 y
    _ -> error "Internal error: fix operator type"
  where
    fixType' tyX tyY = TyArr (TyArr (TyArr tyX tyY)
                                (TyArr tyX tyY))
                         (TyArr tyX tyY)



prettyType :: Context -> Type -> Doc a
prettyType ctx (TyAll tyX ty) =
  let (ctx', tyX') = freshName ctx tyX
      in align
      $ "∀" <+> pretty tyX' <> "." <> softline
      <> prettyType ctx' ty
prettyType ctx' tyT = arrowType ctx' tyT
  where
    arrowType ctx (TyArr tyL tyR) = align
      $ atomicType ctx tyL <+> "->"
      <> softline <> arrowType ctx tyR
    arrowType ctx ty = atomicType ctx ty
    atomicType _ (TyVar _ _ x) = pretty x
    atomicType _ (ExTyVar x) = pretty x
    atomicType _ (TyId b) = pretty b
    atomicType ctx (TyTuple tys) = prettyTuple $ fmap (prettyType ctx) tys
    atomicType ctx (TyList ty) = "List" <+> prettyType ctx ty
    atomicType _ TyBool = "Bool"
    atomicType _ TyNat = "Nat"
    atomicType ctx (TySome tyX ty) =
      let (ctx'', tyX') = freshName ctx tyX
      in align
      $ "∃" <+> pretty tyX' <> "," <> softline
      <> prettyType ctx'' ty <> ""
    atomicType ctx ty = "(" <> prettyType ctx ty <> ")"


prettyTuple :: [Doc a] -> Doc a
prettyTuple = group
  . encloseSep (flatAlt "< " "<")
               (flatAlt " >" ">")
               ", "


prettyTerm :: Context -> Term -> Doc a
prettyTerm ctx (Abs _ x ty t) =
  let (ctx', x') = freshName ctx x
  in align
  $ "λ" <+> pretty x' <> ":" <> prettyType ctx ty <> "."
  <> softline <> prettyTerm ctx' t
prettyTerm ctx (Fix_ _ t) = "fix" <+> prettyTerm ctx t
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
prettyTerm appCtx appT = appTerm appCtx appT
  where
    appTerm ctx (App _ tf tx)
      = align
      $ appTerm ctx tf <+> atomicTerm ctx tx
    appTerm ctx (TPred _ t) = "pred" <+> atomicTerm ctx t
    appTerm ctx (TIsZero _ t) = "isZero" <+> atomicTerm ctx t
    appTerm ctx (TApp _ t tyS)
      = align
      $ appTerm ctx t
      <+> "[" <> prettyType ctx tyS <> "]"
    appTerm ctx t = pathTerm ctx t
    pathTerm ctx (TupleProj _ tu ti) =
      atomicTerm ctx tu <+> "!" <+> atomicTerm ctx ti
    pathTerm ctx t = atomicTerm ctx t
    atomicTerm _ (Var _ vn _ _) = pretty vn
    atomicTerm ctx (Tuple _ ts) = prettyTuple $ fmap (prettyTerm ctx) ts
    atomicTerm ctx (Cons_ _ th tt)
      = "(cons" <+> atomicTerm ctx th
      <+> atomicTerm ctx tt <> ")"
    atomicTerm _ Nil_{} = "nil"
    atomicTerm ctx (IsNil_ _ t) = "isNil" <+> atomicTerm ctx t
    atomicTerm ctx (Head_ _ t) = "head" <+> atomicTerm ctx t
    atomicTerm ctx (Tail_ _ t) = "tail" <+> atomicTerm ctx t
    atomicTerm _ TTrue{} = "#t"
    atomicTerm _ TFalse{} = "#f"
    atomicTerm _ TZero{} = "0"
    atomicTerm ctx (TSucc _ ts) = go (1 :: Int) ts
      where
        go n TZero{} = pretty n
        go n (TSucc _ t) = go (n+1) t
        go _ t = "(succ" <+> atomicTerm ctx t <> ")"
    atomicTerm ctx (TPack _ ty t ty')
      = align
      $ "{*" <> prettyType ctx ty <> "," <> softline
      <> prettyTerm ctx t <> "}"
      <+> "as" <+> prettyType ctx ty'
    atomicTerm ctx Ascribe{t} = prettyTerm ctx t
    atomicTerm ctx t = "(" <> prettyTerm ctx t <> ")"


showTermType :: Context -> Term -> Type -> String
showTermType ctx t ty
  = show
  $ prettyTerm ctx t <+> ":" <+> prettyType ctx ty


showTerm :: Context -> Term -> String
showTerm ctx t = show $ prettyTerm ctx t

showType :: Context -> Type -> String
showType ctx ty = show $ prettyType ctx ty


prettyBinding :: Context -> Binding -> Doc a
prettyBinding ctx = go
  where
    go NameBind = mempty
    go TyVarBind = mempty
    go (VarBind ty) = ":" <+> prettyType ctx ty
    go (TypeBind _) = ":: *"
    go (TermBind _ Nothing) = mempty
    go (TermBind _ (Just ty)) = ":" <+> prettyType ctx ty
    go ExTyVarBind = mempty
    go ExTyMarker = mempty
    go (ExTySolution ty) = prettyType ctx ty


unexpected :: Context -> Info -> String -> Type -> Term -> Type -> a
unexpected ctx fi fname expected term found
      = err fi . show . nest 2
        $ vsep [ pretty fname
                 <> ": expected type"
                 <+> prettyType ctx expected
               , "for term" <+> prettyTerm ctx term
               , "found type" <+> prettyType ctx found <+> "instead"
               ]


natToInt :: Term -> Int
natToInt TSucc{t} = 1 + natToInt t
natToInt TZero{} = 0
natToInt t = err (i t) "Not a natural"

pix :: Int
-- placeholder index
pix = -1

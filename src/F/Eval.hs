{-# LANGUAGE FlexibleInstances #-}
module F.Eval
  (
    InContext(..),
    eval,
    eval1,
    evalBinding,
    simplifyType,
    typeOf,
    ) where


import F.Syntax (Type(..), Term(..), Binding(..), Context(..),
                 addBinding, addName, dummyInfo, getBinding, getTypeFromContext,
                 termShift, termSubstTop, tytermSubstTop,
                 typeShift, typeSubstTop,
                 err)
import F.Decor (decor , decorT)


import Control.Applicative ((<|>))
import Data.Maybe (isJust, fromJust)
--import Debug.Trace (trace)


isVal :: Context -> Term -> Bool
isVal _ Abs{}    = True
isVal _ TAbs{}   = True
isVal ctx (TPack _ _ v _) = isVal ctx v
isVal _ TTrue{}  = True
isVal _ TFalse{} = True
isVal _ TZero{}  = True
isVal ctx (TSucc _ t) = isVal ctx t
isVal ctx (TPred _ t) = isVal ctx t
isVal _ Var{} = False
isVal _ App{} = False
isVal _ TApp{} = False
isVal _ TUnpack{} = False
isVal _ Fix{} = False
isVal _ TIf{} = False
isVal _ TIsZero{} = False


eval1 :: Context -> Term -> Maybe Term
eval1 ctx = go
  where
    go (Var fi _ i _) = case getBinding fi ctx i of
      TermBind t _ -> Just t
      _ -> Nothing
    go Abs{} = Nothing
    go (App _fi (Abs __fi _x _tyT11 t12) v2)
      | isVal ctx v2 = Just $ termSubstTop v2 t12
    go (App fi v1 t2)
      | isVal ctx v1 = eval1 ctx t2 >>= Just . App fi v1
    go (App fi t1 t2) = eval1 ctx t1 >>= \t1' -> Just $ App fi t1' t2
    go TAbs{} = Nothing
    go (TApp _fi (TAbs __fi _x t11) tyT2) =
      Just $ tytermSubstTop tyT2 t11
    go (TApp fi t1 tyT2) = eval1 ctx t1 >>= \t1' -> Just $ TApp fi t1' tyT2
    go (TUnpack _fi _ _ (TPack _ tyT11 v12 _) t2)
      | isVal ctx v12 = Just
        $ tytermSubstTop tyT11 $ termSubstTop (termShift 1 v12) t2
    go (TUnpack fi tyX x t1 t2) =
      eval1 ctx t1 >>= \t1' -> Just $ TUnpack fi tyX x t1' t2
    go (TPack fi tyT1 t2 tyT3) = eval1 ctx t2
      >>= \t2' -> Just $ TPack fi tyT1 t2' tyT3
    go t@(Fix _ (Abs _ _ _ body)) =
      Just $ termSubstTop t body
    go (Fix fi t) = eval1 ctx t >>= Just . Fix fi
    go TTrue{} = Nothing
    go TFalse{} = Nothing
    go (TIf _ TTrue{} tt _) = Just tt
    go (TIf _ TFalse{} _ tf) = Just tf
    go (TIf fi tcond tt tf) =
      eval1 ctx tcond >>= \tcond' -> Just $ TIf fi tcond' tt tf
    go TZero{} = Nothing
    go (TSucc fi t) = eval1 ctx t >>= Just . TSucc fi
    go (TPred _ z@TZero{}) = Just z
    go (TPred _ (TSucc _ t)) = Just t
    go (TPred fi t) = eval1 ctx t >>= Just . TPred fi
    go (TIsZero fi TZero{}) = Just $ TTrue fi
    go (TIsZero fi TSucc{}) = Just $ TFalse fi
    go (TIsZero fi t) = eval1 ctx t >>= Just . TIsZero fi


eval :: Context -> Term -> Term
eval ctx = rewrite (eval1 ctx)


---
-- typing
typeOf :: Context -> Term -> Type
typeOf ctx = go
  where
    go (Var fi _ i _) = getTypeFromContext fi ctx i
    go (Abs _fi x tyT1 t2) =
      let ctx' = addBinding ctx x (VarBind tyT1)
          tyT2 = typeOf ctx' t2
      in TyArr tyT1 $ typeShift (-1) tyT2
    go (App fi t1 t2) =
      let tyT1 = typeOf ctx t1
          tyT2 = typeOf ctx t2
      in case simplifyType ctx tyT1 of
        TyArr tyT11 tyT12 ->
          if typeEqv ctx tyT2 tyT11
          then tyT12
          else err fi "app: parameter type mismatch"
        _ -> err fi "app: arrow type expected"
    go (TAbs _fi tyX t2) =
      let ctx' = addBinding ctx tyX TyVarBind
          tyT2 = typeOf ctx' t2
      in TyAll tyX tyT2
    go (TApp fi t1 tyT2) =
      let tyT1 = typeOf ctx t1
      in case simplifyType ctx tyT1 of
        TyAll _ tyT12 -> typeSubstTop tyT2 tyT12
        _ -> err fi "app: universal type expected"
    go (TPack fi tyT1 t2 tyT@(TySome _tyY tyT2)) =
      let tyU  = typeOf ctx t2
          tyU' = typeSubstTop tyT1 tyT2
      in if typeEqv ctx tyU tyU'
         then tyT
         else err fi "pack: doesn't match declared type"
    go (TPack fi _ _ _) = err fi "pack: existential type expected"
    go (TUnpack fi tyX x t1 t2) =
      let tyT1 = typeOf ctx t1
      in case tyT1 of
        TySome _tyY tyT11 ->
          let ctx'  = addBinding ctx tyX TyVarBind
              ctx'' = addBinding ctx' x (VarBind tyT11)
              tyT2  = typeOf ctx'' t2
          in typeShift (-2) tyT2
        _ -> err fi "unpack: existential type expected"
    go (Fix fi t) =
      case simplifyType ctx $ typeOf ctx t of
        (TyArr ty ty') ->
          if typeEqv ctx ty ty'
          then ty'
          else err fi "fix: domain-incompatible body result"
        _ -> err fi "fix: arrow type expected"
    go (TTrue _)  = TyBool
    go (TFalse _) = TyBool
    go (TIf fi tcond tt tf) =
      if typeIs TyBool tcond
      then let tytt = typeOf ctx tt
           in if typeIs tytt tf
              then tytt
              else err fi "if: arms of conditional have different types"
      else err fi "if: conditional guard is not a boolean"
    go TZero{} = TyNat
    go (TSucc fi t) =
      if typeIs TyNat t
      then TyNat
      else err fi "succ: argument must be of type Nat"
    go (TPred fi t) =
      if typeIs TyNat t
      then TyNat
      else err fi "pred: argument must be of type Nat"
    go (TIsZero fi t) =
      if typeIs TyNat t
      then TyBool
      else err fi "iszero: argument must be of type Nat"
    typeIs ty t = typeEqv ctx ty $ typeOf ctx t

typeEqv :: Context -> Type -> Type -> Bool
typeEqv ctx ty1 ty2 = go ty1' ty2'
  where
    go (TyId b1) (TyId b2) = b1 == b2
    go (TyVar i _ _) _
      | isTypeAbscription ctx i = typeEqv ctx (getTypeAbscription ctx i) ty2'
    go _ (TyVar j _ _)
      | isTypeAbscription ctx j = typeEqv ctx ty2' ty1'
    go (TyVar i _ _) (TyVar j _ _) = i == j
    go (TyArr ty11 ty12) (TyArr ty21 ty22)
      = typeEqv ctx ty11 ty21 && typeEqv ctx ty12 ty22
    go (TySome tyX ty11) (TySome _ ty21) = highOrdEqv tyX ty11 ty21
    go (TyAll tyX ty11) (TyAll _ ty21) = highOrdEqv tyX ty11 ty21
    go TyBool TyBool = True
    go TyBool _ = False
    go _ TyBool = False
    go TyNat TyNat = True
    go TyNat _ = False
    go _ TyNat = False
    go TyId{} _ = False
    go _ TyId{} = False
    go TyArr{} _ = False
    go _ TyArr{} = False
    go TySome{} _ = False
    go _ TySome{} = False
    go _ TyAll{} = False
    go TyAll{} _ = False
    highOrdEqv tyX = typeEqv (addName ctx tyX)
    ty1' = simplifyType ctx ty1
    ty2' = simplifyType ctx ty2


simplifyType :: Context -> Type -> Type
simplifyType ctx = rewrite computeType
  where
    computeType (TyVar i _ _) = maybeAbscription ctx i
    computeType _ = Nothing


maybeAbscription :: Context -> Int -> Maybe Type
maybeAbscription ctx i =
  case getBinding dummyInfo ctx i of
    TypeBind tyT -> Just tyT
    _ -> Nothing


isTypeAbscription :: Context -> Int -> Bool
isTypeAbscription ctx i = isJust $ maybeAbscription ctx i
getTypeAbscription :: Context -> Int -> Type
getTypeAbscription ctx i = fromJust $ maybeAbscription ctx i

rewrite :: (a -> Maybe a) -> a -> a
rewrite f x = case f x of
  Just x' -> rewrite f x'
  Nothing -> x


evalBinding :: Context -> Binding -> Either String Binding
evalBinding ctx = go
  where
    go b@NameBind = Right b
    go (VarBind tyT) = Right . VarBind $ decorT tyT ctx
    go b@TyVarBind = Right b
    go (TermBind t mTyT) =
      let t' = decor t ctx
          tyT' = typeOf ctx t'
          t'' = eval ctx t'
      in if maybe True (typeEqv ctx tyT') mTyT
         then Right $ TermBind t'' (mTyT <|> Just tyT')
         else Left "Type of binding does not match declared type"
    go (TypeBind tyT) = Right . TypeBind $ decorT tyT ctx


--- printing
data InContext a = InCtx {thing :: a, context :: Context}

instance Show (InContext Binding) where
  show (b `InCtx` ctx) = showBinding ctx b

instance Show (InContext Type) where
  show (ty `InCtx` ctx) = showType ctx ty

instance Functor InContext where
  fmap f (a `InCtx` ctx) = f a `InCtx` ctx

instance Semigroup a => Semigroup (InContext a) where
  (a `InCtx` ctx) <> (a' `InCtx` ctx') = (a <> a') `InCtx` (ctx <> ctx')

instance Monoid a => Monoid (InContext a) where
  mempty = mempty `InCtx` mempty


showBinding :: Context -> Binding -> String
showBinding ctx = go
  where
    go NameBind = ""
    go TyVarBind = ""
    go (VarBind tyT) = unwords [":", showType ctx tyT]
    go (TermBind t mTyT)
      = case mTyT of
          Nothing -> show $ typeOf ctx t `InCtx` ctx
          Just tyT -> show $ tyT `InCtx` ctx
    go (TypeBind tyT) = unwords ["=", showType ctx tyT]


showType :: Context -> Type -> String
showType _ = show -- FIXME: pretty-print!


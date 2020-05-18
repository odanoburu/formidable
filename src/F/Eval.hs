{-# LANGUAGE FlexibleInstances #-}
module F.Eval
  (
    InContext(..),
    eval,
    eval1,
    evalBinding,
    typeOf,
    ) where

import F.Syntax (Type(..), Term(..), Binding(..), Context(..),
                 addBinding, addName, getBinding, getTypeFromContext,
                 termShift, termSubstTop, tytermSubstTop,
                 typeShift, typeSubstTop,
                 showError)
import F.Decor (decor)


isVal :: Context -> Term -> Bool
isVal _ Abs{}    = True
isVal _ TAbs{}   = True
isVal _ TTrue{}  = True
isVal _ TFalse{} = True
isVal _ _ = False

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
    go TTrue{} = Nothing
    go TFalse{} = Nothing
    go (TIf _ TTrue{} tt _) = Just tt
    go (TIf _ TFalse{} _ tf) = Just tf
    go (TIf fi tcond tt tf) =
      eval1 ctx tcond >>= \tcond' -> Just $ TIf fi tcond' tt tf


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
      in case tyT1 of
        TyArr tyT11 tyT12 ->
          if tyT2 == tyT11
          then tyT12
          else showError fi "parameter type mismatch"
        _ -> showError fi "arrow type expected"
    go (TAbs _fi tyX t2) =
      let ctx' = addBinding ctx tyX TyVarBind
          tyT2 = typeOf ctx' t2
      in TyAll tyX tyT2
    go (TApp fi t1 tyT2) =
      let tyT1 = typeOf ctx t1
      in case tyT1 of
        TyAll _ tyT12 -> typeSubstTop tyT2 tyT12
        _ -> showError fi "universal type expected"
    go (TPack fi tyT1 t2 tyT@(TySome _tyY tyT2)) =
      let tyU  = typeOf ctx t2
          tyU' = typeSubstTop tyT1 tyT2
      in if tyU == tyU'
         then tyT
         else showError fi "doesn't match declared type"
    go (TPack fi _ _ _) = showError fi "existential type expected"
    go (TUnpack fi tyX x t1 t2) =
      let tyT1 = typeOf ctx t1
      in case tyT1 of
        TySome _tyY tyT11 ->
          let ctx'  = addBinding ctx tyX TyVarBind
              ctx'' = addBinding ctx' x (VarBind tyT11)
              tyT2  = typeOf ctx'' t2
          in typeShift (-2) tyT2
        _ -> showError fi "existential type expected"
    go (TTrue _)  = TyBool
    go (TFalse _) = TyBool
    go (TIf fi tcond tt tf) =
      if typeOf ctx tcond == TyBool
      then let tytt = typeOf ctx tt
           in if typeEqv ctx tytt $ typeOf ctx tf
              then tytt
              else showError fi
                             "arms of conditional have different types*IMPROVEMSG*"
      else showError fi "conditional guard is not a boolean"


typeEqv :: Context -> Type -> Type -> Bool
typeEqv ctx ty1 ty2 = go ty1' ty2'
  where
    go TyBool TyBool = True
    go (TyId b1) (TyId b2) = b1 == b2
    -- TODO: when type abscription we need to change this
    go (TyVar i _ _) (TyVar j _ _) = i == j
    go (TyArr ty11 ty12) (TyArr ty21 ty22)
      = typeEqv ctx ty11 ty21 && typeEqv ctx ty12 ty22
    go (TySome tyX ty11) (TySome _ ty21) = highOrdEqv tyX ty11 ty21
    go (TyAll tyX ty11) (TyAll _ ty21) = highOrdEqv tyX ty11 ty21
    go TyBool _ = False
    go _ TyBool = False
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
simplifyType ctx = rewrite (computeType ctx)
  where
    -- TODO: implement when tyAbbBind is implemented
    computeType _ TyVar{} = Nothing
    computeType _ _ = Nothing


rewrite :: (a -> Maybe a) -> a -> a
rewrite f x = case f x of
  Just x' -> rewrite f x'
  Nothing -> x


evalBinding :: Context -> Binding -> Either String (InContext Binding)
evalBinding ctx = go
  where
    go b@NameBind = Right $ b `InCtx` ctx
    go b@VarBind{} = Right $ b `InCtx` ctx
    go b@TyVarBind = Right $ b `InCtx` ctx
    go (TermBind t mTyT) =
      let (t', ctx') = decor t ctx
          tyT' = typeOf ctx' t'
          t'' = eval ctx' t'
      in if maybe True (typeEqv ctx tyT') mTyT
      -- DOUBT: does returning tyT' which is equivalent but not
      -- necessarily the same as mTyT = Just tyT generate confusing
      -- error messages?
         then Right $ TermBind t'' (Just tyT') `InCtx` ctx'
         else Left "Type of binding does not match declared type"


--- printing
data InContext a = InCtx a Context

instance Show (InContext Binding) where
  show (b `InCtx` ctx) = showBinding ctx b

instance Show (InContext Type) where
  show (ty `InCtx` ctx) = showType ctx ty


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

showType :: Context -> Type -> String
showType _ = show -- FIXME: 

module F.Eval
  (
    typeOf,
    eval,
    ) where

import F.Syntax (Type(..), Term(..), Binding(..), Context(..),
                 addBinding, getTypeFromContext,
                 termShift, termSubstTop, tytermSubstTop,
                 typeShift, typeSubstTop,
                 showError)


isVal :: Context -> Term -> Bool
isVal _ Abs{} = True
isVal _ TAbs{} = True
isVal _ _ = False

eval1 :: Context -> Term -> Maybe Term
eval1 ctx = go
  where
    go (App _fi (Abs __fi _x _tyT11 t12) v2)
      | isVal ctx v2 = Just $ termSubstTop v2 t12
    go (App fi v1 t2)
      | isVal ctx v1 = eval1 ctx t2 >>= Just . App fi v1
    go (App fi t1 t2) = eval1 ctx t1 >>= \t1' -> Just $ App fi t1' t2
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
    go _ = Nothing


eval :: Context -> Term -> Term
eval ctx t = case eval1 ctx t of
  Just t' -> eval ctx t'
  Nothing -> t


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


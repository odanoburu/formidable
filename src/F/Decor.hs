module F.Decor (decor') where


import F.Syntax ( Context(..), Info(..), Term(..), Type(..)
                , addName, nameToIndex )


import Data.Semigroup (Sum(..))


infixl 4 .<
(.<) :: (a -> b, c) -> (c -> (a, c)) -> (b, c)
(t_, ctx) .< t' = let (a, ctx') = t' ctx in (t_ a, ctx')


-- use ‘decor’ from ‘F.Eval’ which returns InContext Term, making
-- explicit that they are tied together
decor' :: Term -> Context -> (Term, Context)
decor' (Var fi vn _ _) ctx@(Ctx _ (Sum n)) =
  let mvi = nameToIndex fi ctx vn
  in maybe (error "Unbound identifier*IMPROVEMSG*")
           (\vi -> (Var fi vn vi n, ctx))
           mvi
decor' (Abs fi vn ty t) ctx =
  (Abs fi vn ty, ctx `addName` vn) .< decor' t
decor' (App fi t1 t2) ctx =
  (App fi, ctx) .< decor' t1 .< decor' t2
decor' (TAbs fi tn t) ctx =
  (TAbs fi tn, ctx `addName` tn) .< decor' t
decor' (TApp fi t ty) ctx =
  (TApp fi, ctx) .< decor' t .< decorT' ty
decor' TPack{} _ = error "decor tpack"
decor' TUnpack{} _ = error "decor tunpack"
-- add-ons
decor' (TTrue fi) ctx = (TTrue fi, ctx)
decor' (TFalse fi) ctx = (TFalse fi, ctx)
decor' (TIf fi tcond tt tf) ctx =
  (TIf fi, ctx) .< decor' tcond .< decor' tt .< decor' tf


decorT' :: Type -> Context -> (Type, Context)
decorT' TyBool ctx = (TyBool, ctx)
decorT' (TyId _) _ = error "decorT tyid"
decorT' (TyVar _ _ tvn) ctx@(Ctx _ (Sum n)) =
  (, ctx) $ case nameToIndex (Offset $ -1) ctx tvn of
    Just tvi -> TyVar tvi n tvn
    Nothing -> TyId tvn
decorT' (TyArr t1 t2) ctx =
  (TyArr, ctx) .< decorT' t1 .< decorT' t2
decorT' (TyAll tvn ty) ctx =
  (TyAll tvn, ctx `addName` tvn) .< decorT' ty
decorT' (TySome tvn ty) ctx =
  (TySome tvn, ctx `addName` tvn) .< decorT' ty

module F.Decor where


import F.Syntax ( Command(..), Term(..), Type(..), Context(..), TopLevel(..)
                , addName, nameToIndex )


import Data.Semigroup (Sum(..))


contextualize :: [Command] -> TopLevel
contextualize = foldr go mempty
  where
    go cmd (TopLevel ctx cmds) =
      case cmd of
        Eval fi t -> let (ctx', t') = decor ctx t
                     in TopLevel ctx' $ Eval fi t' : cmds
        _ -> error "TBI - contextualize"


(.>) :: (a -> b) -> (c, a) -> (c, b)
-- | fill in term\/type with hole with term\/type in the pair and
-- return it
t_ .> (ctx, t') = (ctx, t_ t')


decor :: Context -> Term -> (Context, Term)
decor ctx@(Ctx _ (Sum n)) (Var fi vn _ _) =
  let mvi = nameToIndex fi ctx vn
  in maybe (error "Unbound identifier*IMPROVEMSG*")
           (\vi -> (ctx, Var fi vn vi n))
           mvi
decor ctx (Abs fi vn ty t) =
  let ctx' = ctx `addName` vn
  in Abs fi vn ty .> decor ctx' t
decor ctx (App fi t1 t2) =
  let (ctx', t1') = decor ctx t1
  in App fi t1' .> decor ctx' t2
decor ctx (TAbs fi tn t) =
  let ctx' = ctx `addName` tn
  in TAbs fi tn .> decor ctx' t
decor ctx (TApp fi t ty) =
  let (ctx', t') = decor ctx t
  in TApp fi t' .> decorT ctx' ty
decor _ TPack{} = error "decor tpack"
decor _ TUnpack{} = error "decor tunpack"


decorT :: Context -> Type -> (Context, Type)
decorT ctx TyBool = (ctx, TyBool)
decorT _ (TyId _) = error "decorT tyid"
decorT ctx@(Ctx _ (Sum n)) (TyVar _ _ tvn) =
  (ctx, ) $ case nameToIndex () ctx tvn of
    Just tvi -> TyVar tvi n tvn
    Nothing -> TyId tvn
decorT ctx (TyArr t1 t2) =
  let (ctx', t1') = decorT ctx t1
  in TyArr t1' .> decorT ctx' t2
decorT ctx (TyAll tvn ty) =
  let ctx' = ctx `addName` tvn
  in TyAll tvn .> decorT ctx' ty
decorT ctx (TySome tvn ty) =
  let ctx' = ctx `addName` tvn
  in TySome tvn .> decorT ctx' ty

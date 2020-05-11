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


(.>) :: (a -> a) -> (b, a) -> (b, a)
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
decor ctx (TAbs fi tn t) =
  let ctx' = ctx `addName` tn
  in TAbs fi tn .> decor ctx' t
-- TODO: fill in all terms, so that it becomes easier to add new ones
-- (we know where to add them)
decor ctx t = (ctx, t)

decorT :: Context -> Type -> (Context, Type)
decorT ctx@(Ctx _ (Sum n)) (TyVar _ _ tvn) =
  (ctx, ) $ case nameToIndex () ctx tvn of
    Just tvi -> TyVar tvi n tvn
    Nothing -> TyId tvn
decorT ctx (TyArr t1 t2) =
  let (ctx', t1') = decorT ctx t1
  in TyArr t1' .> decorT ctx' t2
decorT ctx (TyAll tn ty) =
  let ctx' = ctx `addName` tn
  in TyAll tn .> decorT ctx' ty
-- TODO: fill in all terms, so that it becomes easier to add new
-- ones (we know where to add them)
decorT ctx ty = (ctx, ty)

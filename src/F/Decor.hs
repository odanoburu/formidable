module F.Decor (decor, decorT) where


import F.Syntax ( Context(..), Info(..), Term(..), Type(..)
                , addName, nameToIndex, err )


import Data.Semigroup (Sum(..))


decor :: Term -> Context -> Term
decor (Var fi vn _ _) ctx@(Ctx _ (Sum n)) =
  let mvi = nameToIndex fi ctx vn
  in maybe (err fi $ unwords ["Unbound identifier", show vn])
           (\vi -> Var fi vn vi n)
           mvi
decor (Abs fi vn ty t) ctx =
  let ty' = decorT ty ctx
      t' = decor t $ ctx `addName` vn
  in Abs fi vn ty' t'
decor (App fi t1 t2) ctx =
  let t2' = decor t2 ctx
      t1' = decor t1 ctx
  in App fi t1' t2'
decor (TAbs fi tn t) ctx =
  let t' = decor t $ ctx `addName` tn
  in TAbs fi tn t'
decor (TApp fi t ty) ctx =
  let ty' = decorT ty ctx
      t' = decor t ctx
  in TApp fi t' ty'
decor (TPack fi ty1 t ty2) ctx =
  let ty1' = decorT ty1 ctx
      t' = decor t ctx
      ty2' = decorT ty2 ctx
  in TPack fi ty1' t' ty2'
decor (TUnpack fi tyX x t1 t2) ctx =
  let ctx' = ctx `addName` tyX
      ctx'' = ctx' `addName` x
      t1' = decor t1 ctx
      t2' = decor t2 ctx''
  in TUnpack fi tyX x t1' t2'
-- add-ons
decor (TTrue fi) _ = TTrue fi
decor (TFalse fi) _ = TFalse fi
decor (TIf fi tcond tt tf) ctx =
  let tcond' = decor tcond ctx
      tt' = decor tt ctx
      tf' = decor tf ctx
  in TIf fi tcond' tt' tf'


decorT :: Type -> Context -> Type
decorT TyBool _ = TyBool
decorT (TyId _) _ = error "decorT tyid"
decorT (TyVar _ _ tvn) ctx@(Ctx _ (Sum n)) =
  case nameToIndex (Offset $ -1) ctx tvn of
    Just tvi -> TyVar tvi n tvn
    Nothing -> TyId tvn
decorT (TyArr t1 t2) ctx =
  let t2' = decorT t2 ctx
      t1' = decorT t1 ctx
  in TyArr t1' t2'
decorT (TyAll tvn ty) ctx =
  let ty' = decorT ty $ ctx `addName` tvn
  in TyAll tvn ty'
decorT (TySome tvn ty) ctx =
  let ty' = decorT ty $ ctx `addName` tvn
  in TySome tvn ty'

module F.Typing where

import F.Syntax ( Binding(..), Context(..), Term(..), Type(..)
                , addBinding, addBindings, dropBindingsUntil, getTypeFromContext
                , natToInt, typeSubstTop, unexpected
                )


import Data.Semigroup (Sum(..))

isFreeInType :: String -> Type -> Bool
-- TODO:
isFreeInType exTyVarName ty = False

fill :: Context -> String -> [(String, Binding)] -> Context
-- fill hole in context specified by binding name (String)
fill (Ctx ctx (Sum n)) vn bs' = Ctx (go ctx) (Sum $ n + length bs' - 1)
  where
    go [] = []
    go ((bn, ExTyVarBind):bs)
      | bn == vn = bs' ++ bs
    go (b:bs) = b : go bs

apply :: Context -> Type -> Type
-- TODO: complete (or change tymap to have a onExVar parameter)
apply (Ctx ctx _) exV@(ExTyVar vn) = subst ctx
  where
    subst [] = exV
    subst ((vn', ExTyVarBind):_)
      | vn == vn' = exV
    subst ((vn', ExTySolution ty):_)
      | vn == vn' = ty
    subst (_:bs) = subst bs
apply _ v@TyVar{} = v
apply ctx (TyArr ty ty') = TyArr (apply ctx ty) (apply ctx ty')
apply ctx (TyAll vn ty) = TyAll vn $ apply ctx ty

instantiate :: Context -> Type -> Type -> Context
instantiate ctx (ExTyVar vn) ty =
  case ty of
    ExTyVar vn' -> -- InstLReach
      fill ctx vn' [(vn', ExTySolution $ ExTyVar vn)]
    TyArr lty rty -> -- InstLArr
      let ctx'' = instantiate ctx' lty lExVar
      in instantiate ctx'' rExVar (apply ctx'' rty)
      where
        lExVarN = vn ++ "_₁"
        lExVar = ExTyVar lExVarN
        rExVarN = vn ++ "_₂"
        rExVar = ExTyVar rExVarN
        ctx' = fill ctx vn [ (rExVarN, ExTyVarBind)
                           , (lExVarN, ExTyVarBind)
                           , (unwords [vn, "=", lExVarN, "->", rExVarN],
                              ExTySolution (TyArr lExVar rExVar))
                           ]
    TyAll vn' ty' -> -- InstLAIIR
      instantiate (addBinding ctx vn' TyVarBind) (ExTyVar vn) ty'
    _ -> -- InstLSolve
      fill ctx vn [(vn, ExTySolution ty)] -- TODO: check that ty is a monotype
instantiate ctx ty exV@ExTyVar{} =
  case ty of
    TyAll vn' ty' -> -- InstRAIIL
      instantiate (addBindings ctx [("⏵" ++ vn', ExTyMarker), (exvn, ExTyVarBind)]) (typeSubstTop (ExTyVar exvn) ty') exV
      where
        exvn = "^" ++ vn'
    _ -> -- DOUBT: is it ok to just swap argument order?
      instantiate ctx exV ty
instantiate _ _ _ = error "internal error: can't instantiate non-existential type variable"

isSubType :: Context -> Type -> Type -> Maybe Context
isSubType ctx (TyAll vn ty) ty' -- <:∀L
  = isSubType ctx' (typeSubstTop (ExTyVar exvn) ty) ty'
  where
    ctx' = addBindings ctx [(exvn, ExTyMarker), ("^" ++ vn, ExTyVarBind)]
    exvn = "⏵" ++ vn
isSubType ctx ty (TyAll vn ty') -- <:∀R
  = isSubType ctx' ty ty'
  where
    ctx' = addBinding ctx vn TyVarBind
isSubType ctx exV@(ExTyVar vn) ty -- <:InstantiateL
  = if isFreeInType vn ty
  then Nothing
  -- DOUBT: should it always be Just?
  else Just $ instantiate ctx exV ty
isSubType ctx ty exV@(ExTyVar vn) -- <:InstantiateR
  = if isFreeInType vn ty
    then Nothing
    else Just $ instantiate ctx ty exV
isSubType ctx (TyVar i l _) (TyVar i' l' _) -- <:Var
  = if i == i' && l == l' then Just ctx else Nothing
-- isSubType TyVar{} _ = False
-- isSubType _ TyVar{} = False
isSubType ctx (ExTyVar vn) (ExTyVar vn') -- <:Exvar
  | vn == vn' = Just ctx
isSubType ctx (TyArr t1 t2) (TyArr t1' t2') -- <:⟶
  = case isSubType ctx t1' t1 of
      Nothing -> Nothing
      Just ctx' -> isSubType ctx' (apply ctx' t2) (apply ctx' t2')
isSubType _ TyArr{} _ = Nothing
isSubType _ _ TyArr{} = Nothing
isSubType ctx TyBool TyBool = Just ctx
isSubType ctx TyNat TyNat = Just ctx
-- isSubType ctx (TyTuple tys) (TyTuple tys') = (ctx, all snd $ zipWith (isSubType ctx) tys tys')
isSubType ctx (TyList ty) (TyList ty') = isSubType ctx ty ty'


check :: Context -> Term -> Type -> Maybe (Type, Context)
check ctx t aTy@(TyAll vn ty) = -- ∀I
  do
    (_, ctx') <- check (addBinding ctx vn TyVarBind) t ty
    -- DOUBT: is this correct?
    return (aTy, dropBindingsUntil vn ctx')
check ctx t ty = -- Sub
  do
    (ty', ctx') <- infer ctx t
    ctx'' <- isSubType ctx' ty ty'
    return (ty, ctx'')


infer :: Context -> Term -> Maybe (Type, Context)
infer ctx = go
  where
    go Var{i, ix} = Just (getTypeFromContext i ctx ix, ctx)
    go Ascribe{t, ty} = -- Anno
      --- DOUBT: do I have to check well-formedness of ty?
      check ctx t ty
    -- go Tuple{ts} = (, ctx) . TyTuple <$> mapM (infer ctx) ts
    -- go (TupleProj fi t ixt) = do
    --   ty <- infer ctx t
    --   case ty of
    --     TyTuple tys -> Just $ tys !! natToInt ixt
    --     _ -> unexpected ctx fi "!" (TyTuple []) t ty --FIXME: fix expected type
    -- go TTrue{} = Just TyBool
    -- go TFalse{} = Just TyBool
    -- go TIf{tcond, tt, tf}
    --   = check ctx tcond TyBool
    --   >> (infer ctx tt >>= check ctx tf)
    --   <|> (infer ctx tf >>= check ctx tt)
    -- go TZero{} = Just TyNat
    -- go TSucc{t} = check ctx t TyNat
    -- go TPred{t} = check ctx t TyNat
    -- go TIsZero{t} = check ctx t TyNat >> Just TyBool

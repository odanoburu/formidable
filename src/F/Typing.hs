module F.Typing where

import F.Syntax ( Binding(..), Context(..), Info(..), Term(..), Type(..)
                , addBinding, addBindings, dropBindingsUntil, getTypeFromContext
                , orderedInCtx, typeSubstTop
                )


import Debug.Trace (trace)
import Control.Applicative ((<|>))
import Data.Function ((&))
import Data.Semigroup (Sum(..))


isMonotype :: Type -> Bool
isMonotype TyBool = True
isMonotype TyNat = True
isMonotype TyId{} = True
isMonotype TyVar{} = True
isMonotype (TyArr lty rty) = isMonotype lty && isMonotype rty
isMonotype TyAll{} = False
isMonotype ExTyVar{} = True
isMonotype TySome{} = False
isMonotype (TyTuple tys) = all isMonotype tys
isMonotype (TyList ty) = isMonotype ty

freeVars :: Type -> [String]
freeVars TyBool = []
freeVars TyNat = []
freeVars TyId{} = []
freeVars TyVar{} = []
freeVars (TyArr lty rty) = freeVars lty <> freeVars rty
freeVars (TyAll _ ty) = freeVars ty
freeVars (ExTyVar xvn) = [xvn]
freeVars (TySome _ ty) = freeVars ty
freeVars (TyTuple tys) = concatMap freeVars tys
freeVars (TyList ty) = freeVars ty

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
apply theCtx@(Ctx ctx _) exV@(ExTyVar vn) = subst ctx
  where
    subst [] = exV
    subst ((vn', ExTySolution ty):_)
      | vn == vn' = apply theCtx ty
    subst ((vn', ExTyVarBind):_)
      | vn == vn' = exV
    subst (_:bs) = subst bs
apply _ tv@TyVar{} = tv
apply ctx (TyArr ty ty') = TyArr (apply ctx ty) (apply ctx ty')
apply ctx (TyAll vn ty) = TyAll vn $ apply ctx ty
apply ctx (TyTuple tys) = TyTuple $ fmap (apply ctx) tys
apply ctx (TyList ty) = TyList $ apply ctx ty
apply _ TyBool = TyBool
apply _ TyNat = TyNat

instantiate :: Context -> Type -> Type -> Context
instantiate ctx a b = trace (unwords ["instantiate:", show a, show b]) go a b where
  go (ExTyVar vn) ty =
    case ty of
      ExTyVar vn'
        | orderedInCtx ctx vn vn' -> -- InstLReach
          fill ctx vn' [(vn', ExTySolution $ ExTyVar vn)]
        | otherwise -> fill ctx vn [(vn, ExTySolution $ ExTyVar vn')]
      TyArr lty rty -> -- InstLArr
        let ctx'' = instantiate ctx' lty lExVar
        in instantiate ctx'' rExVar (apply ctx'' rty)
        where
          lExVarN = vn ++ "_₁"
          lExVar = ExTyVar lExVarN
          rExVarN = vn ++ "_₂"
          rExVar = ExTyVar rExVarN
          ctx' = fill ctx vn [ (vn, ExTySolution (TyArr lExVar rExVar))
                             , (lExVarN, ExTyVarBind)
                             , (rExVarN, ExTyVarBind)
                             ]
      TyAll vn' ty' -> -- InstLAllR
        instantiate (addBinding ctx vn' TyVarBind) (ExTyVar vn) ty'
        & dropBindingsUntil vn'
      _ | isMonotype ty -> -- InstLSolve
          --- TODO: check that type is well-formed
          fill ctx vn [(vn, ExTySolution ty)]
  go ty exV@ExTyVar{} =
    case ty of
      TyAll vn' ty' -> -- InstRAll
        instantiate ctx' (typeSubstTop (ExTyVar exvn) ty') exV
        & dropBindingsUntil exmarker
        where
          ctx' = addBindings ctx [(exvn, ExTyVarBind), (exmarker, ExTyMarker)]
          exvn = "^" ++ vn'
          exmarker = "⏵" ++ vn'
      _ -> -- DOUBT: is it ok to just swap argument order?
        instantiate ctx exV ty
  go _ _ = error "internal error: can't instantiate non-existential type variable"


isSubType :: Context -> Type -> Type -> Maybe Context
isSubType ctx a b = trace (unwords ["isSubType:", show a, show b]) go a b where
  go ty (TyAll vn ty') -- <:∀R
    = isSubType ctx' ty ty'
    >>= Just . dropBindingsUntil vn
    where
      ctx' = addBinding ctx vn TyVarBind
  go (TyAll vn ty) ty' -- <:∀L
    = isSubType ctx' (typeSubstTop (ExTyVar exvn) ty) ty'
    >>= Just . dropBindingsUntil exvn
    where
      ctx' = addBindings ctx [(exvn, ExTyVarBind), (exmarker, ExTyMarker)]
      exvn = "^" ++ vn
      exmarker = "⏵" ++ vn
  go (ExTyVar vn) (ExTyVar vn') -- <:Exvar
    | vn == vn' = Just ctx
  go exV@(ExTyVar vn) ty -- <:InstantiateL
    = if vn `elem` freeVars ty
      then Nothing
           -- DOUBT: should it always be Just?
      else Just $ instantiate ctx exV ty
  go ty exV@(ExTyVar vn) -- <:InstantiateR
    = if vn `elem` freeVars ty
      then Nothing
      else Just $ instantiate ctx ty exV
  go (TyVar i l _) (TyVar i' l' _) -- <:Var
    = if i == i' && l == l' then Just ctx else Nothing
  -- isSubType TyVar{} _ = False
  -- isSubType _ TyVar{} = False
  go (TyArr t1 t2) (TyArr t1' t2') -- <:⟶
    = case isSubType ctx t1' t1 of
        Nothing -> Nothing
        Just ctx' -> isSubType ctx' (apply ctx' t2) (apply ctx' t2')
  go TyArr{} _ = Nothing
  go _ TyArr{} = Nothing
  go TyBool TyBool = Just ctx
  go TyNat TyNat = Just ctx
  go (TyList ty) (TyList ty') = isSubType ctx ty ty'


check :: Context -> Term -> Type -> Maybe (Type, Context)
check ctx theTerm theType
  = trace (unwords ["check:", show theTerm, show theType]) go theTerm theType where
  go t aTy@(TyAll vn ty) = -- ∀I
    do
      let ctx' = addBinding ctx vn TyVarBind
      (_, ctx'') <- check ctx' t ty
      return (aTy, dropBindingsUntil vn ctx'')
  go Abs{var, t} arrTy@(TyArr ty ty') = -- ⟶I
    do
      let ctx' = addBinding ctx var $ VarBind ty
      (_, ctx'') <- check ctx' t ty'
      return (arrTy, dropBindingsUntil var ctx'')
  -- TODO: existential type? others?
  go t ty = -- Sub
    do
      (ty', ctx') <- infer ctx t
      ctx'' <- isSubType ctx' ty ty'
      return (ty, ctx'')


infer :: Context -> Term -> Maybe (Type, Context)
infer ctx theTerm = trace ("infer:" ++ show theTerm) go theTerm
  where
    go Var{i, ix} = Just (getTypeFromContext i ctx ix, ctx)
    go TAbs{} = Nothing
    go TApp{} = Nothing
    go Ascribe{t, ty} = -- Anno
      --- TODO: check well-formedness of ty
      check ctx t ty
    go Abs{var, t} = do -- ⟶I⇒
      -- FIXME: names will conflict
      let ctx' = addBindings ctx [ (var, VarBind $ ExTyVar lvar)
                                 , (rvar, ExTyVarBind)
                                 , (lvar, ExTyVarBind)
                                 ]
      (_, ctx'') <- check ctx' t $ ExTyVar rvar
      return (TyArr (ExTyVar lvar) (ExTyVar rvar), dropBindingsUntil var ctx'')
        where
          rvar = var ++ "^β"
          lvar = var ++ "^α"
    go App{l, r} = do -- ⟶E
      (ty, ctx') <- infer ctx l
      inferApp ctx' r (apply ctx' ty)
    -- go Tuple{ts} = (, ctx) . TyTuple <$> mapM (infer ctx) ts
    -- go (TupleProj fi t ixt) = do
    --   ty <- infer ctx t
    --   case ty of
    --     TyTuple tys -> Just $ tys !! natToInt ixt
    --     _ -> unexpected ctx fi "!" (TyTuple []) t ty --FIXME: fix expected type
    go TTrue{} = Just (TyBool, ctx)
    go TFalse{} = Just (TyBool, ctx)
    go TIf{tcond, tt, tf}
      = check ctx tcond TyBool
      >> (infer ctx tt >>= \(ty, _) -> check ctx tf ty)
      <|> (infer ctx tf >>= \(ty, _) -> check ctx tt ty)
    go TZero{} = Just (TyNat, ctx)
    go TSucc{t} = check ctx t TyNat
    go TPred{t} = check ctx t TyNat
    go TIsZero{t} = check ctx t TyNat >>= \(_, ctx') -> Just (TyBool, ctx')


inferApp :: Context -> Term -> Type -> Maybe (Type, Context)
inferApp ctx t = trace (unwords ["inferApp", show t]) go
  where
    go (TyAll vn ty) = do -- ∀App
      let ctx' = addBinding ctx exvn ExTyVarBind
      inferApp ctx' t $ typeSubstTop (ExTyVar exvn) ty
        where
          exvn = "^" ++ vn
    go (ExTyVar exvn) = do -- αApp
      let ctx' = fill ctx exvn [ (exvn, ExTySolution (TyArr (ExTyVar lvar)
                                                            (ExTyVar rvar)))
                               , (lvar, ExTyVarBind)
                               , (rvar, ExTyVarBind)
                               ]
      (_, ctx'')<- check ctx' t (ExTyVar lvar)
      return (ExTyVar rvar, ctx'')
        where
          lvar = exvn ++ "_₁"
          rvar = exvn ++ "_₂"
    go (TyArr lty rty) = do -- ⟶App
      (_, ctx') <- check ctx t lty
      return (rty, ctx')


typeIs :: Context -> Term -> Maybe Type
typeIs ctx t = infer ctx t
  >>= \(ty, ctx') -> Just $ apply ctx' ty

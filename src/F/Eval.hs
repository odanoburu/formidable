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
                 addBinding, addName, dummyInfo, err,
                 getBinding, getTypeFromContext,
                 showTerm, showType,
                 termShift, termSubstTop, tytermSubstTop,
                 typeShift, typeSubstTop
                 )
import F.Decor (decor , decorT)


import Control.Applicative ((<|>))
import Data.Maybe (isJust, fromJust, fromMaybe)
import Prelude hiding ((!!))
--import Debug.Trace (trace)


isVal :: Context -> Term -> Bool
isVal _ Abs{}    = True
isVal _ TAbs{}   = True
isVal ctx (TPack _ _ v _) = isVal ctx v
isVal ctx (Tuple _ ts) = all (isVal ctx) ts
isVal _ TTrue{}  = True
isVal _ TFalse{} = True
isVal _ TZero{}  = True
isVal ctx (TSucc _ t) = isVal ctx t
isVal ctx (TPred _ t) = isVal ctx t
isVal _ Var{} = False
isVal _ App{} = False
isVal _ TApp{} = False
isVal _ TUnpack{} = False
isVal _ Ascribe{} = False
isVal _ Fix{} = False
isVal _ TupleProj{} = False
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
    go (Ascribe _ t _)
      | isVal ctx t = Just t
    go (Ascribe fi t ty) = eval1 ctx t >>= Just . flip (Ascribe fi) ty
    go t@(Fix _ (Abs _ _ _ body)) =
      Just $ termSubstTop t body
    go (Fix fi t) = eval1 ctx t >>= Just . Fix fi
    go (Tuple _ []) = Nothing
    go (Tuple fi ts) = case foldr f (False, []) ts of
      (True, ts') -> Just $ Tuple fi ts'
      (False, _) -> Nothing
      where
        f t (True, ts') = (True, t:ts')
        f t (False, ts') = case eval1 ctx t of
          Just t' -> (True, t':ts')
          Nothing -> (False, t:ts')
    go (TupleProj _ (Tuple _ []) _) = Nothing -- DOUBT: will typeOf get this error?
    go (TupleProj _ (Tuple _ (t:_)) TZero{})
      | isVal ctx t = Just t
    go (TupleProj fi (Tuple fi' (t:ts)) z@TZero{}) =
      eval1 ctx t >>= \t' -> Just $ TupleProj fi (Tuple fi' (t':ts)) z
    go (TupleProj fi (Tuple fi' (_:ts)) (TSucc _ ti)) = Just
      -- DOUBT: how hacky is this? will it show non-sensical error
      -- messages to the user? (I'm guesshoping not since eval1 is
      -- total)
      $ TupleProj fi (Tuple fi' ts) ti
    go (TupleProj fi tu@Tuple{} ti) =
      eval1 ctx ti >>= Just . TupleProj fi tu
    go (TupleProj fi tu ti) =
      eval1 ctx tu >>= \tu' -> Just $ TupleProj fi tu' ti
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
      case simpleTypeOf t1 of
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
      let tyT1 = simpleTypeOf t1
      in case tyT1 of
        TySome _tyY tyT11 ->
          let ctx'  = addBinding ctx tyX TyVarBind
              ctx'' = addBinding ctx' x (VarBind tyT11)
              tyT2  = typeOf ctx'' t2
          in typeShift (-2) tyT2
        _ -> err fi "unpack: existential type expected"
    go (Ascribe fi t ty) =
      let tyT = simpleTypeOf t
      in if typeEqv ctx tyT ty
         then ty
         else err fi
              $ unlines [ "as-type: expected type " ++ showType ctx ty
                        , "for term " ++ showTerm ctx t
                        , "found type", showType ctx tyT, "instead"
                        ]
    go (Fix fi t) =
      case simpleTypeOf t of
        (TyArr ty ty') ->
          if typeEqv ctx ty ty'
          then ty'
          else err fi "fix: domain-incompatible body result"
        _ -> err fi "fix: arrow type expected"
    go (Tuple _ ts) = TyTuple $ fmap (typeOf ctx) ts
    go (TupleProj fi tu ti) =
      case simpleTypeOf tu of
        (TyTuple tys) ->
          if ti `typeIs` TyNat
          then fromMaybe (err fi "!: out of bounds") (tys !! ti)
          else err fi "!: Nat type expected as right argument"
        _ -> err fi "!: tuple type expected as left argument"
    go (TTrue _)  = TyBool
    go (TFalse _) = TyBool
    go (TIf fi tcond tt tf) =
      if tcond `typeIs` TyBool
      then let tytt = typeOf ctx tt
           in if tf `typeIs` tytt
              then tytt
              else err fi "if: arms of conditional have different types"
      else err fi "if: conditional guard is not a boolean"
    go TZero{} = TyNat
    go (TSucc fi t) =
      if t `typeIs` TyNat
      then TyNat
      else err fi "succ: argument must be of type Nat"
    go (TPred fi t) =
      if t `typeIs` TyNat
      then TyNat
      else err fi "pred: argument must be of type Nat"
    go (TIsZero fi t) =
      if t `typeIs` TyNat
      then TyBool
      else err fi "iszero: argument must be of type Nat"
    typeIs t ty = typeEqv ctx ty $ typeOf ctx t
    simpleTypeOf = simplifyType ctx . typeOf ctx

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
    go (TyTuple tys) (TyTuple tys') = and $ zipWith (typeEqv ctx) tys tys'
    go (TyTuple _) _ = False
    go _ (TyTuple _) = False
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


infixl 9  !! -- safe indexing
(!!) :: [a] -> Term -> Maybe a
(x:_) !! TZero{} = Just x
(_:xs) !! (TSucc _ n) = xs !! n
_ !! _ = Nothing

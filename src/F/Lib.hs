module F.Lib
    (
      initialContext,
      processCommand,
      processCommands,
      processInput,
      parseDecorateTerm,
    ) where


import F.Syntax ( Binding(..), Command(..), Context(..), Term(..), Type(..)
                , addBinding, consTerm, consType, headType, isNilTerm, isNilType
                , makeContext, nilType, showError
                , prettyBinding, showTermType, tailType, termShift)
import F.Parser (parseCommands, parseTerm)
import F.Decor (decor)
import F.Eval (InContext(..), eval, evalBinding, fixType, simplifyType, typeOf)


import Data.Bifunctor (bimap)
import Data.List (foldl')
--import Debug.Trace (trace)


processCommand :: Context -> Command -> Either String (InContext (String, Command))
processCommand ctx (Eval fi t) =
  let t' = decor t ctx
      tyT = typeOf ctx t'
      t'' = eval ctx t'
      out = showTermType ctx t'' tyT
  in Right $ (out, Eval fi t'') `InCtx` ctx
processCommand ctx (Bind fi x _bind) =
  case evalBinding ctx _bind of
    Right bind' -> let
      out = unwords [x, showBinding bind']
      in Right $ (out, Bind fi x bind') `InCtx` addBinding ctx x bind'
    Left err -> Left err
  where
    showBinding (TermBind t Nothing)
      = showBinding . TermBind t . Just
      $ typeOf ctx t
    showBinding b = show $ prettyBinding ctx b
processCommand ctx (SomeBind fi tyX x t) =
  case simplifyType ctx $ typeOf ctx t' of
    TySome _ tyBody ->
      let t'' = eval ctx t'
          b = case t'' of
            TPack _ _ t12 _ -> TermBind (termShift 1 t12) (Just tyBody)
            _ -> VarBind tyBody
          ctx' = addBinding ctx tyX TyVarBind
          ctx'' = addBinding ctx' x b
          out = unwords [tyX, x, ":", show tyBody]
      in Right $ (out, SomeBind fi tyX x t'') `InCtx` ctx''
    _ -> Left $ showError fi "Expected existential type"
  where
    t' = decor t ctx

processCommands :: Context -> [Command]
  -> Either String (InContext [(String, Command)])
processCommands initCtx = foldl' go (Right $ [] `InCtx` initCtx)
  where
    go err@Left{} _ = err
    go (Right (os `InCtx` ctx)) cmd
      = processCommand ctx cmd
      >>= \(InCtx (o, cmd') ctx') -> Right $ ((o, cmd'):os) `InCtx` ctx'


processInput :: Context -> FilePath -> String
  -> Either String (InContext [(String, Command)])
processInput initCtx fp input
  = parseCommands fp input >>= processCommands initCtx


parseDecorateTerm :: Context -> String
  -> Either String Term
parseDecorateTerm ctx input = bimap id (`decor` ctx)
  $ parseTerm input


initialContext :: Context
initialContext =
  makeContext [ define "fix" FixOp (`fixType` Nothing)
              , define "nil" (const Nil) nilType
              , define "cons" (const (consTerm mempty)) consType
              , define "isNil" (const (isNilTerm mempty)) isNilType
              , define "head" HeadOp headType
              , define "tail" TailOp tailType
              ]
  where
    define name t fTy = (name, TermBind (t Nothing) . Just $ fTy mempty Nothing)

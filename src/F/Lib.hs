module F.Lib
    (
      processCommand,
      processCommands,
      processInput,
    ) where


import F.Syntax ( Binding(..), Command(..), Context(..), Term(..), Type(..)
                , addBinding, showError, termShift )
import F.Parser (parseCommands)
import F.Decor (decor)
import F.Eval (InContext(..), eval, evalBinding, simplifyType, typeOf)


import Data.List (foldl')
--import Debug.Trace (trace)


processCommand :: Context -> Command -> Either String (InContext (String, Command))
processCommand ctx (Eval fi t) =
  let t' = decor t ctx
      tyT = typeOf ctx t'
      t'' = eval ctx t'
      out = unwords [show t'', ":", show tyT]
  in Right $ (out, Eval fi t'') `InCtx` ctx
processCommand ctx (Bind fi x _bind) =
  case evalBinding ctx _bind of
    Right bind' -> let
      out = unwords [x, ":", show bind']
      in Right $ (out, Bind fi x bind') `InCtx` addBinding ctx x bind'
    Left err -> Left err
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



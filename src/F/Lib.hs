module F.Lib
    (
      processCommand,
      processCommands,
      processFile,
    ) where


import F.Syntax (Command(..), Context(..), addBinding, showError)
import F.Parser (parseCommands)
import F.Eval (InContext(..), decor, eval, evalBinding, typeOf)


import Control.Monad (foldM)
import Data.Functor (($>))
--import Debug.Trace (trace)


processCommand :: Context -> Command -> IO (InContext Command)
processCommand ctx (Eval fi t) = do
  let (t' `InCtx` ctx') = decor t ctx
      tyT = typeOf ctx' t'
      t'' = eval ctx' t'
  putStrLn $ unwords [show t'', ":", show tyT]
  return $ Eval fi t'' `InCtx` ctx
processCommand ctx (Bind fi x _bind) =
  case evalBinding ctx _bind of
    Right bindInCtx@(bind' `InCtx` _) -> do
      putStrLn $ unwords [x, ":", show bindInCtx]
      return $ Bind fi x bind' `InCtx` addBinding ctx x bind'
    Left err -> showError fi err
processCommand _ctx _ = error "TBI - processCommand"


parseFile :: FilePath -> IO (Either String [Command])
parseFile fp = parseCommands fp <$> readFile fp


processFile :: FilePath -> Context -> IO (InContext [Command])
processFile fp initCtx = parseFile fp
  >>= either (\err -> putStrLn err $> mempty) (processCommands initCtx)


processCommands :: Context -> [Command] -> IO (InContext [Command])
processCommands initCtx = foldM go $ [] `InCtx` initCtx
  where
    go (cmds `InCtx` ctx) cmd =
      fmap (: cmds) <$> processCommand ctx cmd

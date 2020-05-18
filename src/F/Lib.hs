module F.Lib
    (
      processCommand,
      processFile,
    ) where


import F.Syntax (Command(..), Context(..), addBinding, showError)
import F.Parser (parseCommands)
import F.Decor (decor)
import F.Eval (InContext(..), eval, evalBinding, typeOf)


import Control.Monad (foldM_)
import Data.Functor (($>))
--import Debug.Trace (trace)


processCommand :: Context -> Command -> IO Context
processCommand ctx (Eval _ t) = do
  let (t', ctx') = decor t ctx
      tyT = typeOf ctx' t'
      t'' = eval ctx' t'
  putStrLn $ unwords [show t'', ":", show tyT]
  return ctx
processCommand ctx (Bind fi x _bind) =
  case evalBinding ctx _bind of
    Right bindInCtx@(bind' `InCtx` _) -> do
      putStrLn $ unwords [x, ":", show bindInCtx]
      return $ addBinding ctx x bind'
    Left err -> showError fi err
processCommand _ctx _ = error "TBI - processCommand"


parseFile :: FilePath -> IO (Either String [Command])
parseFile fp = parseCommands fp <$> readFile fp


processFile :: FilePath -> Context -> IO ()
processFile fp initCtx = parse
  >>= either (\err -> putStrLn err $> mempty) (foldM_ processCommand initCtx)
  where
    parse = parseFile fp


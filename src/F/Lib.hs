module F.Lib
    (
      processCommand,
      processFile,
    ) where


import F.Syntax (Command(..), Context(..), TopLevel(..))
import F.Parser (parseCommands)
import F.Decor (contextualize)
import F.Eval (typeOf, eval)


import Data.Functor (($>))
--import Debug.Trace (trace)


processCommand :: Context -> Command -> String
processCommand ctx (Eval _ t) =
  let tyT = typeOf ctx t
      t'  = eval ctx t
  in unwords [show t', ":", show tyT]
processCommand _ctx _ = error "TBI - processCommand"

parseFile :: FilePath -> IO (Either String [Command])
parseFile fp = parseCommands fp <$> readFile fp


processFile :: FilePath -> IO ()
processFile fp = parse
  >>= decorate
  >>= evaluate
  where
    parse = parseFile fp
    decorate = either (\err -> putStrLn err $> mempty) (pure . contextualize)
    evaluate (TopLevel ctx cmds) = mapM_ (putStrLn . processCommand ctx) cmds

module Main where


import F.Lib (processFile, processCommands)
import F.Eval (InContext(..))
import F.Parser (parseCommands)
import F.Syntax (Context(..))

import Control.Monad.IO.Class (liftIO)
import Data.Char (isSpace)
import Options.Applicative
import System.Console.Haskeline (InputT, defaultSettings, getInputLine
                                , outputStrLn, runInputT)
import System.Directory (canonicalizePath)


data CLI = CLI [FilePath] CLIsub
  deriving (Eq, Show)


data CLIsub
  = REPL
  | Eval FilePath
  deriving (Eq, Show)


showHelpOnErrorExecParser :: ParserInfo a -> IO a
showHelpOnErrorExecParser = customExecParser (prefs showHelpOnError)


parseSubCommand :: Parser CLIsub -> Parser CLI
parseSubCommand subcommand = CLI <$> many importDir <*> subcommand
  where
    importDir = option str
      (metavar "SEARCHDIR" <> short 'I' <> long "import-path"
       <> help "Add SEARCHDIR to search list for imports")


parseCommand :: Parser CLI
parseCommand = hsubparser
  -- start repl
  $ command "repl" (info (helper <*> parseSubCommand (pure REPL))
                     (fullDesc <> progDesc "Start REPL"))
  -- eval file
  <> command "eval" (info (helper <*> parseSubCommand evalP)
                      (fullDesc <> progDesc "Evaluate FILE"))
  where
    evalP = Eval <$> strArgument (metavar "FILE" <> help "Input FILE to eval")


cliProgDesc :: String
cliProgDesc =
  "Evaluate system F programs"

cliHeader :: String
cliHeader = "formidable — system F interpreter."

runREPL :: [FilePath] -> IO ()
runREPL _ = runInputT defaultSettings (loop mempty)
  where
    loop :: Context -> InputT IO ()
    loop ctx = do
      minput <- getInputLine "formidable> "
      case splitAt 1 . dropWhile isSpace <$> minput of
        Just (":", metaCommand) -> handleMetaCommand metaCommand
        Just ("", "") -> loop ctx
        Just (x, xs) ->
          let input = x ++ xs
          in do
            let parseRes = parseCommands "*REPL*" input
            case parseRes of
              Right cmds -> do
                (_ `InCtx` ctx') <- liftIO $ processCommands ctx cmds
                loop ctx'
              Left err -> outputStrLn err *> loop ctx
            return ()
        Nothing -> return () -- control-D and stuff
        where
          handleMetaCommand "exit" = return ()
          handleMetaCommand "quit" = return ()
          handleMetaCommand "context" = outputStrLn (show ctx) *> loop ctx
          handleMetaCommand _ = outputStrLn "Unrecognized command" *> loop ctx


main :: IO ()
main = do
  (CLI importDirs' subcommand) <- showHelpOnErrorExecParser
                                 $ info (helper <*> parseCommand)
                                        (fullDesc <> progDesc cliProgDesc
                                         <> header cliHeader)
  importDirs <- mapM canonicalizePath importDirs'
  case subcommand of
    REPL -> runREPL importDirs
    Eval f -> (fmap show <$> processFile f mempty) >>= putStrLn . thing

module Main where


import F.Lib (processFile)


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
runREPL _ = runInputT defaultSettings loop
  where
    loop :: InputT IO ()
    loop = do
      minput <- getInputLine "formidable> "
      case splitAt 1 . dropWhile isSpace <$> minput of
        Just (":", metaCommand) -> handleMetaCommand metaCommand
        Just (_, "") -> loop
        Just (_x, _xs) -> error "TBI - repl"
        --   let mStatement = prepareStatement $ x ++ xs
        --   t' <- either (\msg -> outputStrLn msg >> return t)
        --                (\st -> liftIO (executeStatement t st)
        --                  <* outputStrLn "Executed.")
        --                mStatement
        --   loop t'
        Nothing -> return () -- control-D and stuff
        where
          handleMetaCommand "exit" = return ()
          handleMetaCommand "quit" = return ()
          handleMetaCommand _ = outputStrLn "Unrecognized command" *> loop


main :: IO ()
main = do
  (CLI importDirs' subcommand) <- showHelpOnErrorExecParser
                                 $ info (helper <*> parseCommand)
                                        (fullDesc <> progDesc cliProgDesc
                                         <> header cliHeader)
  importDirs <- mapM canonicalizePath importDirs'
  case subcommand of
    REPL -> runREPL importDirs
    Eval f -> (show <$> processFile f) >>= putStrLn

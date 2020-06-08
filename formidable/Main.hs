module Main where


import F.Lib (processInput, parseDecorateTerm)
import F.Eval (InContext(..), typeOf)
import F.Parser (parseCommands)
import F.Syntax (Context(..), showTermType)

--import Control.Monad.IO.Class (liftIO)
import Data.Char (isSpace)
import Options.Applicative
import System.Console.Haskeline (InputT, defaultSettings, getInputLine
                                , outputStrLn, runInputT)
import System.Directory (canonicalizePath)
import System.IO (hPutStrLn, stderr)


data CLI = CLI [FilePath] CLIsub
  deriving (Eq, Show)


data CLIsub
  = REPL
  | Eval Input String
  | Parse Input String
  deriving (Eq, Show)

data Input = File | StdIn
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
                      (fullDesc <> progDesc "Evaluate INPUT"))
  -- only parse
  <> command "parse" (info (helper <*> parseSubCommand parseP)
                      (fullDesc <> progDesc "Parse INPUT"))
  where
    input = flag File StdIn (short 'i' <> long "in"
                            <> help "Read INPUT from standard input")
            <|> flag' File (short 'F' <> long "file"
                           <> help "Read INPUT from file (default)")
    evalP = Eval
      <$> input
      <*> strArgument (metavar "INPUT" <> help "INPUT to evaluate")
    parseP = Parse <$> input <*> strArgument (metavar "INPUT"
                                              <> help "INPUT to parse")


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
        Just (":", metaCommand) ->
          case break (== ' ') metaCommand of
            (name, arg) -> handleMetaCommand name arg
        Just ("", "") -> loop ctx
        Just (x, xs) ->
          let input = x ++ xs
          in do
            let res = processInput ctx "*REPL*" input
            case res of
              Right (os `InCtx` ctx') -> do
                mapM_ (outputStrLn.fst) os
                loop ctx'
              Left err -> outputStrLn err *> loop ctx
            return ()
        Nothing -> return () -- control-D and stuff
        where
          handleMetaCommand "e" _ = return ()
          handleMetaCommand "exit" _ = return ()
          handleMetaCommand "q" _ = return ()
          handleMetaCommand "quit" _ = return ()
          handleMetaCommand "c" t = handleMetaCommand "context" t
          handleMetaCommand "context" _ = outputStrLn (show ctx) *> loop ctx
          handleMetaCommand "t" t = handleMetaCommand "type" t
          handleMetaCommand "type" tStr = case parseDecorateTerm ctx tStr of
            Left err -> outputStrLn err *> loop ctx
            Right t -> let ty = typeOf ctx t
              in outputStrLn (showTermType ctx t ty) *> loop ctx
          handleMetaCommand _ _ = outputStrLn "Unrecognized command" *> loop ctx


main :: IO ()
main = do
  (CLI importDirs' subcommand) <- showHelpOnErrorExecParser
                                 $ info (helper <*> parseCommand)
                                        (fullDesc <> progDesc cliProgDesc
                                         <> header cliHeader)
  importDirs <- mapM canonicalizePath importDirs'
  case subcommand of
    REPL -> runREPL importDirs
    Eval what input -> caseInput what input (processInput mempty)
      >>= either putErr (mapM_ (putStrLn . fst) . reverse . thing)
    Parse what input -> caseInput what input parseCommands
      >>= either putErr print
  where
    caseInput File fp f = f fp <$> readFile fp
    caseInput StdIn input f = return $ f "*std-in*" input
    putErr = hPutStrLn stderr

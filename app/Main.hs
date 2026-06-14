module Main (main) where

import Ligare.Core.Eval
import Ligare.Pretty
import Ligare.Front.Parser
import Ligare.Checker.Context
import Ligare.Checker.Checker
import Control.Monad.IO.Class
import Data.List
import System.Exit (exitSuccess)
import System.Console.Haskeline
import Debug.Trace (trace)

main :: IO ()
main = loop

loop :: IO ()
loop = 
  runInputT settings $ do
    input' <- getInputLine "> "
    liftIO $ case input' of
      Nothing -> exitSuccess
      Just ":q" -> exitSuccess
      Just i -> inner i
  where
    settings = Settings {
      complete = completeFilename,
      historyFile = Nothing,
      autoAddHistory = True
    }

inner :: String -> IO ()
inner input = do
  if ":check " `isPrefixOf` input then do
    let rest = drop (length (":check " :: String)) input
    case break (== ':') rest of
      (termStr, ':' : rawConstr) -> do
        let constrStr = dropWhile (== ' ') rawConstr
        putStrLn termStr 
        case (parseExprTop termStr, parseConstraintFromString constrStr) of
          (Right tm, Right c) -> do
            putStrLn (show c)
            case check emptyCtx tm c of
              Left err -> putStrLn ("Check failed: " ++ err)
              Right _  -> putStrLn "OK"
          _ -> putStrLn "Parse error"
      _ -> putStrLn "Usage: :check <term> : <constraint>"
  else
    case parseExprTop input of
      Left err -> putStrLn ("Parse error: " ++ err)
      Right term -> putStrLn (pretty (eval term))
  loop



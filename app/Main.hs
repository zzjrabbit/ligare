module Main (main) where

import Control.Monad.IO.Class
import Data.IORef
import Data.List (dropWhileEnd, isPrefixOf)
import Ligare.Checker.Checker
import Ligare.Checker.Context
import Ligare.Core.Eval
import Ligare.Front.Parser
import Ligare.Pretty
import System.Console.Haskeline
import System.Exit (exitSuccess)

main :: IO ()
main = do
  tableRef <- newIORef emptyTable
  loop tableRef

loop :: IORef ConstraintTable -> IO ()
loop tableRef =
  runInputT settings $ do
    input' <- getInputLine "> "
    liftIO $ case input' of
      Nothing -> exitSuccess
      Just ":q" -> exitSuccess
      Just i -> inner tableRef i
  where
    settings =
      Settings
        { complete = completeFilename,
          historyFile = Nothing,
          autoAddHistory = True
        }

splitAtLastColon :: String -> (String, String)
splitAtLastColon s = go (0 :: Int) (length s) s
  where
    go _ 0 s' = (s', "")
    go depth i s'
      | i <= 0 = (s', "")
      | s' !! (i - 1) == ')' = go (depth + 1) (i - 1) s'
      | s' !! (i - 1) == '(' = go (depth - 1) (i - 1) s'
      | s' !! (i - 1) == ':' && depth == 0 = (take (i - 1) s', drop (i - 1) s')
      | otherwise = go depth (i - 1) s'

inner :: IORef ConstraintTable -> String -> IO ()
inner tableRef input = do
  if ":refine " `isPrefixOf` input
    then do
      let rest = drop (length (":refine " :: String)) input
      case parseRefineTop rest of
        Right (name, parent, p) -> do
          modifyIORef' tableRef (addRefine name parent p)
          putStrLn ("Defined refinement: " ++ name)
        Left err -> putStrLn ("Parse error: " ++ err)
    else
      if ":check " `isPrefixOf` input
        then do
          let rest = drop (length (":check " :: String)) input
          let (termStr, rawConstr) = splitAtLastColon rest
          case rawConstr of
            ':' : constrStr -> do
              let termStr' = dropWhileEnd (== ' ') termStr
              let constrStr' = dropWhile (== ' ') constrStr
              putStrLn termStr'
              case (parseExprTop termStr', parseConstraintFromString constrStr') of
                (Right tm, Right c) -> do
                  putStrLn (show c)
                  table <- readIORef tableRef
                  case check table emptyCtx tm c of
                    Left err -> putStrLn ("Check failed: " ++ err)
                    Right _ -> putStrLn "OK"
                _ -> putStrLn "Parse error"
            _ -> putStrLn "Usage: :check <term> : <constraint>"
        else case parseExprTop input of
          Left err -> putStrLn ("Parse error: " ++ err)
          Right term -> putStrLn (pretty (eval term))
  loop tableRef

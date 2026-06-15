module Main (main) where

import Control.Monad (foldM)
import Data.List (dropWhileEnd, isPrefixOf)
import Ligare.Checker.Checker
import Ligare.Checker.Context
import Ligare.Core.Eval
import Ligare.Core.Syntax
import Ligare.Front.Parser
import Ligare.Pretty
import System.Environment (getArgs)
import System.Exit (exitFailure)
import System.IO (hPutStrLn, stderr)

-- | Compiler state threaded through source file processing.
data CompState = CompState
  { csTable :: ConstraintTable,
    csEnv :: [(Name, Term)]
  }

main :: IO ()
main = do
  args <- getArgs
  case args of
    [] -> do
      hPutStrLn stderr usage
      exitFailure
    _ ->
      let (files, mEval) = parseArgs args
       in if null files
            then do
              hPutStrLn stderr "No input files given."
              exitFailure
            else do
              _finalState <-
                foldM processFile (CompState emptyTable []) files
              case mEval of
                Nothing -> pure ()
                Just expr ->
                  case parseExprTop expr of
                    Left err ->
                      hPutStrLn stderr ("--eval parse error: " ++ err)
                    Right term ->
                      case eval term of
                        Left err -> hPutStrLn stderr ("--eval error: " ++ err)
                        Right val -> putStrLn (pretty val)
              pure ()

usage :: String
usage =
  unlines
    [ "Ligare compiler frontend",
      "",
      "Usage: ligare [--eval <expr>] <file>...",
      "",
      "Options:",
      "  --eval <expr>   Evaluate an expression after processing all files",
      "",
      "Each source file may contain:",
      "  def <name> [params] [: <type>] = <body>    top-level definition",
      "  #check <term> : <constraint>               type-check assertion",
      "  <expr>                                      evaluate expression"
    ]

parseArgs :: [String] -> ([FilePath], Maybe String)
parseArgs = go [] Nothing
  where
    go files mEval [] = (reverse files, mEval)
    go files _mEval ("--eval" : expr : rest) = go files (Just expr) rest
    go files mEval (f : rest) = go (f : files) mEval rest

-- | Process a single source file line by line.
processFile :: CompState -> FilePath -> IO CompState
processFile st file = do
  content <- readFile file
  let ls = lines content
  go st file (1 :: Int) ls
  where
    go cs _ _ [] = pure cs
    go cs fname lineNum (l : rest)
      | null (dropWhile (== ' ') l) = go cs fname (lineNum + 1) rest
      | "--" `isPrefixOf` dropWhile (== ' ') l =
          go cs fname (lineNum + 1) rest
      | "#check " `isPrefixOf` l = do
          let raw = drop (length ("#check " :: String)) l
          let (termStr, constrStr) = splitAtLastColon raw
          case constrStr of
            ':' : cs' -> do
              let termStr' = dropWhileEnd (== ' ') termStr
              let constrStr' = dropWhile (== ' ') cs'
              case (parseExprTop termStr', parseConstraintFromString constrStr') of
                (Right tm, Right c) -> do
                  case check (csTable cs) emptyCtx tm c of
                    Left err ->
                      hPutStrLn
                        stderr
                        (fname ++ ":" ++ show lineNum ++ ": check failed: " ++ err)
                    Right _ ->
                      putStrLn ("[" ++ fname ++ ":" ++ show lineNum ++ "] OK")
                _ ->
                  hPutStrLn
                    stderr
                    (fname ++ ":" ++ show lineNum ++ ": constraint parse error")
            _ ->
              hPutStrLn
                stderr
                (fname ++ ":" ++ show lineNum ++ ": usage: #check <term> : <constraint>")
          go cs fname (lineNum + 1) rest
      | "def " `isPrefixOf` l = do
          case parseDefTop l of
            Right (name, Refine _ parent predicate) -> do
              let cs' = cs {csTable = addRefine name parent predicate (csTable cs)}
              putStrLn ("[" ++ fname ++ ":" ++ show lineNum ++ "] refinement: " ++ name)
              go cs' fname (lineNum + 1) rest
            Right (name, term) -> do
              let cs' = cs {csEnv = (name, term) : csEnv cs}
              putStrLn ("[" ++ fname ++ ":" ++ show lineNum ++ "] defined: " ++ name)
              go cs' fname (lineNum + 1) rest
            Left err -> do
              hPutStrLn stderr (fname ++ ":" ++ show lineNum ++ ": parse error: " ++ err)
              go cs fname (lineNum + 1) rest
      | otherwise = do
          case parseExprTop l of
            Left err -> do
              hPutStrLn stderr (fname ++ ":" ++ show lineNum ++ ": parse error: " ++ err)
            Right term ->
              case eval term of
                Left err ->
                  hPutStrLn
                    stderr
                    (fname ++ ":" ++ show lineNum ++ ": eval error: " ++ err)
                Right val ->
                  putStrLn ("[" ++ fname ++ ":" ++ show lineNum ++ "] " ++ pretty val)
          go cs fname (lineNum + 1) rest

-- | Split "term : constraint" at the rightmost top-level colon.
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

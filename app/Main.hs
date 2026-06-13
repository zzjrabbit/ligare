module Main (main) where

import Ligare.Core.Eval
import Ligare.Pretty
import Ligare.Front.Parser
import Ligare.Core.Syntax

main :: IO ()
main = do
  let s = "\\x. ((\\x. x)  x)"
  case parseExpr s of Right t -> do_main t; Left e -> putStrLn ("Parse error: " ++ e)

do_main :: Term -> IO ()
do_main t = do
  print t
  let t' = eval t
  print t'
  putStrLn (pretty t')


import Data.List (delete, nub)
import System.Environment (getArgs)

import Dynamics (pretty, run, Val(..))
import Parser (parseFile)
import Print
import Test

runTests = testExamples >> testArith

prelude = "examples/examples.txt"

printHelp :: IO ()
printHelp = mapM_ putStrLn
 ["Usage:"
 ,"  --check file                  |  typecheck a file"
 ,"  --test                        |  run the tests"
 ,"  --elab file                   |  elaborate a file, printing solved metavariables"
 ,"  --run file                    |  execute main function in a file"
 ,"  --print [--latex] file [fn]   |  pretty print a file, optionally a specific function"
 ,"  --help                        |  print this text"
 ]

go :: [String] -> IO ()
go ["--help"] = printHelp
go ["--test"] = runTests
go ("--check":fs) = () <$ elabFiles (nub (prelude:fs))
go ("--elab":fs) = elabFiles (nub (prelude:fs)) >>= printFile Plain 80 Nothing
go ("--run":fs) = do
  env <- elabFiles (nub (prelude:fs))
  putStrLn $ "Main output: " ++ pretty (run env "main" [] [] [])
go ("--print":args) = case args' of
  [file] -> parseFile file >>= printFile fmt 80 Nothing
  [file, fn] -> parseFile file >>= printFile fmt 80 (Just fn)
  _ -> do
    putStrLn "Too many args to --print"
    putStrLn ""
    printHelp
 where
  fmt = if "--latex" `elem` args then Latex else Plain
  args' = delete "--latex" args
go ["--preamble"] = printPreamble
go x = do
 putStrLn $ "Invalid option " ++ show x
 putStrLn ""
 printHelp

main :: IO ()
main = getArgs >>= Main.go

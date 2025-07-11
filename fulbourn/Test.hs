module Test where

import Bwd
import Checker
import Dynamics (Env(..), Val(..), GEnv, expr, run)
import Examples
import Parser (parseFile)
import Syntax

import Control.Monad.Except
import Control.Monad.State
import Data.Functor
import Data.Traversable (for)
import System.FilePath

emptyEnv = Env [] [] []

examples_dir = "./examples"

assertEq :: (Eq a, Show a) => a -> a -> IO ()
assertEq exp act
 | exp == act = putStrLn ":-)"
 | otherwise = error $ "Test failed: expected " ++ show exp ++ " got " ++ show act

simpleTest :: GEnv
           -> Expr String -- Expected result
           -> (String, [Integer], [Expr String]) -- Fn in question, with its args
           -> IO ()
simpleTest genv exp (fn, ns, args) = do
  let vargs = expr emptyEnv <$> args
  let vexp = expr emptyEnv exp
  assertEq vexp (run genv fn ns [] vargs)

tt = "tt" :$ []
ff = "ff" :$ []

testExamples = do
  genv <- elabFiles [examples_dir </> "examples.txt"]
  simpleTest genv tt ("not", [], [ff])
  simpleTest genv ff ("and", [], [tt, ff])
  simpleTest genv tt ("xor", [], [tt, ff])
  simpleTest genv ("pair" :$ [tt, ff]) ("hadd", [], [tt, tt])
  simpleTest genv tt ("eqn", [0], [mkNum 1 1, mkNum 1 1])
  simpleTest genv ff ("eqn", [0], [mkNum 1 1, mkNum 1 0])
  simpleTest genv tt ("eqn", [1], [mkNum 2 0, mkNum 2 0])
  simpleTest genv ff ("eqn", [1], [mkNum 2 1, mkNum 2 2])
  simpleTest genv tt ("eqn", [2], [mkNum 4 3, mkNum 4 3])
  simpleTest genv ff ("eqn", [2], [mkNum 4 5, mkNum 4 1])
  simpleTest genv ("pair" :$ [mkNum 2 0, mkNum 2 2]) ("cas", [1], ["pair" :$ [mkNum 2 2, mkNum 2 0]])
  let gt13 = Rec "ltn" (Just [Suc $ Suc Zer]) :/ mkNum 4 13
  simpleTest genv tt ("any", [4], [gt13, list [mkNum 4 5, mkNum 4 14, mkNum 4 9, mkNum 4 11]])
  simpleTest genv ff ("any", [3], [gt13, list [mkNum 4 5, mkNum 4 13, mkNum 4 7]])
  simpleTest genv (list [mkNum 2 1, mkNum 2 3]) ("merge", [0], [Rec "cas" (Just [Suc Zer]), list [mkNum 2 3], list [mkNum 2 1]])
  let cas_two = Rec "cas" (Just [Suc $ Suc Zer])
  simpleTest genv (list [mkNum 4 1, mkNum 4 3, mkNum 4 5, mkNum 4 7]) ("merge", [1], [cas_two, list [mkNum 4 3, mkNum 4 7], list [mkNum 4 1, mkNum 4 5]])
  simpleTest genv (list [mkNum 4 1, mkNum 4 3, mkNum 4 5, mkNum 4 7]) ("bitonic_to_sorted", [2], [cas_two, list [mkNum 4 3, mkNum 4 7, mkNum 4 5, mkNum 4 1]])
  testSort genv (list [mkNum 4 3, mkNum 4 7, mkNum 4 10, mkNum 4 13]) [2] [cas_two, list [mkNum 4 10, mkNum 4 13, mkNum 4 7, mkNum 4 3]]
  testSort genv (list [mkNum 4 1, mkNum 4 3, mkNum 4 5, mkNum 4 8, mkNum 4 10, mkNum 4 12, mkNum 4 13, mkNum 4 14])
     [3] [cas_two, list [mkNum 4 10, mkNum 4 5, mkNum 4 8, mkNum 4 1, mkNum 4 13, mkNum 4 12, mkNum 4 14, mkNum 4 3]]
 where
  testSort genv expected natargs inps = do
   simpleTest genv expected ("sort", natargs, inps)
   simpleTest genv expected ("bitonic_sort", natargs, ff:inps)

testArith = do
  genv <- elabFiles [examples_dir </> "examples.txt", examples_dir </> "arith.txt"]
  simpleTest genv ("pair" :$ [tt, ff]) ("hadd", [], [tt, tt])
  testAdders genv ("pair" :$ [tt, mkNum 0 0]) [0] [mkNum 0 0, mkNum 0 0, tt]
  testAdders genv ("pair" :$ [ff, mkNum 1 1]) [1] [mkNum 1 1, mkNum 1 0, ff]
  testAdders genv ("pair" :$ [tt, mkNum 1 0]) [1] [mkNum 1 0, mkNum 1 1, tt]
  testAdders genv ("pair" :$ [tt, mkNum 1 1]) [1] [mkNum 1 1, mkNum 1 1, tt]
  testAdders genv ("pair" :$ [ff, mkNum 2 3]) [2] [mkNum 2 1, mkNum 2 2, ff]
  testAdders genv ("pair" :$ [tt, mkNum 2 1]) [2] [mkNum 2 3, mkNum 2 1, tt]
  testAdders genv ("pair" :$ [ff, mkNum 9 269]) [9] [mkNum 9 211, mkNum 9 57, tt]
  simpleTest genv (mkNum 8 143) ("mul", [2], [mkNum 4 11, mkNum 4 13])
  simpleTest genv (mkMatrix 4 [[7, 15], [3, 9], [4, 7]]) ("transpose", [2, 3], [mkMatrix 4 [[7, 3, 4], [15, 9, 7]]])
  simpleTest genv (list [mkNum 4 5]) ("concatSq", [0], [mkMatrix 4 [[5]]])
  simpleTest genv (list $ map (mkNum 4) [1,4,7,11]) ("concatSq", [1], [mkMatrix 4 [[1,4], [7,11]]])
  let elems = [[0,1,3,2], [4,5,7,11], [10,8,13,6], [12,9,14,15]]
  simpleTest genv (list $ map (mkNum 4) $ concat elems) ("concatSq", [2], [mkMatrix 4 elems])
  let elems = map (\n -> [8*n..8*n+7]) [0..7]
  simpleTest genv (list $ map (mkNum 8) $ concat elems) ("concatSq", [3], [mkMatrix 8 elems])
  simpleTest genv (mkMatrix 8 [[4,6,10,14],[6,9,15,21],[10,15,25,35]])
        ("matmul", [3,1,4,3], [mkMatrix 8 [[2],[3],[5]], mkMatrix 8 [[2,3,5,7]]])
 where
  testAdders genv expected nat_args inps = do
   simpleTest genv expected ("adder", nat_args, inps)
   simpleTest genv expected ("spec_adder", nat_args, inps)

mkMatrix :: Int -> [[Int]] -> Expr String
mkMatrix bitLen = list . map (list . map (mkNum bitLen))

runChecker :: Show a => Checking a -> IO a
runChecker m = case flip runState (0, B0) $ runExceptT m of
  (Right a, _) -> pure a
  (Left terr, (_, ctx)) -> putStrLn "\\x1b[1;31m" *> -- Doesn't work in GHCI
                           printCtx ctx *>
                           error (show terr)


elabFiles :: [String] -> IO [(String, (RawScheme, [RawClause]))]
elabFiles names = do
  defs <- concat <$> mapM parseFile names
  defs <- runChecker $ do
    -- Add signatures for each def to the context
    for defs $ \(str, (rawScm, _)) -> do
      scm <- elabScheme rawScm
      addToCtx (Defn str scm)
    -- Individually check every clause
    for defs $ \(x, (ty, cs)) -> (x,) . (ty,) <$> traverse elabClause cs
  putStrLn "Checking success :-)"
  pure defs

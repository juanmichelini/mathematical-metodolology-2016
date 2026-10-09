-- Regression check for the lemma-proving tactics (Prove.hs).
--
-- Runs Test.provelemas 30, which tries to prove every hand-written lemma in
-- Test.lemas (using the earlier lemmas as hypotheses), and reports which
-- proofs are complete. Exits with status 1 if any lemma is left unproved.
module Main where

import qualified Test as T
import Prove (headProof)
import PrettyPrint (toCLI)
import System.Exit

main :: IO ()
main = do
  let proved   = T.provedlemas
      unproved = T.unprovedlemas
  putStrLn ("Lemmas in Test.lemas: " ++ show (length T.lemas))
  putStrLn ("Proved:   " ++ show (length proved))
  putStrLn ("Unproved: " ++ show (length unproved))
  putStrLn "\n== PROVED =="
  mapM_ (putStrLn . toCLI . headProof) proved
  putStrLn "\n== UNPROVED =="
  mapM_ (putStrLn . toCLI . headProof) unproved
  if null unproved then exitSuccess else exitWith (ExitFailure 1)

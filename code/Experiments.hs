-- Measurements for reproducing the thesis results (issues #6 and #8).
--
--  * how many candidates the first and second search enumerate and keep, and
--    the CPU time of each search (Main.hs, paciencia = 30)
--  * how the first search changes with the `paciencia` parameter
--  * the lemmas and proofs found for flipexp (exponentiation) in Test.hs
module Experiments where

import qualified Main as M
import qualified Test as T
import Control.Exception (evaluate)
import System.CPUTime (getCPUTime)
import System.IO
import Syntax
import Prove (headProof, Proof)
import Type (Type)
import Propose (findlemas)
import PrettyPrint (toCLI)

timed :: String -> IO a -> IO a
timed label act = do
  t0 <- getCPUTime
  r <- act
  t1 <- getCPUTime
  putStrLn ("  [" ++ label ++ ": " ++ show (fromIntegral (t1 - t0) / 1e12 :: Double) ++ " s CPU]")
  hFlush stdout
  return r

-- Same as Main.candidatosFstSel but with the search limit as a parameter.
firstSearchWith :: Int -> [((Term, Type), [Proof])]
firstSearchWith n =
  filter ((> 3) . length . map headProof . snd)
    [ ((f, t), findlemas [(Var "f", f)] ((Atm (Var "f"), t) : M.cerothTEnv) M.datas n M.cerothRec (Var "f"))
    | (f, t) <- M.candidatosFst ]

main :: IO ()
main = do
  hSetBuffering stdout LineBuffering
  putStrLn "== Main.hs: search sizes (paciencia = 30) =="
  _ <- timed "enumerate first-search candidates" (evaluate (length M.candidatosFst))
  putStrLn ("  first search candidates:  " ++ show (length M.candidatosFst))
  _ <- timed "first search (findlemas)" (evaluate (length M.candidatosFstSel))
  putStrLn ("  first search kept:        " ++ show (length M.candidatosFstSel) ++ "  (thesis: f0-f2 = 3)")
  _ <- timed "enumerate second-search candidates" (evaluate (length M.candidatosSnd))
  putStrLn ("  second search candidates: " ++ show (length M.candidatosSnd))
  _ <- timed "second search (findlemas)" (evaluate (length M.candidatosSndSel))
  putStrLn ("  second search kept:       " ++ show (length M.candidatosSndSel) ++ "  (thesis: f3-f30 = 28)")

  putStrLn "\n== First search vs paciencia =="
  mapM_ (\n -> do
           r <- timed ("paciencia=" ++ show n) (evaluate (firstSearchWith n))
           putStrLn ("  paciencia=" ++ show n ++ ": kept " ++ show (length r)
                     ++ ", lemmas per kept function " ++ show (map (length . snd) r)))
        [5, 10, 20, 30, 40]

  putStrLn "\n== Test.hs: lemmas found for suma, mult (inputs to the flipexp search) =="
  _ <- timed "suma" (evaluate (length T.lsumad))
  mapM_ (putStrLn . ("  suma:  " ++) . toCLI) T.lsuma
  _ <- timed "mult" (evaluate (length T.lmultd))
  mapM_ (putStrLn . ("  mult:  " ++) . toCLI) T.lmult

  putStrLn "\n== Test.hs: lemmas found for flipexp (thesis Sec. 10: two lemmas) =="
  _ <- timed "flipexp" (evaluate (length T.lexpd))
  mapM_ (putStrLn . ("  flipexp: " ++) . toCLI) T.lexp

  putStrLn "\n== Test.hs: full proofs found for flipexp =="
  mapM_ (\p -> putStrLn (toCLI p) >> putStrLn "") T.lexpd

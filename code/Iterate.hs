-- Third iteration of the method.
--
-- Main.hs runs two searches: the first uses only the base types (f0-f2), the
-- second may use f0-f2 as building blocks (f3-f30). This program runs the next
-- step in the same way: the 31 functions found so far, and the lemmas proved
-- about them, are available, and we look for new functions that use at least
-- one of f3-f30. The selection rule is the one Main uses for the second search
-- (at least 2 lemmas proved by induction).
--
-- Usage:
--   iterate-search count                      number of candidates
--   iterate-search sample K                   time K evenly spaced candidates
--   iterate-search run SHARD SHARDS SECONDS   process candidates i with
--                                             i mod SHARDS == SHARD until the
--                                             CPU time budget is used up
module Iterate where

import qualified Main as M
import Syntax
import Util
import Type
import Data.List
import Data.Maybe
import Compute
import Prove
import Propose
import PrettyPrint
import Control.Exception (evaluate)
import System.CPUTime (getCPUTime)
import System.Environment (getArgs)
import System.IO (hSetBuffering, stdout, BufferMode(LineBuffering))

-- Functions found by the second search, with their proofs (as numbered in Main).
itSndFuns :: [(((Atm, Term), Type), [Proof])]
itSndFuns = M.namedSndSel

itSndEnv :: Env
itSndEnv = M.fstEnv ++ [ (nom, def) | (((nom, def), _), _) <- itSndFuns ]

itSndTEnv :: TEnv
itSndTEnv = M.fstTEnv ++ [ (Atm nom, typ) | (((nom, _), typ), _) <- itSndFuns ]

-- Rewrite rules known after the second search.
itSndRec :: Rec
itSndRec = addAffirms itSndEnv M.fstRec (map headProof (concat (snds itSndFuns)))

itNewFuns :: [Atm]
itNewFuns = [ nom | (((nom, _), _), _) <- itSndFuns ]

itDatas :: [DatasH]
itDatas = M.datas

-- The same two base types Main uses for its second search.
itBaseTypes :: [Type]
itBaseTypes = map (TAtm . TCon . fst) [itDatas !! 1, itDatas !! 3]

itUsesNew :: Term -> Bool
itUsesNew e = any (\a -> contiene a e) itNewFuns

itCandidates :: [(Term, Type)]
itCandidates = uni ++ bin
  where
    ok e = contiene (Var "f") e && itUsesNew e
    uni = filter (ok . fst)
            [ (f, tipo) | tipo <- armarTip 1 itBaseTypes
                        , f <- enumFun itSndRec "f" tipo itDatas itSndTEnv ]
    bin = filter (\(e, _) -> ok e && twice e)
            [ (f, tipo) | tipo <- armarTip 2 itBaseTypes
                        , f <- enumFun itSndRec "f" tipo itDatas itSndTEnv ]
    twice e = case e of
                Abs _ (Abs y b) -> length (take 2 (filter ((Var y) ==) (termToAtm b))) == 2
                _               -> False

itSearch :: (Term, Type) -> [Proof]
itSearch (f, t) =
  findlemas ((Var "f", f) : itSndEnv) ((Atm (Var "f"), t) : itSndTEnv) itDatas M.paciencia itSndRec (Var "f")

itSecs :: IO Double
itSecs = do
  t <- getCPUTime
  return (fromIntegral t / 1.0e12)

itReport :: Int -> (Term, Type) -> [Proof] -> String
itReport i (f, t) ps = unlines (
  [ "== KEPT cand " ++ show i ++ " =="
  , "f = " ++ toCLI f
  , "f :: " ++ toCLI t ] ++
  [ "  lemma" ++ (if containsIndc p then "*" else " ") ++ " " ++ toCLI (headProof p) | p <- ps ])

itSample :: Int -> Int -> IO ()
itSample k n = mapM_ one [0 .. k - 1]
  where
    step = max 1 (n `div` k)
    one j = do
      let i = min (n - 1) (j * step)
      a <- itSecs
      let ps  = itSearch (itCandidates !! i)
          ind = length (filter containsIndc ps)
      _ <- evaluate ind
      b <- itSecs
      putStrLn ("sample cand " ++ show i ++ ": " ++ show (b - a) ++ " s, "
                ++ show (length ps) ++ " lemmas, " ++ show ind ++ " by induction"
                ++ (if ind >= 2 then ", KEPT" else ""))

itRun :: Int -> Int -> Double -> IO ()
itRun s st budget = loop (0 :: Int) (0 :: Int) mine
  where
    mine  = [ (i, c) | (i, c) <- zip [0 ..] itCandidates, i `mod` st == s ]
    total = length mine
    loop done kept [] =
      putStrLn ("DONE: processed " ++ show done ++ "/" ++ show total ++ ", kept " ++ show kept)
    loop done kept ((i, c) : rest) = do
      el <- itSecs
      if el > budget
        then putStrLn ("BUDGET EXHAUSTED: processed " ++ show done ++ "/" ++ show total
                       ++ ", kept " ++ show kept ++ ", next candidate " ++ show i)
        else do
          a <- itSecs
          let ps  = itSearch c
              ind = length (filter containsIndc ps)
          _ <- evaluate ind
          b <- itSecs
          if ind >= 2 then putStr (itReport i c ps) else return ()
          if b - a > 30 then putStrLn ("slow cand " ++ show i ++ ": " ++ show (b - a) ++ " s") else return ()
          if (done + 1) `mod` 25 == 0
            then putStrLn ("progress " ++ show (done + 1) ++ "/" ++ show total ++ " at " ++ show b ++ " s CPU")
            else return ()
          loop (done + 1) (if ind >= 2 then kept + 1 else kept) rest

main :: IO ()
main = do
  hSetBuffering stdout LineBuffering
  args <- getArgs
  t0 <- itSecs
  n <- evaluate (length itCandidates)
  t1 <- itSecs
  putStrLn ("functions available: " ++ show (length itSndEnv))
  putStrLn ("third-search candidates: " ++ show n ++ " (enumerated in " ++ show (t1 - t0) ++ " s CPU)")
  case args of
    ["count"]                -> return ()
    ["sample", k]            -> itSample (read k) n
    ["run", s, st, budget]   -> itRun (read s) (read st) (read budget)
    _                        -> putStrLn "usage: iterate-search count | sample K | run SHARD SHARDS SECONDS"

-- Next iteration of the method, with a chosen set of building blocks.
--
-- Main.hs runs two searches: the first uses only the base types (f0-f2), the
-- second may use f0-f2 as building blocks (f3-f30). This program runs a further
-- search in the same way, but allows only a CHOSEN subset of f3-f30 as building
-- blocks (on top of f0-f2), because with all 31 functions available the number
-- of candidate programs is too large to even enumerate (it did not finish in 30
-- minutes). New functions must use at least one of the chosen ones. The
-- selection rule is Main's rule for the second search (at least 2 lemmas proved
-- by induction).
--
-- KS is a comma separated list of function numbers, e.g. 3,12 for reverse and
-- multiplication (numbers as in Appendix B).
--
-- Usage:
--   iterate-search count KS
--   iterate-search sample K KS                 time K evenly spaced candidates
--   iterate-search run SHARD SHARDS SECONDS KS process candidates i with
--                                              i mod SHARDS == SHARD until the
--                                              CPU time budget is used up
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

data ItCtx = ItCtx
  { icEnv  :: Env
  , icTEnv :: TEnv
  , icRec  :: Rec
  , icNew  :: [Atm]
  }

-- Second-search functions selected by number, with their proofs.
itChosen :: [Int] -> [(((Atm, Term), Type), [Proof])]
itChosen ks = [ x | x@(((nom, _), _), _) <- M.namedSndSel
                  , nom `elem` map (\k -> Var ("f" ++ show k)) ks ]

itCtx :: [Int] -> ItCtx
itCtx ks = ItCtx env tenv rec [ nom | (((nom, _), _), _) <- chosen ]
  where
    chosen = itChosen ks
    env    = M.fstEnv ++ [ (nom, def) | (((nom, def), _), _) <- chosen ]
    tenv   = M.fstTEnv ++ [ (Atm nom, typ) | (((nom, _), typ), _) <- chosen ]
    rec    = addAffirms env M.fstRec (map headProof (concat (snds chosen)))

itDatas :: [DatasH]
itDatas = M.datas

-- The same two base types Main uses for its second search.
itBaseTypes :: [Type]
itBaseTypes = map (TAtm . TCon . fst) [itDatas !! 1, itDatas !! 3]

itCandidates :: ItCtx -> [(Term, Type)]
itCandidates ctx = uni ++ bin
  where
    usesNew e = any (\a -> contiene a e) (icNew ctx)
    ok e = contiene (Var "f") e && usesNew e
    uni = filter (ok . fst)
            [ (f, tipo) | tipo <- armarTip 1 itBaseTypes
                        , f <- enumFun (icRec ctx) "f" tipo itDatas (icTEnv ctx) ]
    bin = filter (\(e, _) -> ok e && twice e)
            [ (f, tipo) | tipo <- armarTip 2 itBaseTypes
                        , f <- enumFun (icRec ctx) "f" tipo itDatas (icTEnv ctx) ]
    twice e = case e of
                Abs _ (Abs y b) -> length (take 2 (filter ((Var y) ==) (termToAtm b))) == 2
                _               -> False

itSearch :: ItCtx -> (Term, Type) -> [Proof]
itSearch ctx (f, t) =
  findlemas ((Var "f", f) : icEnv ctx) ((Atm (Var "f"), t) : icTEnv ctx) itDatas M.paciencia (icRec ctx) (Var "f")

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

itSample :: ItCtx -> [(Term, Type)] -> Int -> Int -> IO ()
itSample ctx cands k n = mapM_ one [0 .. k - 1]
  where
    step = max 1 (n `div` k)
    one j = do
      let i = min (n - 1) (j * step)
      a <- itSecs
      let ps  = itSearch ctx (cands !! i)
          ind = length (filter containsIndc ps)
      _ <- evaluate ind
      b <- itSecs
      putStrLn ("sample cand " ++ show i ++ ": " ++ show (b - a) ++ " s, "
                ++ show (length ps) ++ " lemmas, " ++ show ind ++ " by induction"
                ++ (if ind >= 2 then ", KEPT" else ""))

itRun :: ItCtx -> [(Term, Type)] -> Int -> Int -> Double -> IO ()
itRun ctx cands s st budget = loop (0 :: Int) (0 :: Int) mine
  where
    mine  = [ (i, c) | (i, c) <- zip [0 ..] cands, i `mod` st == s ]
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
          let ps  = itSearch ctx c
              ind = length (filter containsIndc ps)
          _ <- evaluate ind
          b <- itSecs
          if ind >= 2 then putStr (itReport i c ps) else return ()
          if b - a > 30 then putStrLn ("slow cand " ++ show i ++ ": " ++ show (b - a) ++ " s") else return ()
          if (done + 1) `mod` 25 == 0
            then putStrLn ("progress " ++ show (done + 1) ++ "/" ++ show total ++ " at " ++ show b ++ " s CPU")
            else return ()
          loop (done + 1) (if ind >= 2 then kept + 1 else kept) rest

itParseKs :: String -> [Int]
itParseKs str = map read (words (map (\c -> if c == ',' then ' ' else c) str))

main :: IO ()
main = do
  hSetBuffering stdout LineBuffering
  args <- getArgs
  let ks = itParseKs (last args)
  putStrLn ("building blocks: f0-f2 and " ++ show ks)
  putStrLn "running the second search to obtain f3-f30 ..."
  t0 <- itSecs
  let ctx = itCtx ks
  _ <- evaluate (length (icEnv ctx))
  _ <- evaluate (length (show (map fst (itChosen ks))))
  t1 <- itSecs
  putStrLn ("second search done in " ++ show (t1 - t0) ++ " s CPU; functions available: " ++ show (length (icEnv ctx)))
  let cands = itCandidates ctx
  n <- evaluate (length cands)
  t2 <- itSecs
  putStrLn ("candidates: " ++ show n ++ " (enumerated in " ++ show (t2 - t1) ++ " s CPU)")
  case init args of
    ["count"]                -> return ()
    ["sample", k]            -> itSample ctx cands (read k) n
    ["run", s, st, budget]   -> itRun ctx cands (read s) (read st) (read budget)
    _                        -> putStrLn "usage: iterate-search count KS | sample K KS | run SHARD SHARDS SECONDS KS"

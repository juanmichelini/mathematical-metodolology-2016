# Third round of the search

Not part of the thesis. The method was run one more step with f0-f2 and a chosen subset of the second-search functions as building blocks: **f3 (reverse), f12 (multiplication), f24** (`f24 xs n = n * length xs`). New functions must use at least one of f3, f12, f24. Same selection rule as the second search in `Main.hs` (at least 2 lemmas proved by induction). GHC 9.4.8, three CI runners, about 3 minutes each after the 2-minute second search that has to be recomputed.

- 344 candidate functions, all processed (115 + 115 + 114).
- 20 kept, in 12 behaviours. Everything below was checked by evaluating the generated definitions on small inputs (`scripts/eval_third_round.py`), not only by reading them.
- Raw output: `shard0.txt`, `shard1.txt`, `shard2.txt`. Parsed: `kept.json`.

`C_,R` is the natural numbers (R.0 = O, R.1 = S) and `C_,a_R` is lists. Numbers refer to candidate index.

| What it computes | Candidates | Notes |
|---|---|---|
| Ruler / Zimin word: `f [x1..xn] = X ++ [x1] ++ X` with `X = f [x2..xn]`, length 2^n - 1. For `[1,2,3]` it gives `[3,2,3,1,3,2,3]` | 313 | Ignores its second argument |
| Doubly exponential: `f n = 2^(2^n)` (2, 4, 16, 256, 65536) | 76, 205 | Ignores its second argument. Lemma: `f (S a) b = f a b * f a b` |
| Iterated squaring plus one: 1, 2, 5, 26, 677, or the same shifted from 0 | 50, 179 and 49, 178 | Ignores its second argument |
| `reverse ys` repeated `length xs` times | 303, 328 | Lemma: `f (a ++ b) g = f b g ++ f a g` |
| Put `reverse ys` before every element of `xs` | 312 | Lemma: `f (a ++ b) g = f a g ++ f b g` |
| Reverse applied n times (or `length xs` times, or one more) | 174, 175, 340, 341 | Equals ys or its reverse by parity. Lemmas: `f (a ++ b) g = f b (f a g)` and `f a (rev b) = rev (f a b)` (340) |
| `n + length xs`, `length xs + length ys` | 103, 104, 244 | 104 has a redundant `reverse` inside |
| Zero except at the empty list / 0 | 83, 215, 218 | Trivial. Not a factorial: I misread this one at first |

## Caveats

- The selection rule does not reject functions that ignore an argument (the Zimin word, the squaring sequences). Their "lemmas" such as `f a (f3 b) = f a b` are then trivially true. A rule rejecting those would be a small change and would remove most of the dull results, but also the Zimin word.
- Several kept functions are the same function with a redundant `reverse` inside, or with a list standing in for its length. The thesis notes the same for the first two rounds.
- Which functions are building blocks was chosen by hand. With all 31 functions the candidate enumeration alone did not finish in 30 minutes. With 7 blocks (f3, f5, f7, f12, f24, f25, f27) there are 7,165 candidates, about 20 times as many as with 3 blocks (344), at roughly 4 s each.

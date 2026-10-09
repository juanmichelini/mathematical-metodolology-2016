# Foundations for Mathematical Methodology

Let this sink in: some mathematical methods can be treated as mathematical objects.
We show this by formalizing a mathematical method for exploring lambda calculus.

First note that we can enumerate all data types, all functions, and all conjectures among those functions.
Also note that we can do the same for all proofs of those conjectures shorter than some length.

Of course, we are not interested in all the data types, nor all the proofs. We are interested only in a subspace of those.

We provide a method that can explore both of those spaces in a way that results in human readable calculational proofs regarding simple typed lambda calculus' functions.

The strongest result so far is that it finds the reverse::[a] -> [a] function, and then shows that reverse(reverse xs) = xs. This requires that it first discovers the lemma reverse(xs ++ ys) = (reverse ys) ++ (reverse xs), which it does.

The method is presented to be followed by humans in the pdf document: Foundations.
Under the folder `code` we present the same method as Haskell code. Running the Main, it will output the latex code that includes all functions in the document.

## Reproducing the thesis results

Everything below was run in CI (see `.github/workflows/reproduce.yml`); the outputs of that run are committed in `results/`.

### Build

Needs GHC and cabal. The code builds with GHC 8.0.2, 8.10.7, 9.4.8 and 9.8.4 (all tested in CI); the numbers below are from 9.4.8.

```
cabal build all
```

The code has no dependencies beyond `base` and `containers`. Modules that are not used by the thesis results are in `code/legacy/` (see the README there) and are not built.

### Run

| What | Command | Reproduces |
|---|---|---|
| Appendix B (all 31 functions and their proofs) | `cabal run -v0 main > results/appendixB.tex` | thesis Sec. 10 and Appendix B |
| Compare it with the thesis PDF | `python3 scripts/compare_appendixB.py results/appendixB.tex Foundations.pdf` (needs `pdftotext`) | check of Appendix B |
| Lemma-proving suite | `cabal run -v0 check-lemmas` | the 35 lemmas in `Test.hs` (exit status 1 if any is unproved) |
| Search sizes, timings, exponentiation lemmas | `cabal run -v0 experiments` | thesis Sec. 10 (flipexp) |

`Main` prints the body of a LaTeX document: a "First Search" section (f0-f2) and a "Second Search" section (f3-f30).

### What was found

All of the following were checked against the thesis from a CI run (GHC 9.4.8):

- **Appendix B matches.** All 31 functions f0-f30 are found, in the same order. For every one of them the definition, the type, every lemma statement proved by the program, and the number of finished proofs agree with Appendix B of `Foundations.pdf` (`results/appendixB_comparison.md`).
- **Reverse.** `f3` is reverse. The program proves `f3 Nil = Nil`, `f3 (f2 a b) = f2 (f3 b) (f3 a)` (reverse of a concatenation) and `f3 (f3 a) = a` (reverse is its own inverse), where `f2` is list concatenation.
- **Exponentiation.** The search for `flipexp x y = y^x` in `Test.hs` finds both lemmas of Sec. 10, `c^(a+b) = c^a * c^b` and `c^(a*b) = (c^b)^a`, with a proof of the second that follows the same steps as the thesis (`results/experiments.txt`).
- **Lemma suite.** All 35 lemmas in `Test.lemas` are proved (`results/check_lemmas.txt`).
- **Determinism.** Two runs of `Main` produce byte-identical output.

### Cost

On a single core of a GitHub Actions runner (ubuntu-latest):

| Run | Time | Memory |
|---|---|---|
| `Main` (both searches) | 82 s | 11 MB |
| First search alone (64 candidates, 3 kept) | 0.2 s CPU | |
| Second search alone (164 candidates, 28 kept) | 111 s CPU | |
| flipexp search in `Test.hs` | 2.5 s CPU | |
| 35-lemma suite | 0.05 s | 10 MB |

The search limit `paciencia` is 30 in `Main.hs`. For the first search, a limit of 5 finds nothing, 10 finds f0-f2 but with fewer lemmas each (4, 4, 4 instead of 7, 7, 4), and 20, 30 and 40 give identical results. The second search was only run with 30.

### Not checked

- The thesis marks some functions as equal to earlier ones (for example `f11 = f7`). The program generates them as separate functions; that they are extensionally equal was not checked here.
- The comparison script compares text after removing layout (whitespace, underscores). It does not compare the proofs line by line; it checks the lemma statements and the number of finished proofs.
- The repo has only the PDF, not the thesis LaTeX source, so Appendix B cannot be rebuilt into the PDF from this output.

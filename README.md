# Foundations for Mathematical Methodology

Let this sink in: some mathematical methods can be treated as mathematical objects.
We show this by formalizing a mathematical method for exploring lambda calculus.

First note that we can ennumerate all data types, all functions, and all conjetures among those functions.
Also note that we can do the same for all proofs of those conjectures shorter than some length.

Of course, we are not interested in all the data types, nor all the proofs. We are interested only in a subspace of those.

We provide a method that can explore both of those spaces in a way that results in human readable calculational proofs regarding simple typed lambda calculus' functions.

The strongest result so far is that it finds the reverse::[a] -> [a] function, and then shows that reverse(reverse xs) = xs. This requires that it first discovers the lemma reverse(xs ++ ys) = (reverse ys) ++ (reverse xs), which it does.

The method is presented to be followed by humands in the pdf document: Foundations.
Under te folder code we present the same method as Haskell code.




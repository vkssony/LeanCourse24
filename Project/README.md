Vivek Sasse and Robin Pfeiffer
Project topic: Constructible Polygons

# Introduction

This Lean formalization project attempts to prove the Gauss-Wantzel Theorem, which states that a regular n-gon can be constructed via compass and straightedge if and only if n equals the product of a power of 2 and distinct Fermat primes.

# Main Results

The main results of our project are as follows:

Robin.lean:
- **Fermat primes**: definition of Fermat primes. Mathlib does already have a definition of Fermat numbers, but it is very new and not included in the version of Mathlib used in the repository
- **phi_pow_two_iff**: for natural numbers n, totient of n is a power of 2 if and only if it factors as in the Gauss-Wantzel theorem above. This is the main lemma about Fermat primes that we needed for our proof of the Gauss-Wantzel theorem
-

Polygon.lean:
- **ord_pow_two_tower** : For a group G with |G| = 2^n, there exists a tower of subgroups 1 = G_n \subset \cdots \subset G_1 \subset G_0 = G such that G_{i+1} is normal in G_i and \[G_i:G_{i+1}\]=2. Although this is a very technically lemma, it was surprisingly hard to prove. It is usually proved quickly using properties of solvable groups, but those are implimented using derived series instead, which makes things difficult
- **algebraic_constructable_iff** : this result shows that an algebraic number is constructible if and only if the degree of its splitting field (over the rationals) is a power of 2. This is the main result of this file, which corresponds to Theorem 10.1.12 from Cox's book (see below). Result mainly relies on the criterion for constructibility proved by Ludwig in his code about a tower of quadratic extensions.

Polygon_work.lean:
- **gauss_wantzel**: the Gauss-Wantzel theorem


Other interesting side lemmas that might be useful elsewhere:
- **smallest_prime_index**: If H is a subgroup of G and \[G:H\] is the smallest prime that divides |G|, then H is normal : originally, we wanted to prove that index 2 subgroups are normal, but this generalization ended up being easier to prove as it did not require working with cosets directly. This lemma could be added to Mathlib in the future.


# Sorry's




# References

The main reference we used was *Galois Theory* by David A. Cox, specifically Chapter 10.

Our work of course would in no way been possible without the Ludwig's lean project that did the heavy lifting of formalizing construcible numbers in Lean, found [here](https://github.com/Louis-Le-Grand/Formalisation-of-constructable-numbers/tree/main)

For `smallest_prime_index`, we used [this Math Stack Exchange post](https://math.stackexchange.com/questions/164244/normal-subgroup-of-prime-index/). We could not find a textbook source for this proof, and some commenters elsewhere have said it is a folklore theorem/proof.

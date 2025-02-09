Vivek Sasse and Robin Pfeiffer
Project topic: Constructible Polygons

# Introduction

This Lean formalization project attempts to prove the Gauss-Wantzel Theorem, which states that a regular n-gon can be constructed via compass and straightedge if and only if n equals the product of a power of 2 and distinct Fermat primes.

# Main Results

The main results of our project are as follows:

NumberTheory.lean (Robin's work):
- **Fermat primes**: definition of Fermat primes. Mathlib does already have a definition of Fermat numbers, but it is very new and not included in the version of Mathlib used in the repository.
- **phi_pow_two_iff**: for natural numbers n, totient of n is a power of 2 if and only if it factors as in the Gauss-Wantzel theorem above. This is the main lemma about Fermat primes that we needed for our proof of the Gauss-Wantzel theorem.
-

Constructability.lean (Vivek's Work):
- **ord_pow_two_tower** : For a group G with |G| = 2^n, there exists a tower of subgroups 1 = G_n \subset \cdots \subset G_1 \subset G_0 = G such that G_{i+1} is normal in G_i and \[G_i:G_{i+1}\]=2. Although this is a very technically lemma, it was surprisingly hard to prove. It is usually proved quickly using properties of solvable groups, but those are implimented using derived series instead, which makes things difficult.
- **algebraic_constructable_iff** : this result shows that an algebraic number is constructible if and only if the degree of its splitting field (over the rationals) is a power of 2. This is the main result of this file, which corresponds to Theorem 10.1.12 from Cox's book (see below). Result mainly relies on the criterion for constructibility proved by Ludwig in his code about a tower of quadratic extensions.

Polygon_work.lean (Vivek's work):
- **gauss_wantzel**: the Gauss-Wantzel theorem


Other interesting side lemmas that might be useful elsewhere:
- **smallest_prime_index**: If H is a subgroup of G and \[G:H\] is the smallest prime that divides |G|, then H is normal : originally, we wanted to prove that index 2 subgroups are normal, but this generalization ended up being easier to prove as it did not require working with cosets directly. This lemma could be added to Mathlib in the future.


# Sorry's

NumberTheory.lean:
- **Nat.pow_of_pow_add_prime** : This is a result that exists in a newer version of Matlib, and so we have included it with a sorry.
- **product_of_prime_factors** : This is a very standard result which we expected to be in Matlib. However we could not find it and have ran out of time to prove it.
- **pow_log** : Similarly to the previous lemma, we expected to find it in Matlib, and were not able to complete it in time.
- **totient_prod** : This is a lemma that exists in Matlib in the case where you are multiplying two coprime numbers (Nat.totient_mul). This lemma generalises that to multiplying over a set of pairwise coprime numbers.
All four of these lemmas can be seen at the very top of NumberTheory.lean

For these two, more details behind the sorries are in comments in the files themselves, as they make more sense in context

Constructability.lean:
- **fixedField_bot**,  **fixedField_top** - lemmas from Mathlib that required too many auxiliaries to be able to copy in what whas needed without updating Mathlib. Included with sorries as needed later
- **algebraic_constructable_iff** - most incomplete theorem.
  - The mpr of the iff is nearly complete, with only the last step of using the Galois correspondence to get from a tower of index 2 subgroups to get a tower of quadradic extensions
  - The forward direction has a lot of `sorry`'s due to type casting issues. Most of the work was getting all the types correct using lifts, equivalences, restriction and extension of scalars, etc., rather than the actual content of the theorem.
  - additionally, proving that the tower of fields obtain after applying the automorphism satisfies the conditions of `Classfication_z_in_M_inf` was not completed due to time

Gauss-Wantzel.lean:
- only two `sorry`'s
- both due to fields being equivalent as sets but not definitionally equivalent

Overall, for both of these files, the main stumbling block was getting all the types to work correctly as we working with more than a half dozen different fields at once, either as fields, subfields, or  intermediatefields.


# References

The main reference we used was *Galois Theory* by David A. Cox, specifically Chapter 10.

Our work of course would in no way been possible without the Ludwig's lean project that did the heavy lifting of formalizing construcible numbers in Lean, found [here](https://github.com/Louis-Le-Grand/Formalisation-of-constructable-numbers/tree/main)

For `smallest_prime_index`, we used [this Math Stack Exchange post](https://math.stackexchange.com/questions/164244/normal-subgroup-of-prime-index/). We could not find a textbook source for this proof, and some commenters elsewhere have said it is a folklore theorem/proof.

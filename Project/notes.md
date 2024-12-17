Main claims:

1. $\vaprhi(n) = 2^m \iff n=2^sp_1\cdots p_r$ where $s\in \Z_{\geq 0}$ and $p_i$ are Fermat primes
   1. if $n=\bigprod q_i^{a_i}$, $\varphi(n)= \bigprod q_i^{a_i-1} \cdot (q_i-1)$ [Matlib](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Data/Nat/Totient.html#Nat.totient_eq_prod_factorization)
   2. $q$ odd prime $q=2^k+1$ implies $k=2^n$
2. $\zeta_n$ constructible is equivalent to $[\Q(\zeta_n):\Q]=2^n$
   1. $\alpha\in \C$ algebraic over $\Q$, $L$ splitting field of min poly of $\alpha$, then $\alpha \in M_\infty \iff [L:\Q]=2^n$
   2. $\Q(\zeta_n)/\Q$ Galois
      1. Note: implies in situation above $\alpha=\zeta_n$ then $L=\Q(\zeta_n)$?
      2. $\zeta_n$ algebraic over $\Q$
      3. $|Gal(L/\Q)|=[L:\Q]$
      4. $G$ group, $|G|=p^n$ implies $G$ solvable
      5. $G$ solvable, $|G|=2^n$ implies composition series of $G$ all index 2
3. $[\Q(\zeta_n):\Q]=\varphi(n)
4.

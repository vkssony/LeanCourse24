import LeanCourse.Common
import Mathlib.Data.Complex.Exponential
-- import Std.Data.BitVec
-- import Mathlib.NumberTheory.Fermat

def FermatPrime (n : ℕ) : Prop :=
  Nat.Prime n ∧ (∃ k : ℕ, n = 2 ^ (2 ^ k) + 1)

def ProductOfDistinctFermatPrimes (n : ℕ) : Prop :=
  ∀ p ∈ n.primeFactors, (FermatPrime p ∧ ¬ (p ^ 2 ∣ n))
  -- ∃ k : ℕ, ∃ j : ℕ → ℕ, (n = ∏ i ∈ Finset.range k, j i) ∧ (∀ i ∈ Finset.range k, FermatPrime (j i)) ∧ (∀ p q : Finset.range k, p ≠ q → j p ≠ j q)

def ProductOfDistinctFermatPrimes' (n : ℕ) : Prop :=
  ∀ p ∈ n.primeFactors, FermatPrime p ∧ n.factorization p = 1



#eval (12 : ℕ).primeFactors



#check FermatPrime 3
#eval Finset.range 5

#check Nat.primeFactors

#check pow_ne_zero

#leansearch "a b : ℕ, a ^ b ≠ 0?"

-- lemma prime_factors_of_n {n : ℕ} : (∃ s k : ℕ, ∃ j : ℕ → ℕ, (n = 2 ^ s * ∏ i ∈ Finset.range k, j i) ∧ (∀ i ∈ Finset.range k, FermatPrime (j i)) ∧ (∀ p q : Finset.range k, p ≠ q → j p ≠ j q)) → n.primeFactors = {}






lemma phi_pow_two_iff {n : ℕ} : (∃ m : ℕ, Nat.totient n = 2 ^ m) ↔ (∃ s p : ℕ, n = 2^s * p ∧ ProductOfDistinctFermatPrimes p) := by {
  constructor
  · intro h
    obtain ⟨m, hm⟩ := h
    have hn0 : n ≠ 0 := by {
      intro h
      rw [h] at hm
      simp at hm
      apply pow_ne_zero m (Ne.symm (Nat.zero_ne_add_one 1))
      exact id (Eq.symm hm)
    }
    by_cases h1 : m = 0
    . simp [h1] at hm
      have h2 : n = 1 ∨ n = 2 := by exact Nat.totient_eq_one_iff.mp hm
      have hfermat : ProductOfDistinctFermatPrimes 1 := by {
          unfold ProductOfDistinctFermatPrimes
          simp
        }
      obtain h3|h4 := h2
      · use 0
        use 1
        exact ⟨h3, hfermat⟩
      · use 1
        use 1
        exact ⟨h4, hfermat⟩
    · rw [Nat.totient_eq_div_primeFactors_mul] at hm
      unfold ProductOfDistinctFermatPrimes

      have hn : (2^m).primeFactors = {2} := by {
        refine Nat.primeFactors_prime_pow h1 ?hp
        exact Nat.prime_two
      }
      let p1 := ∏ p ∈ n.primeFactors, p
      let p2 := ∏ p ∈ n.primeFactors, (p - 1)
      have hhh :  (∏ p ∈ n.primeFactors, p) / ∏ p ∈ n.primeFactors, (p - 1) = ∏ p ∈ n.primeFactors, p / (p - 1) := by {
        sorry

      }
      #leansearch "∏ x ∈ A, f x / ∏ x ∈ A, g x = ∏ x ∈ A, f x / g x?"
      #check Finset.prod_div_distrib

      have hm : n = 2^m * ∏ p ∈ n.primeFactors, p / (p - 1) := by {
        sorry
      }
      use m
      use ∏ p ∈ n.primeFactors, p / (p - 1)
      constructor
      · exact hm
      · intro p hp
        sorry

      -- sorry

      -- #check Int.mul_ediv_cancel


    -- · rw [h1] at hm
    --   simp at hm
    --   obtain ⟨hm1, hm2⟩ := hm

    --
    -- sorry
  · intro h
    obtain ⟨s, p, h1, h2⟩ := h
    unfold ProductOfDistinctFermatPrimes at h2
    unfold FermatPrime at h2

}


#check 3.factorization.prod

#eval Nat.primeFactors (55^11)

#check Nat.totient_mul_prod_primeFactors
#check Nat.pow_of_pow_add_prime
#check Nat.totient_eq_prod_factorization
#check Nat.totient_eq_div_primeFactors_mul

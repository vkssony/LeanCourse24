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


def fermat_power (n : ℕ) (hn : FermatPrime n): Prop := {
  hn.2
}


def test (n : ℕ) (hn : FermatPrime n) : ℕ :=
  match hn.2 with
  | ⟨k, _⟩ => k


def FermatPower (p : ℕ) (hp : FermatPrime p) : ℕ × Prop :=
  match hp.2 with
  | ⟨k, hk⟩ => (k, hk)


#check FermatPrime 3
#eval Finset.range 5

#check Nat.primeFactors

#check pow_ne_zero

#leansearch "a b : ℕ, a ^ b ≠ 0?"

-- lemma prime_factors_of_n {n : ℕ} : (∃ s k : ℕ, ∃ j : ℕ → ℕ, (n = 2 ^ s * ∏ i ∈ Finset.range k, j i) ∧ (∀ i ∈ Finset.range k, FermatPrime (j i)) ∧ (∀ p q : Finset.range k, p ≠ q → j p ≠ j q)) → n.primeFactors = {}




lemma phi_pow_two_iff {n : ℕ} : (∃ m : ℕ, Nat.totient n = 2 ^ m) ↔ (∃ s p : ℕ, n = 2^s * p ∧ ProductOfDistinctFermatPrimes' p) := by {
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
      have hfermat : ProductOfDistinctFermatPrimes' 1 := by {
          unfold ProductOfDistinctFermatPrimes'
          simp
        }
      obtain h3|h4 := h2
      · use 0
        use 1
        exact ⟨h3, hfermat⟩
      · use 1
        use 1
        exact ⟨h4, hfermat⟩
    · rw [Nat.totient_eq_prod_factorization] at hm
      unfold Finsupp.prod at hm
      rw [Nat.support_factorization] at hm

      have simplyfunc : ∏ a ∈ n.primeFactors, (fun p k => p ^ (k - 1) * (p - 1)) a (n.factorization a) = ∏ p ∈ n.primeFactors, p ^ (n.factorization p - 1) * (p - 1) := by {
        exact rfl
      }

      rw [simplyfunc] at hm

      have hp : ∀ p ∈ n.primeFactors, (∃ k : ℕ, (p ^ (n.factorization p - 1) * (p - 1) = 2 ^ k)):= by {
        intro p hp

      }

      unfold ProductOfDistinctFermatPrimes'

      have hp2 : ∃ s : ℕ, n.factorization 2 = s := by {
        simp
      }

      obtain ⟨s, hs⟩ := hp2
      use s
      have hp3 : ∃ p : ℕ, n / (2 ^ s) = p := by {
        simp
      }
      obtain ⟨p, hp3⟩ := hp3
      use p
      constructor
      · rw [←hp3]
        group
        sorry
      · have hp2 : p.factorization 2 = 0 := by {
          rw [←hp3, ←hs]
          calc (n / 2 ^ n.factorization 2).factorization 2 = n.factorization 2 - (2 ^ n.factorization 2).factorization 2 := by sorry
                                                         _ = n.factorization 2 - n.factorization 2 := by sorry
                                                         _ = 0 := by simp
        }
        intro p1 hp1
        specialize hp p1 hp1
        sorry


      exact hn0


  · intro hn
    obtain ⟨s, p, hn⟩ := hn
    obtain ⟨hn1, hn2⟩ := hn
    unfold ProductOfDistinctFermatPrimes' at hn2

    have hp : ∀ p_1 ∈ p.primeFactors, ∃ k, p_1 = 2 ^ (2 ^ k) + 1 := by {
      intro p_1 hp1
      specialize hn2 p_1
      apply hn2 at hp1
      obtain ⟨hp, _⟩ := hp1
      unfold FermatPrime at hp
      exact hp.2
    }

}

#leansearch "(∏ x ∈ A, f x).primeFactors = (f x).primeFactors?"




#check 3.factorization.prod

#eval Nat.primeFactors (55^11)

#check Nat.totient_mul_prod_primeFactors
#check Nat.pow_of_pow_add_prime
#check Nat.totient_eq_prod_factorization
#check Nat.totient_eq_div_primeFactors_mul

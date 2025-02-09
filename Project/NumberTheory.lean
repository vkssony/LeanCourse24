import LeanCourse.Common
import Mathlib.Data.Complex.Exponential


/-
# Section - Sorrys

In this section I list the lemmas that were not completed, and give my reasons for not completeing them
-/

theorem Nat.pow_of_pow_add_prime {a n : ℕ} (ha : 1 < a) (hn : n ≠ 0) (hP : Nat.Prime (a ^ n + 1)) : ∃ (m : ℕ), n = 2 ^ m := by {
  sorry
}

lemma product_of_prime_factors (n : ℕ) : n ≠ 0 → n = ∏ p ∈ n.primeFactors, p ^ (n.factorization p) := by {
  sorry
}

lemma pow_log (a b : ℕ) : 1 < a → 0 < b → (∃ k, a ^ k = b) → a ^ Nat.log a b = b := by {
  sorry
}

lemma totient_prod (A : Finset ℕ) : (∀ x ∈ A, ∀ y ∈ A, x ≠ y → x.Coprime y) → (∏ p ∈ A, p).totient = ∏ p ∈ A, (p).totient := by {
  sorry
}

/-# Section 2 - Fermat Primes
  In this section I define Fermat Primes, and another number I called a product of distinct Fermat Primes.
  These numbers describe exactly what we want our final numbers to look like-/
def FermatPrime (n : ℕ) : Prop :=
  Nat.Prime n ∧ (∃ k : ℕ, n = 2 ^ (2 ^ k) + 1)

def ProductOfDistinctFermatPrimes (n : ℕ) : Prop :=
  (n ≠ 0) ∧ ∀ p ∈ n.primeFactors, FermatPrime p ∧ n.factorization p = 1

/-# Section 3 - Necessary Lemmas
  The following lemmas were made just to use in the big proof at the end-/

lemma nat_sub_one (n : ℕ) : (n ≠ 0 ∧ n ≠ 1) → n - 1 ≠ 0 := by {
  intro h
  refine Nat.sub_ne_zero_of_lt ?_
  exact Nat.one_lt_iff_ne_zero_and_ne_one.mpr h
}

lemma hpowertwo (m : ℕ): 2 ^ m = 1 → m = 0 := by {
  intro hm
  by_contra hm2
  have hm2 : m ≠ 0 := by exact hm2
  rw [←Nat.one_lt_two_pow_iff] at hm2
  linarith
}

lemma nat_sub_plus_one (n : ℕ) : (¬ n = 0) → n = n - 1 + 1 := by exact fun a => Eq.symm (Nat.succ_pred_eq_of_ne_zero a)



lemma totient_of_fermat_prime (p : ℕ) : (ProductOfDistinctFermatPrimes p) → p.totient = 2 ^ (∑ p_1 ∈ p.primeFactors, Nat.log 2 (p_1 - 1)) := by {
  intro hp
  unfold ProductOfDistinctFermatPrimes at hp
  rw [product_of_prime_factors p hp.1]
  have hp1 : ∏ p_1 ∈ p.primeFactors, p_1 ^ p.factorization p_1 = ∏ p_1 ∈ p.primeFactors, p_1 := by {
    apply Finset.prod_congr
    · exact rfl
    · intro p_1 hp_1
      rw [(hp.2 p_1 hp_1).2]
      simp
  }
  rw [hp1]

  have hcoprime : (∀ x ∈ p.primeFactors, ∀ y ∈ p.primeFactors, x ≠ y → x.Coprime y) := by {
    intro x hx y hy hxy
    rw [Nat.coprime_primes]
    exact hxy
    exact Nat.prime_of_mem_primeFactors hx
    exact Nat.prime_of_mem_primeFactors hy
  }
  rw [totient_prod p.primeFactors hcoprime]

  have htotient2 : ∏ p ∈ p.primeFactors, p.totient = ∏ p ∈ p.primeFactors, (p - 1) := by {
    apply Finset.prod_congr
    · exact rfl
    · intro p_1 hp_1
      exact Nat.totient_prime (Nat.prime_of_mem_primeFactors hp_1)
  }
  have hpower : ∀ p_1 ∈ p.primeFactors, p_1 - 1 = 2 ^ Nat.log 2 (p_1 - 1) := by {
    intro p_1 hp_1
    have hb : 1 < 2 := by linarith

    have hb2 : p_1 - 1 > 0 := by {
      by_contra hb2
      simp at hb2
      rw [Nat.le_one_iff_eq_zero_or_eq_one] at hb2
      have htemp : p_1 ≠ 0 ∧ p_1 ≠ 1 := by {
        constructor
        · exact Nat.Prime.ne_zero (Nat.prime_of_mem_primeFactors hp_1)
        · exact Nat.Prime.ne_one (Nat.prime_of_mem_primeFactors hp_1)
      }
      tauto
    }

    have hb3 : ∃ k, 2 ^ k = p_1 - 1 := by {
      have htemp : FermatPrime p_1 := by exact ((hp.2) p_1 hp_1).1
      unfold FermatPrime at htemp
      obtain ⟨k, hk⟩ := htemp.2
      use 2 ^ k
      rw [hk]
      simp
    }

    exact Eq.symm (pow_log 2 (p_1 - 1) hb hb2 hb3)
  }
  have hpower2 : ∀ p_1 ∈ p.primeFactors, p_1.totient = 2 ^ Nat.log 2 (p_1 - 1) := by {
    intro p_1 hp_1
    rw [Nat.totient_prime (Nat.prime_of_mem_primeFactors hp_1)]
    exact hpower p_1 hp_1
  }
  have hpower3 : ∏ p_1 ∈ p.primeFactors, p_1.totient = ∏ p_1 ∈ p.primeFactors, 2 ^ Nat.log 2 (p_1 - 1) := by {
    apply Finset.prod_congr
    · exact rfl
    · exact hpower2
  }
  rw [hpower3]
  rw [Finset.prod_pow_eq_pow_sum]
  have hprimefactors : (∏ p_1 ∈ p.primeFactors, p_1).primeFactors = p.primeFactors := by {
    have hprime : ∀ p_1 ∈ p.primeFactors, Nat.Prime p_1 := by exact fun p_1 a ↦ Nat.prime_of_mem_primeFactors a
    apply Nat.primeFactors_prod at hprime
    exact hprime
  }
  exact
    congrArg (HPow.hPow 2)
      (congrFun (congrArg Finset.sum (id (Eq.symm hprimefactors))) fun i ↦ Nat.log 2 (i - 1))


}

/-# Section 4 - Main Result-/

lemma phi_pow_two_iff {n : ℕ} : (∃ m : ℕ, Nat.totient n = 2 ^ m) ↔ (∃ s p : ℕ, n = 2^s * p ∧ ProductOfDistinctFermatPrimes p) := by {
  constructor
  · -- First Direction of if and only if
    -- The plan for this direction is to obtain n = 2 ^ s * p
    -- And then to show that the s and p satisfy the requirements in the lemma
    intro h
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
    · rw [Nat.totient_eq_prod_factorization] at hm
      unfold Finsupp.prod at hm
      rw [Nat.support_factorization] at hm

      have simplyfunc : ∏ a ∈ n.primeFactors, (fun p k => p ^ (k - 1) * (p - 1)) a (n.factorization a) = ∏ p ∈ n.primeFactors, p ^ (n.factorization p - 1) * (p - 1) := by {
        exact rfl
      }

      have hnot1 : n ≠ 1 := by {
        intro h
        rw [h] at hm
        simp at hm
        have hhhh : 2 ^ m > 1 := by {
          exact Nat.one_lt_two_pow_iff.2 h1
        }
        linarith
      }

      rw [simplyfunc] at hm

      have hp : ∀ p ∈ n.primeFactors, (∃ k : ℕ, (p ^ (n.factorization p - 1) * (p - 1) = 2 ^ k)):= by {
        intro p₀ hp₀
        have hprod : ∏ p ∈ n.primeFactors, p ^ (n.factorization p - 1) * (p - 1) = (∏ p ∈ (n.primeFactors \ {p₀}), p ^ (n.factorization p - 1) * (p - 1)) * (p₀ ^ (n.factorization p₀ - 1) * (p₀ - 1)) := by {
          exact
            Finset.prod_eq_prod_diff_singleton_mul hp₀ fun x =>
              x ^ (n.factorization x - 1) * (x - 1)
        }
        have hnonzero1 : (∏ p ∈ (n.primeFactors \ {p₀}), p ^ (n.factorization p - 1) * (p - 1)) ≠ 0 := by {
          apply Finset.prod_ne_zero_iff.mpr
          intro p1 hp1
          refine Nat.mul_ne_zero_iff.mpr ?_
          have hprime : p1 ∈ n.primeFactors := by {
            have hsubset : n.primeFactors \ {p₀} ⊆ n.primeFactors := by {
              exact Finset.sdiff_subset
            }
            exact hsubset hp1
          }
          apply Nat.prime_of_mem_primeFactors at hprime
          constructor
          · refine pow_ne_zero (n.factorization p1 - 1) ?left.h
            exact Nat.Prime.ne_zero hprime
          · have this : (p1 ≠ 0 ∧ p1 ≠ 1) := by {
              constructor
              · exact Nat.Prime.ne_zero hprime
              · exact Nat.Prime.ne_one hprime
            }
            exact nat_sub_one p1 this

        }
        have hnonzero2 : p₀ ^ (n.factorization p₀ - 1) * (p₀ - 1) ≠ 0 := by {
          refine Nat.mul_ne_zero_iff.mpr ?_
          constructor
          · apply Nat.prime_of_mem_primeFactors at hp₀
            refine pow_ne_zero (n.factorization p₀ - 1) (Nat.Prime.ne_zero hp₀)
          · apply Nat.prime_of_mem_primeFactors at hp₀
            simp at *
            have hnot01 : p₀ ≠ 0 ∧ p₀ ≠ 1 := by {
              constructor
              · exact Nat.Prime.ne_zero hp₀
              · exact Nat.Prime.ne_one hp₀
            }
            exact nat_sub_one p₀ hnot01

        }
        have hfact : (p₀ ^ (n.factorization p₀ - 1) * (p₀ - 1)).primeFactors ⊆ (∏ p ∈ n.primeFactors, p ^ (n.factorization p - 1) * (p - 1)).primeFactors := by {
          have hh : ∏ p ∈ n.primeFactors, p ^ (n.factorization p - 1) * (p - 1) = (∏ p ∈ n.primeFactors \ {p₀}, p ^ (n.factorization p - 1) * (p - 1)) * (p₀ ^ (n.factorization p₀ - 1) * (p₀ - 1)) := by {
            exact hprod
          }
          rw [hh]
          have hh2 : ((∏ p ∈ n.primeFactors \ {p₀}, p ^ (n.factorization p - 1) * (p - 1)) * (p₀ ^ (n.factorization p₀ - 1) * (p₀ - 1))).primeFactors = (∏ p ∈ n.primeFactors \ {p₀}, p ^ (n.factorization p - 1) * (p - 1)).primeFactors ∪ (p₀ ^ (n.factorization p₀ - 1) * (p₀ - 1)).primeFactors := by exact Nat.primeFactors_mul hnonzero1 hnonzero2
          rw [hh2]
          exact Finset.subset_union_right
        }

        have hprimefactors : (∏ p ∈ n.primeFactors, p ^ (n.factorization p - 1) * (p - 1)).primeFactors = {2} := by {
          rw [hm]
          apply Nat.primeFactors_prime_pow h1 Nat.prime_two
        }

        have hprimefactors3 : (p₀ ^ (n.factorization p₀ - 1) * (p₀ - 1)).primeFactors ⊆ {2} := by {
          rw [←hprimefactors]
          exact hfact
        }
        have hprimefactors2 : (p₀ ^ (n.factorization p₀ - 1) * (p₀ - 1)).primeFactors = {2} ∨ (p₀ ^ (n.factorization p₀ - 1) * (p₀ - 1)).primeFactors = ∅ := by {
          have htemp : ¬ (p₀ ^ (n.factorization p₀ - 1) * (p₀ - 1)).primeFactors = ∅ → (p₀ ^ (n.factorization p₀ - 1) * (p₀ - 1)).primeFactors = {2} := by {
            intro htemp
            have hnonempty : ((p₀ ^ (n.factorization p₀ - 1) * (p₀ - 1)).primeFactors).Nonempty := by exact Finset.nonempty_iff_ne_empty.mpr htemp
            exact (Finset.Nonempty.subset_singleton_iff hnonempty).mp hprimefactors3
          }
          tauto
        }

        obtain h1 | h2 := hprimefactors2
        · use (p₀ ^ (n.factorization p₀ - 1) * (p₀ - 1)).factorization 2
          calc p₀ ^ (n.factorization p₀ - 1) * (p₀ - 1) = ∏ p ∈ (p₀ ^ (n.factorization p₀ - 1) * (p₀ - 1)).primeFactors, p ^ ((p₀ ^ (n.factorization p₀ - 1) * (p₀ - 1)).factorization p) := by {
            exact product_of_prime_factors (p₀ ^ (n.factorization p₀ - 1) * (p₀ - 1)) hnonzero2
          }
                                                      _ = ∏ p ∈ {2}, p ^ ((p₀ ^ (n.factorization p₀ - 1) * (p₀ - 1)).factorization p) := by rw [h1]
                                                      _ = 2 ^ ((p₀ ^ (n.factorization p₀ - 1) * (p₀ - 1)).factorization 2) := by simp
        · have h1 : p₀ ^ (n.factorization p₀ - 1) * (p₀ - 1) = 1 := by {
            rw [Nat.primeFactors_eq_empty] at h2
            have h11 : ¬ p₀ ^ (n.factorization p₀ - 1) * (p₀ - 1) = 0 := by {
              by_contra h11
              rw [Nat.mul_eq_zero] at h11
              obtain h111 | h112 := h11
              · simp at h111
                have h1111 : p₀ ≠ 0 := by exact Nat.Prime.ne_zero (Nat.prime_of_mem_primeFactors hp₀)
                exact h1111 h111.1
              · have h1111 : p₀ ≠ 0 ∧ p₀ ≠ 1 := by {
                  constructor
                  · exact Nat.Prime.ne_zero (Nat.prime_of_mem_primeFactors hp₀)
                  · exact Nat.Prime.ne_one (Nat.prime_of_mem_primeFactors hp₀)
                }
                exact nat_sub_one p₀ h1111 h112
            }
            tauto
          }
          rw [h1]
          use 0
          simp


      }

      unfold ProductOfDistinctFermatPrimes

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
        have hfact : (2 ^ s) ∣ n := by {
          refine (Nat.Prime.pow_dvd_iff_dvd_ord_proj ?pp hn0).mpr ?_
          · exact Nat.prime_two
          · rw [hs]
        }
        exact Eq.symm (Nat.div_mul_cancel hfact)
      · have hfact : (2 ^ s) ∣ n := by {
            refine (Nat.Prime.pow_dvd_iff_dvd_ord_proj ?pp hn0).mpr ?_
            rw [hs]
          }
        have hp2 : p.factorization 2 = 0 := by {
          rw [←hp3, ←hs]
          have hfact : (2 ^ (n.factorization 2)) ∣ n := by exact Nat.ord_proj_dvd n 2
          calc (n / 2 ^ n.factorization 2).factorization 2 = (n.factorization - (2 ^ n.factorization 2).factorization) 2 := by rw [Nat.factorization_div hfact]
                                                         _ = n.factorization 2 - (2 ^ n.factorization 2).factorization 2 := by exact rfl
                                                         _ = n.factorization 2 - (n.factorization 2) • ((2).factorization 2) := by {
                                                          rw [Nat.factorization_pow 2 (n.factorization 2)]
                                                          rfl
                                                         }
                                                         _ = n.factorization 2 - n.factorization 2 := by simp [Nat.Prime.factorization_self Nat.prime_two]
                                                         _ = 0 := by simp
        }
        constructor
        · by_contra hp4
          rw [hp4] at hp3

          have hn00 : n = 0 := by exact Nat.eq_zero_of_dvd_of_div_eq_zero hfact hp3
          exact hn0 hn00

        · intro p_1 hp_1
          have hnps : n = 2 ^ s * p := by exact Nat.eq_mul_of_div_eq_right hfact hp3
          have hpp : p ∣ n := by exact Dvd.intro_left (2 ^ s) (id (Eq.symm hnps))
          have hsubset : p.primeFactors ⊆ n.primeFactors := by exact Nat.primeFactors_mono hpp hn0
          have hp22 : p_1 ∈ n.primeFactors := by exact hsubset hp_1
          specialize hp p_1 hp22
          have h2 : p_1 ≠ 2 := by {
            by_contra h2
            rw [h2] at hp_1
            have htemp : Nat.Prime 2 ∧ 2 ∣ p ∧ p ≠ 0 := by {
              constructor
              · exact Nat.prime_two
              · constructor
                · exact Nat.dvd_of_mem_primeFactors hp_1
                · by_contra hp0
                  have htempp : n = 0 := by {
                    calc n = 2 ^ s * p := by rw [hnps]
                         _ = 2 ^ s * 0 := by rw [hp0]
                         _ = 0 := by simp
                  }
                  exact hn0 htempp
            }
            have htemp2 : ¬Nat.Prime 2 ∨ ¬2 ∣ p ∨ p = 0 := by {
              rw [Nat.factorization_eq_zero_iff p 2] at hp2
              exact hp2
            }
            have htemp3 : ¬ (Nat.Prime 2 ∧ 2 ∣ p ∧ p ≠ 0) := by tauto
            exact htemp3 htemp
          }


          have hfactorization2 : n.factorization p_1 = 1 := by {
            obtain ⟨k, hk⟩ := hp
            by_contra hfactorization
            have htemp : n.factorization p_1 ≠ 0 ∧ n.factorization p_1 ≠ 1 := by {
              constructor
              · exact Finsupp.mem_support_iff.mp (hsubset hp_1)
              · exact hfactorization
            }
            have hfactorization2 : n.factorization p_1 ≥ 2 := by {
              rw [←Nat.two_le_iff (n.factorization p_1)] at htemp
              exact htemp
            }
            have hp_1factor : p_1 ∈ (p_1 ^ (n.factorization p_1 - 1) * (p_1 - 1)).primeFactors := by {
              refine (Nat.mem_primeFactors_of_ne_zero ?hn).mpr ?_
              · rw [hk]
                exact Ne.symm (NeZero.ne' (2 ^ k))
              · constructor
                · exact Nat.prime_of_mem_primeFactors hp_1
                · have htemp : n.factorization p_1 - 1 ≥ 1 := by exact Nat.le_sub_one_of_lt hfactorization2
                  have htemp2 : n.factorization p_1 - 1 ≠ 0 := by exact Nat.one_le_iff_ne_zero.1 htemp
                  have htemp1 : p_1 ∣ p_1 ^ (n.factorization p_1 - 1) := by {
                    have htemp11 : p_1 ∣ p_1 := by exact Nat.dvd_refl p_1
                    exact Dvd.dvd.pow htemp11 htemp2
                  }
                  exact Dvd.dvd.mul_right htemp1 (p_1 - 1)
            }
            have hp_1factor2 : p_1 ∉ (2 ^ k).primeFactors := by {
              have hs : k ≠ 0 := by {
                by_contra hs
                rw [hs] at hk
                simp at hk
                have htemp : p_1 = 2 := by {
                  have temp1 : p_1 ≠ 0 := by exact Nat.Prime.ne_zero (Nat.prime_of_mem_primeFactors hp_1)
                  calc p_1 = p_1 - 1 + 1 := by exact nat_sub_plus_one p_1 temp1
                         _ = 1 + 1 := by rw [hk.2]
                         _ = 2 := by simp
                }
                exact h2 htemp
              }
              have htemp : (2 ^ k).primeFactors = {2} := by {
                exact Nat.primeFactors_prime_pow hs Nat.prime_two
              }
              rw [htemp]
              simp
              exact h2
            }
            have hprimeFactors : (2 ^ k).primeFactors = (p_1 ^ (n.factorization p_1 - 1) * (p_1 - 1)).primeFactors := by {
              rw [hk]
            }
            have hprimeFactors2 : (p_1 ^ (n.factorization p_1 - 1) * (p_1 - 1)).primeFactors ≠ (2 ^ k).primeFactors := by {
              exact ne_of_mem_of_not_mem' hp_1factor hp_1factor2
            }
            tauto
          }

          have hfactorization : p.factorization p_1 = 1 := by {
            rw [hnps] at hfactorization2
            have htemp : 2 ^ s ≠ 0 := by exact Ne.symm (NeZero.ne' (2 ^ s))
            have htemp2 : p ≠ 0 := by {
              by_contra hp0
              rw [hp0] at hnps
              simp at hnps
              tauto
            }
            rw [Nat.factorization_mul htemp htemp2] at hfactorization2
            simp at hfactorization2
            have htemp3 : (2).factorization p_1 = 0 := by {
              have htemp4 : ¬ p_1 ∣ 2 := by {
                have : ∀ {p m : ℕ}, Nat.Prime p → (m ∣ p ↔ m = 1 ∨ m = p) := Nat.dvd_prime
                by_contra htemp5
                rw [Nat.dvd_prime Nat.prime_two] at htemp5
                have : p_1 ≠ 1 ∧ p_1 ≠ 2 := by {
                  constructor
                  · exact Nat.Prime.ne_one (Nat.prime_of_mem_primeFactors hp_1)
                  · exact h2
                }
                tauto
              }
              exact Nat.factorization_eq_zero_of_not_dvd htemp4
            }
            rw [htemp3] at hfactorization2
            simp at hfactorization2
            exact hfactorization2
          }

          constructor
          · rw [hfactorization2] at hp
            simp at hp
            obtain ⟨k, hk⟩ := hp
            unfold FermatPrime
            constructor
            · exact Nat.prime_of_mem_primeFactors hp_1
            · have hpnot0 : p_1 ≠ 0 := by exact Nat.Prime.ne_zero (Nat.prime_of_mem_primeFactors hp_1)

              have hk2 : p_1 = 2 ^ k + 1 := by {
                calc p_1 = p_1 - 1 + 1 := by exact nat_sub_plus_one p_1 hpnot0
                       _ = 2 ^ k + 1 := by rw [hk]
              }
              have hk3 : 2 > 1 := by linarith
              have hk4 : k ≠ 0 := by {
                by_contra hk5
                rw [hk5] at hk2
                simp at hk2
                exact h2 hk2
              }
              have hk5 : Nat.Prime (2 ^ k + 1) := by {
                rw [hk2] at hp_1
                exact Nat.prime_of_mem_primeFactors (hsubset hp_1)
              }
              have hm : ∃ m, k = 2 ^ m := by {
                exact Nat.pow_of_pow_add_prime hk3 hk4 hk5
              }
              obtain ⟨m, hm⟩ := hm
              use m
              rw [←hm, hk2]

          · exact hfactorization


      exact hn0


  · -- Second direction of if and only if
    -- This direction is easier, as we have a formula to compute what n.totient is
    intro hn
    obtain ⟨s, p, hn⟩ := hn
    obtain ⟨hn1, hn2⟩ := hn
    unfold ProductOfDistinctFermatPrimes at hn2

    have hp : ∀ p_1 ∈ p.primeFactors, ∃ k, p_1 = 2 ^ (2 ^ k) + 1 := by {
      have hn2 : ∀ p_1 ∈ p.primeFactors, FermatPrime p_1 ∧ p.factorization p_1 = 1 := by exact hn2.2
      intro p_1 hp1
      specialize hn2 p_1
      apply hn2 at hp1
      obtain ⟨hp, _⟩ := hp1
      unfold FermatPrime at hp
      exact hp.2
    }

    have hnnot0 : n ≠ 0 := by {
      by_contra h0
      rw [h0] at hn1
      have hp0 : p = 0 := by {
        by_contra h1
        have hh : 2 ^ s = 0 := by exact eq_zero_of_ne_zero_of_mul_right_eq_zero h1 (id (Eq.symm hn1))
        have hh2 : 2 ^ s ≠ 0 := by exact Ne.symm (NeZero.ne' (2 ^ s))
        exact hh2 hh
      }
      exact hn2.1 hp0
    }

    by_cases hs : s = 0
    · have hnp : n = p := by {
        calc n = 2 ^ s * p := by rw [hn1]
             _ = 2 ^ 0 * p := by rw [hs]
             _ = p := by simp
      }

      use ∑ p_1 ∈ p.primeFactors, Nat.log 2 (p_1 -1)
      rw [hnp]
      exact totient_of_fermat_prime p hn2


    · use (s - 1) + ∑ p_1 ∈ p.primeFactors, Nat.log 2 (p_1 -1)

      have hpfactors : 2 ∉ p.primeFactors := by {
        by_contra h2
        apply hp at h2
        obtain ⟨k, hk⟩ := h2
        simp at hk
        have hk2 : 2 ^ k = 0 := by exact hpowertwo (2 ^ k) hk
        have hk3 : 2 = 0 := by exact pow_eq_zero (hpowertwo (2 ^ k) hk)
        linarith
      }

      have hsprimefactors : (2 ^ s).primeFactors = {2} := by exact Nat.primeFactors_prime_pow hs Nat.prime_two

      have hcoprime : (2^s).Coprime p := by {
        have hdisjoint : Disjoint (2^s).primeFactors p.primeFactors := by {
          rw [hsprimefactors]
          exact Finset.disjoint_singleton_left.mpr hpfactors
        }
        have hnonzero1 : (2^s) ≠ 0 := by exact Ne.symm (NeZero.ne' (2 ^ s))
        have hnonzero2 : p ≠ 0 := by {
          by_contra hp0
          have hn0 : n = 0 := by {
            calc n = 2 ^ s * p := by rw [hn1]
                 _ = 2 ^ s * 0 := by rw [hp0]
                 _ = 0 := by simp
          }
          exact hnnot0 hn0
        }
        exact (Nat.disjoint_primeFactors hnonzero1 hnonzero2).1 hdisjoint
      }

      rw [hn1]

      rw [Nat.totient_mul hcoprime]

      have htotient2 : (2 ^ s).totient = 2 ^ (s - 1) := by {
        calc Nat.totient (2 ^ s) = Nat.totient (2 ^ (s - 1 + 1)) := by nth_rw 1 [nat_sub_plus_one s hs]
                          _ = 2 ^ (s - 1) * (2 - 1) := by rw [Nat.totient_prime_pow_succ Nat.prime_two (s - 1)]
                          _ = 2 ^ (s - 1) := by simp
      }

      have htotient3 : p.totient = 2 ^ (∑ p_1 ∈ p.primeFactors, Nat.log 2 (p_1 - 1)) := by {
        exact totient_of_fermat_prime p hn2
      }

      rw [htotient2, htotient3]
      group

}

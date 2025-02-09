import Project.Polygon
import Project.Robin
import Mathlib.RingTheory.Polynomial.Cyclotomic.Basic

open Construction IntermediateField




set_option maxHeartbeats 0
set_option synthInstance.maxHeartbeats 0
theorem gauss_wantzel (n : ℕ) (hn: n > 2) : (Complex.exp (2 * (Real.pi) * Complex.I  /(n : ℂ ))) ∈ M_inf {(0: ℂ), 1} ↔  (∃ s p : ℕ, n = 2^s * p ∧ ProductOfDistinctFermatPrimes p) := by {
  let M := ({(0: ℂ ), 1} : Set ℂ )
  let ζ := (Complex.exp (2 * (Real.pi) * Complex.I /(n : ℂ )))
  have n_neq_0 : n≠ 0 := by
    linarith
  have kmq : K_zero M = ⊥ := by {
    unfold K_zero M
    unfold conj_set
    simp
    have this : {x:ℂ  | 0 = x ∨ 1 = x} = {0 ,1} := by
      ext x
      simp
      tauto
    rw[this]
    simp
    refine Set.pair_subset ?ha ?hb
    exact zero_mem ⊥
    exact one_mem ⊥

  }
  let L := (K_zero M)⟮ζ⟯

  have poly_same : Polynomial.cyclotomic n (K_zero M) = (minpoly (K_zero M) ζ) := by
    refine @IsPrimitiveRoot.minpoly_eq_cyclotomic_of_irreducible (K_zero M) _ ℂ _ _ ζ n _ ?_ ?_ ?_
    · exact Complex.isPrimitiveRoot_exp n n_neq_0
    · sorry
    · apply @NeZero.charZero (K_zero M) n (neZero_iff.mpr n_neq_0)

  have ζ_alg : IsAlgebraic (↥(K_zero M)) ζ := by
    apply @IsAlgebraic.tower_top ℚ (K_zero M)
    use (Polynomial.X)^n+ (-1)
    constructor
    · refine Polynomial.Monic.ne_zero_of_ne ?h.left.h ?h.left.hp
      · linarith
      · refine Polynomial.monic_X_pow_sub ?h.left.hp.H
        simp
        linarith
    · rw[Polynomial.aeval_add, Polynomial.aeval_X_pow]
      simp
      rw[← sub_eq_add_neg, sub_eq_iff_eq_add']
      ring
      exact (Complex.isPrimitiveRoot_exp n n_neq_0).pow_eq_one

  have L_tot : Module.finrank (K_zero M) L = n.totient := by
    obtain poly_deg:= @IntermediateField.adjoin.finrank (K_zero M) _ ℂ _ _ ζ (IsAlgebraic.isIntegral ζ_alg)
    rw[poly_deg,← poly_same]
    rw[← Polynomial.degree_eq_iff_natDegree_eq]
    · exact Polynomial.degree_cyclotomic n (K_zero M)
    · exact Polynomial.cyclotomic_ne_zero n (K_zero M)
  rw[← phi_pow_two_iff]
  have h₀ : 0 ∈ M := by exact Set.mem_insert 0 {1}
  have h₁ : 1 ∈ M := by exact Set.mem_insert_of_mem 0 rfl
  have n_gt_0 : n > 0 := by linarith

  have h₄ : Polynomial.IsSplittingField (K_zero M) L (minpoly (K_zero M) ζ) := by
    rw[← poly_same]
    have prim_ζ : IsPrimitiveRoot ζ (⟨n, n_gt_0⟩: ℕ+) := by
      simp only
      exact Complex.isPrimitiveRoot_exp n n_neq_0

    obtain L'_cyclo := @IsPrimitiveRoot.adjoin_isCyclotomicExtension (K_zero M) ℂ _ _ _ ζ ⟨n,n_gt_0⟩ prim_ζ
    let L' := (Algebra.adjoin ↥(K_zero M) {ζ})
    have equiv_L'_L : L' ≃ₐ[(K_zero M)] L := by sorry
    obtain := @IsCyclotomicExtension.equiv {⟨n,n_gt_0⟩} (K_zero M) L' _ _ _ L _ _ (L'_cyclo) equiv_L'_L
    apply @IsCyclotomicExtension.splitting_field_cyclotomic ⟨n,n_gt_0⟩ (K_zero M) L _ _ _

  obtain ζ_struct := algebraic_constructable_iff M ζ h₀ h₁ L ζ_alg h₄
  rw[ζ_struct]
  simp_rw[L_tot]
  tauto


}

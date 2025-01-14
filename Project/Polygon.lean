import Construction

import Mathlib.FieldTheory.Galois.Basic
import Mathlib.Data.Setoid.Partition
import Mathlib.Data.Set.Card
import Mathlib.GroupTheory.Sylow
open IntermediateField Construction MulOpposite


#check Subgroup.subtype_comp_inclusion
#check QuotientGroup.leftRel_apply



-- set_option synthInstance.maxHeartbeats 0
set_option diagnostics true


#check mem_leftCoset_leftCoset
#check Subgroup.coe_toSubmonoid
#check leftCoset_mem_leftCoset
#check Set.Nat.card_coe_set_eq
#check QuotientGroup.range_mk
open scoped Pointwise
set_option diagnostics true

--subtype and comap, preimage
--own definition of subgroup normal

lemma ord_pow_two_tower {G : Type*} [Group G] [Finite G] (n : ℕ) (h: Nat.card G = 2^n) :
  ∃ T : Fin (n+1) → Subgroup G, T 0 = ⊤ ∧ T n = ⊥ ∧ ∀ i < n, ((T (i+1) ≤  T i) ∧ ((T (i+1)).relindex (T i)=2)) := by {
    induction n generalizing G with
    | zero =>
      simp at *
      use fun (a : Fin 1) ↦ ⊥
      simp
      obtain card_1 := @Subgroup.card_top G _
      rw[h] at card_1
      symm
      exact Subgroup.eq_bot_of_card_eq ⊤ card_1
    | succ n ih =>
      obtain ⟨K, hK⟩ := @Sylow.exists_subgroup_card_pow_prime G _ _ 2 n _ _
      specialize ih hK


}


lemma index_two_left_coset {G : Type*} [Group G] (H: Subgroup G) (h : H.index = 2):
  { (H : Set G), (H : Set G)ᶜ } = (QuotientGroup.leftRel H).classes := by {
    have hcard : (QuotientGroup.leftRel H).classes.ncard = 2 := by
      rw[Subgroup.index_eq_card] at h
      sorry

    rw[Set.ncard_eq_two] at hcard
    obtain ⟨x,y,hxy,hset⟩ := hcard
    rw[hset]
    have hin: (H: Set G) ∈ (QuotientGroup.leftRel H).classes := by

    -- refine Set.pair_eq_pair_iff.mpr ?intro.intro.intro.a

}

lemma index_two_right_coset {G : Type*} [Group G] (H: Subgroup G) (h : H.index = 2):
  { (H : Set G), (H : Set G)ᶜ } = (QuotientGroup.rightRel H).classes := by {
    sorry
}


lemma index_two_normal {G : Type*} [Group G] (H: Subgroup G) (h : H.index = 2) : H.Normal := by {
  rw[normal_iff_eq_cosets]
  intro g
  by_cases h_mem: g ∈ H
  · rw[leftCoset_mem_leftCoset H h_mem, rightCoset_mem_rightCoset H h_mem]
  · have l_neq : g • (H : Set G) ≠ (H : Set G) := by
      by_contra hc
      obtain := mem_leftCoset_leftCoset H.toSubmonoid hc
      tauto
    have r_neq :op g • (H : Set G) ≠ (H : Set G) := by
      by_contra hc
      obtain := mem_rightCoset_rightCoset H.toSubmonoid hc
      tauto
    have hleft : (g • (H : Set G) ) ∈ ({ (H : Set G), (H : Set G)ᶜ } : Set (Set G)) := by
      rw[index_two_left_coset _ h]
      have coset_eq : g • (H : Set G) = {x : G | (QuotientGroup.leftRel H).Rel x g} := by
        ext x
        simp
        sorry
      rw[coset_eq]
      apply Setoid.mem_classes
    have hright :  (op g • (H : Set G) ) ∈ ({ (H : Set G), (H : Set G)ᶜ } : Set (Set G)) := by
      sorry
    obtain hleft_c := Set.mem_diff_singleton.mpr ⟨hleft, l_neq⟩
    simp at hleft_c
    obtain hright_c := Set.mem_diff_singleton.mpr ⟨hright, r_neq⟩
    simp at hright_c
    simp[hright_c,hleft_c]
}


section degree_two

variable {F: Type*} [Field F] {E : Type*} [Field E] [Algebra F E]
variable (K : IntermediateField F E) (L : IntermediateField K E)


theorem dergree_two_eq_sqr' :  Module.finrank K L = 2 ↔ ∃ x : E, x ^ 2 ∈ K ∧ ¬(x ∈ K) ∧ L = IntermediateField.adjoin K {x} := by {
  sorry
}

end degree_two



lemma algebraic_constructable_iff (M : Set ℂ) (z : ℂ) (h₀: 0 ∈ M) (h₁:1 ∈ M) (h₂: z ∈ K_zero M)
  (L :IntermediateField (K_zero M) ℂ) (h₃ : IsAlgebraic (K_zero M) z)
  (h₄ : Polynomial.IsSplittingField (K_zero M) L (minpoly (K_zero M) z)):
  z ∈ M_inf M ↔ ∃ (n : ℕ), ((2 : ℕ) ^ n) = Module.finrank (K_zero M) L := by {
    constructor
    · sorry
    · intro h
      have h_sep: (minpoly (K_zero M) z ).Separable := by
        apply Irreducible.separable
        apply minpoly.irreducible
        apply IsAlgebraic.isIntegral
        exact h₃
      have L_galois : IsGalois (K_zero M) L := by
        apply IsGalois.of_separable_splitting_field h_sep
      obtain ⟨n, hn⟩ := h
      have L_findim : FiniteDimensional (K_zero M) L := by
        apply FiniteDimensional.of_finrank_pos
        rw[← hn]
        exact Nat.two_pow_pos n
      have L_galdeg : Nat.card (L ≃ₐ[K_zero M] L) = 2^n := by
        rw[hn,Nat.card_eq_fintype_card]
        apply IsGalois.card_aut_eq_finrank
      set Gal := L ≃ₐ[K_zero M] L
      obtain⟨tow_f, ⟨tow_bot,tow_top,sub⟩⟩ := @ord_pow_two_tower Gal _ _ n L_galdeg
  }

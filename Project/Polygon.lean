import Construction

import Mathlib.FieldTheory.Galois.Basic
import Mathlib.Data.Setoid.Partition
import Mathlib.Data.Set.Card
import Mathlib.GroupTheory.Sylow
import Mathlib.GroupTheory.Index
open IntermediateField Construction MulOpposite


#check Subgroup.subtype_comp_inclusion
#check QuotientGroup.leftRel_apply
#check Subgroup.normal_subgroupOf_iff
#check Fin.le_def
#check Fin.val_add_one
#check Subgroup.normalCore
#check Nat.pow_of_pow_add_prime






#check mem_leftCoset_leftCoset
#check Subgroup.coe_toSubmonoid
#check leftCoset_mem_leftCoset
#check Set.Nat.card_coe_set_eq
#check QuotientGroup.range_mk
#check Subgroup.coe_iSup_of_directed
open scoped Pointwise


example (a b c :ℝ)(h : a ≠ 0)(h1 : a * b = a * c) : b = c := by
  simp_all only [ne_eq, mul_eq_mul_left_iff, or_false]





theorem index_map_of_injective  {G : Type u_1} {G' : Type u_2} [Group G] [Group G'] (H : Subgroup G){f : G →* G'} (hf : Function.Injective f) :
    (H.map f).index = H.index * f.range.index := by
  rw [H.index_map, f.ker_eq_bot_iff.mpr hf, sup_bot_eq]

theorem index_map_subtype  {G : Type u_1} [Group G] {H : Subgroup G}  (K : Subgroup H) :
    (K.map H.subtype).index = K.index * H.index := by
  rw [index_map_of_injective K H.subtype_injective, H.subtype_range]


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



lemma ord_pow_two_tower {G : Type*} [Group G] [Finite G] (n : ℕ) (h: Nat.card G = 2^n) :
  ∃ T : Fin (n+1) → Subgroup G, T 0 = ⊤ ∧ T n = ⊥ ∧ ∀ i < n, ((T (i+1) ≤  T i) ∧ ((T (i+1)).relindex (T i)=2) ∧ ((T (i+1)).subgroupOf (T (i))).Normal ) := by {
    induction n generalizing G with
    | zero =>
      simp at *
      use fun a ↦ ⊥
      simp
      obtain card_1 := @Subgroup.card_top G _
      rw[h] at card_1
      symm
      exact Subgroup.eq_bot_of_card_eq ⊤ card_1
    | succ n ih =>
      have hGcarddvd : 2 ^ n ∣ Nat.card G := by
        exact Dvd.intro 2 (id (Eq.symm h))
      obtain ⟨K, hK⟩ := @Sylow.exists_subgroup_card_pow_prime G _ _ 2 n _ hGcarddvd
      specialize ih hK
      obtain ⟨T, hT0, hTnp1, hTi⟩ := ih
      let S : Fin (n+2) → Subgroup G := fun m ↦ if m = 0 then ⊤ else Subgroup.map K.subtype (T (m-1))
      use S
      refine ⟨?_, ?_, ?_⟩
      · tauto
      · unfold S
        simp
        have hif : (n : Fin (n + 1 + 1)) + 1 ≠ 0 := by
          rw[← Fin.val_ne_iff, Fin.val_add_one]
          simp
          rw[← ne_eq, ← Fin.val_ne_iff]
          simp
          ring_nf
          rw[Nat.mod_eq_of_lt]
          · rw[← ne_eq, add_comm]
            exact Nat.ne_add_one n
          · linarith
        simp[hif]
        rw[Fin.val_add_one_of_lt]
        simp
        rw[Nat.mod_eq_of_lt]
        rw[hTnp1]
        exact Subgroup.map_bot K.subtype
        linarith
        rw[Fin.lt_iff_val_lt_val]
        simp
        rw[Nat.mod_eq_of_lt]
        linarith
        linarith
      · intro i hi
        have hip1 : (i : Fin (n + 1 +1)) + 1 ≠ 0 := by
          rw[← Fin.val_ne_iff, Fin.val_add_one]
          simp
          rw[← ne_eq, ← Fin.val_ne_iff]
          simp
          ring_nf
          rw[Nat.mod_eq_of_lt]
          · rw[← ne_eq, add_comm]
            exact Nat.ne_of_lt hi
          · linarith
        have hKind2 : K.index = (2 ^ (n+1))/2 ^ n  := by
          obtain lagrange := Subgroup.index_mul_card K
          rw[h, hK] at lagrange
          rw[eq_comm, Nat.div_eq_iff_eq_mul_left]
          tauto
          exact Nat.two_pow_pos n
          exact Dvd.intro 2 rfl
        ring_nf at hKind2
        simp at hKind2
        by_cases hi0: i = 0
        · subst i
          simp[S]
          by_cases hn0: n=0
          · subst n
            simp at *
            simp[hTnp1]
            constructor
            · exact h
            · exact Subgroup.normal_of_characteristic ⊥
          · have h0ltn: 0 < n := by exact Nat.zero_lt_of_ne_zero hn0
            obtain ⟨hT01sg, hT01ind, hT01norm⟩:= (hTi 0) h0ltn
            simp[hT0] at hT01sg hT01ind hT01norm ⊢
            have hKmapG : (Subgroup.map K.subtype ⊤) = K := by
              aesop
            rw[hKmapG]
            constructor
            · exact hKind2
            · refine Subgroup.Normal.subgroupOf ?_ ⊤
              exact index_two_normal K hKind2
        · simp[S]
          simp[hip1]
          have hndvd : ¬ n + 1 + 1 ∣ i := by
            refine Nat.not_dvd_of_pos_of_lt ?_ ?_
            exact Nat.zero_lt_of_ne_zero hi0
            linarith
          have hi0cast : ¬ @Eq (Fin (n + 2)) ((i : Fin (n + 1 + 1))) 0 := by
            simp[Fin.val_ne_iff, hndvd]
          simp[hndvd, hi0cast]
          have himin_lt_n: i-1 < n := by
            refine Nat.sub_one_lt_of_le ?h₀ ?h₁
            exact Nat.zero_lt_of_ne_zero hi0
            exact Nat.le_of_lt_succ hi
          obtain ⟨hTa,hTb,hTc⟩ := hTi (i-1) himin_lt_n
          norm_cast at hTa hTb hTc
          rw[Nat.sub_one_add_one_eq_of_pos (Nat.zero_lt_of_ne_zero hi0)] at hTa hTb hTc
          have himin1 : ((i-1) : Fin (n+1)) =(((i-1) : ℕ): Fin (n+1)) := by
            refine Eq.symm (Nat.cast_pred ?_)
            exact Nat.zero_lt_of_ne_zero hi0
          rw[Fin.val_add_one_of_lt]
          simp
          rw[Nat.mod_eq_of_lt, himin1]
          have hi_i1_index_2 := by
            obtain hend := Subgroup.relindex_mul_index ((@Subgroup.map_mono _ _ _ _ K.subtype) hTa)
            simp[index_map_subtype, hKind2] at hend
            nth_rw 1 [← hTb] at hend
            nth_rw 2 [mul_comm] at hend
            rw[Subgroup.relindex_mul_index hTa, mul_comm] at hend
            have hindexneq0 : (T ↑i).index ≠ 0 := by
              exact Subgroup.FiniteIndex.finiteIndex
            rw[mul_eq_mul_left_iff ] at hend
            exact hend
          obtain hyes|hno := hi_i1_index_2
          refine ⟨?_,?_,?_⟩
          · exact hTa
          · exact hyes
          · rw[if_neg]
            apply index_two_normal
            apply hyes
            exact hi0cast
          exfalso
          have : (T ↑i).index ≠ 0 := by
            exact Subgroup.FiniteIndex.finiteIndex
          contradiction
          linarith
          rw[Fin.lt_iff_val_lt_val]
          simp
          rw[Nat.mod_eq_of_lt]
          exact hi
          linarith
}
#check Subgroup.relindex_mul_index


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

import Construction

import Mathlib.FieldTheory.Galois.Basic
import Mathlib.Data.Setoid.Partition
import Mathlib.Data.Set.Card
import Mathlib.GroupTheory.Sylow
import Mathlib.GroupTheory.Index
import Mathlib.Logic.Equiv.Set
import Mathlib.Algebra.IsPrimePow
import Mathlib.Data.Nat.Factorization.PrimePow
import Mathlib.NumberTheory.Padics.PadicVal.Basic
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.FieldTheory.PolynomialGaloisGroup
open IntermediateField Construction MulOpposite


#check Subgroup.subtype_comp_inclusion
#check QuotientGroup.leftRel_apply
#check Subgroup.normal_subgroupOf_iff
#check Fin.le_def
#check Fin.val_add_one
#check Subgroup.normalCore
-- #check Nat.pow_of_pow_add_prime






#check mem_leftCoset_leftCoset
#check Subgroup.coe_toSubmonoid
#check leftCoset_mem_leftCoset
#check Set.Nat.card_coe_set_eq
#check QuotientGroup.range_mk
#check Subgroup.coe_iSup_of_directed
open scoped Pointwise







theorem index_map_of_injective  {G : Type*} {G' : Type*} [Group G] [Group G'] (H : Subgroup G){f : G →* G'} (hf : Function.Injective f) :
    (H.map f).index = H.index * f.range.index := by
  rw [H.index_map, f.ker_eq_bot_iff.mpr hf, sup_bot_eq]

theorem index_map_subtype  {G : Type*} [Group G] {H : Subgroup G}  (K : Subgroup H) :
    (K.map H.subtype).index = K.index * H.index := by
  rw [index_map_of_injective K H.subtype_injective, H.subtype_range]




  lemma dvd_conditions (n m: ℕ) (h1: (Nat.minFac n)∣m) (h2: m∣(Nat.minFac n).factorial)
      (h3: m∣n) : m= (Nat.minFac n):= by {
        by_cases hn0 : n =1
        · simp[hn0] at *
          tauto
        · have ppow : IsPrimePow m := by
            rw[isPrimePow_iff_unique_prime_dvd]
            use Nat.minFac n
            simp
            refine ⟨⟨?_, ?_⟩ , ?_⟩
            · exact Nat.minFac_prime hn0
            · exact h1
            · intro q hq hqm
              by_contra hneqp
              by_cases hqp: (Nat.minFac n) < q
              obtain p_dvd_fac := (@Nat.Prime.dvd_factorial (Nat.minFac n) q hq).mp (Nat.dvd_trans hqm h2)
              linarith
              obtain cont := Nat.minFac_le_of_dvd (Nat.Prime.two_le hq) (Nat.dvd_trans hqm h3)
              obtain thing := eq_of_ge_of_not_gt cont hqp
              tauto
          obtain ⟨p, k, pprime, k_gt_0, pkm⟩ := ppow
          subst m
          rw[← Nat.prime_iff] at pprime
          have hnminp : p=n.minFac := by
            refine Nat.le_antisymm ?h₁ ?h₂
            · have this := (Nat.minFac_le_of_dvd (Nat.Prime.two_le (Nat.minFac_prime hn0)) h1)
              rw[Nat.Prime.pow_minFac] at this
              tauto
              exact pprime
              exact Nat.not_eq_zero_of_lt k_gt_0
            · exact Nat.minFac_le_of_dvd (Nat.Prime.two_le pprime) (Nat.dvd_of_pow_dvd k_gt_0 h3)
          rw[← hnminp] at h2 h1 ⊢
          have p2_dvd_not : ¬ p ^ 2 ∣ p.factorial := by
            rw[@padicValNat_dvd_iff_le p (fact_iff.mpr pprime)]
            · nth_rw 2[← mul_one p]
              rw[@padicValNat_factorial_mul p 1 (fact_iff.mpr pprime)]
              simp
            · exact Nat.factorial_ne_zero p
          have hk_lt_2: k < 2 := by
            rw[Nat.Prime.pow_dvd_iff_le_factorization pprime (Nat.factorial_ne_zero p)] at h2 p2_dvd_not
            linarith
          have hk1: k=1 := by linarith
          subst k
          exact Nat.pow_one p
      }











    lemma smallest_prime_index {G : Type*} [Group G] [Finite G] (H: Subgroup G)
      (h : H.index = Nat.minFac (Nat.card G)) : H.Normal := by {
        let K := (MulAction.toPermHom G (G⧸H)).ker
        let p := Nat.minFac (Nat.card G)
        have K_normalcore: K = H.normalCore := Eq.symm (Subgroup.normalCore_eq_ker H)
        let f := MulAction.toPermHom G (G⧸H)
        -- have perm_card: Nat.card (Equiv.Perm (G ⧸ H)) = (H.index).factorial := by sorry
        have perm_card: Nat.card (Equiv.Perm (G ⧸ H)) = (H.index).factorial := by
          rw[Subgroup.index_eq_card]
          obtain fintype_q := Subgroup.fintypeQuotientOfFiniteIndex H
          rw[← Fintype.card_eq_nat_card, ← Fintype.card_eq_nat_card]
          apply @Fintype.card_perm _ ?_
          exact Classical.typeDecidableEq (G ⧸ H)
        have thing : Nat.card (G⧸K) ∣ Nat.card (Equiv.Perm (G ⧸ H)):=
          Subgroup.card_dvd_of_injective (QuotientGroup.kerLift f) (QuotientGroup.kerLift_injective f)
        rw[perm_card, h] at thing
        have k_in_h : K ≤ H := by
          rw[K_normalcore]
          exact Subgroup.normalCore_le H
        have p_dvd : p ∣ Nat.card (G⧸K) := by
          trans H.index
          · unfold p
            rw[h]
          · rw[← Subgroup.index_eq_card]
            simp[Subgroup.index_dvd_of_le, k_in_h]
        obtain hGKcard: Nat.card (G⧸K) = p := by
          apply dvd_conditions (Nat.card G) (Nat.card (G⧸K)) p_dvd thing
          exact Subgroup.card_quotient_dvd_card K
        obtain releq :=  Subgroup.relindex_mul_index k_in_h
        rw[Subgroup.index_eq_card K, hGKcard, h, ← one_mul p] at releq
        unfold p at releq
        obtain KrelH := Nat.mul_right_cancel (Nat.minFac_pos (Nat.card G)) releq
        rw[Subgroup.relindex_eq_one] at KrelH
        obtain HeqK := eq_of_le_of_le k_in_h KrelH
        rw[K_normalcore] at HeqK
        rw[← HeqK]
        exact Subgroup.normalCore_normal H
    }

lemma ord_pow_two_tower' {G : Type*} [Group G] [Finite G] (n : ℕ) (h: Nat.card G = 2^n) :
  ∃ T : ℕ → Subgroup G, T 0 = ⊤ ∧ T n = ⊥ ∧ (∀ i : ℕ, (T (i+1) ≤  T i)) ∧ ∀ i < n, ((T (i+1)).relindex (T i)=2) ∧ ((T (i+1)).subgroupOf (T (i))).Normal  := by {
    induction n generalizing G with
    | zero =>
      simp only [pow_zero, not_lt_zero', false_implies, implies_true, and_true] at *
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
      obtain ⟨T, hT0, hTnp1, hTi⟩ := ih hK
      let S : ℕ → Subgroup G := fun m ↦ if m = 0 then ⊤ else Subgroup.map K.subtype (T (m-1))
      use S
      refine ⟨?_, ?_, ?_, ?_⟩
      · tauto
      · unfold S
        simp[hTnp1]
      · intro i
        by_cases hi0 : i = 0
        · subst i
          simp[S]
        · simp[S, hi0]
          obtain ⟨T_sub, ignore⟩ := hTi
          obtain wts := T_sub (i - 1)
          simp[Nat.sub_one_add_one hi0] at wts
          tauto
      · intro i hi
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
            simp[hTnp1] at *
            constructor
            · exact h
            · exact Subgroup.normal_of_characteristic ⊥
          · have h0ltn: 0 < n := by exact Nat.zero_lt_of_ne_zero hn0
            obtain ⟨ignore, hTi⟩ := hTi
            obtain ⟨hT01ind, hT01norm⟩:= (hTi 0) h0ltn
            simp[hT0] at hT01ind hT01norm ⊢
            have hKmapG : (Subgroup.map K.subtype ⊤) = K := by
              aesop
            rw[hKmapG]
            constructor
            · exact hKind2
            · refine Subgroup.Normal.subgroupOf ?_ ⊤
              -- exact index_two_normal K hKind2
              apply smallest_prime_index
              simp[hKind2, h, (Nat.Prime.pow_minFac Nat.prime_two)]
        · simp[S, hi0]
          have himin_lt_n: i-1 < n := by
            refine Nat.sub_one_lt_of_le ?h₀ ?h₁
            exact Nat.zero_lt_of_ne_zero hi0
            exact Nat.le_of_lt_succ hi
          obtain ⟨T_sub, hTi⟩ := hTi
          obtain hTa := T_sub (i-1)
          rw[Nat.sub_one_add_one hi0] at hTa
          obtain ⟨hTb,hTc⟩ := hTi (i-1) himin_lt_n
          rw[Nat.sub_one_add_one_eq_of_pos (Nat.zero_lt_of_ne_zero hi0)] at hTb hTc
          have hi_i1_index_2 := by
            obtain hend := Subgroup.relindex_mul_index ((@Subgroup.map_mono _ _ _ _ K.subtype) hTa)
            simp[index_map_subtype, hKind2] at hend
            nth_rw 1 [← hTb] at hend
            nth_rw 2 [mul_comm] at hend
            rw[Subgroup.relindex_mul_index hTa, mul_comm] at hend
            have hindexneq0 : (T ↑i).index ≠ 0 := by
              exact Subgroup.FiniteIndex.finiteIndex
            rw[mul_eq_mul_left_iff ] at hend
            simp[hindexneq0] at hend
            exact hend
          refine ⟨?_,?_⟩
          · exact hi_i1_index_2
          · rw[if_neg]
            -- apply index_two_normal
            -- apply hi_i1_index_2
            -- exact hi0
            apply smallest_prime_index
            have two_smallest_prime_dvd: (Nat.card ↥(Subgroup.map K.subtype (T (i - 1)))).minFac = 2 := by{
              have thingy : Nat.card ↥(Subgroup.map K.subtype (T (i - 1))) = Nat.card ↥(T (i-1)) := by{
                apply Nat.card_image_of_injective (Subgroup.subtype_injective K)
              }
              rw[thingy]
              obtain sub_two_gp := IsPGroup.to_subgroup (IsPGroup.of_card hK) (T (i-1))
              have non_triv : Nontrivial ↥(T (i-1)) := by{
                refine Finite.one_lt_card_iff_nontrivial.mp ?_
                have this2: ((⊥ : Subgroup ↥K).relindex (T (i-1))) ≠ 0 := by{
                  simp
                  refine Nat.card_ne_zero.mpr ?_
                  constructor
                  · exact One.instNonempty
                  · exact Subgroup.instFiniteSubtypeMem (T (i - 1))
                }
                obtain thingy2 := Subgroup.relindex_le_of_le_left (OrderBot.bot_le (T i)) this2
                simp[hTb] at thingy2
                linarith
              }
              rw[IsPGroup.nontrivial_iff_card sub_two_gp] at non_triv
              obtain ⟨n,hn0,hncard⟩ := non_triv
              rw[hncard]
              apply Nat.Prime.pow_minFac Nat.prime_two
              linarith
            }

            rw[two_smallest_prime_dvd]
            apply hi_i1_index_2
            exact hi0


}



section degree_two

variable {F: Type*} [Field F] {E : Type*} [Field E] [Algebra F E]
variable (K : IntermediateField F E) (L : IntermediateField K E)


theorem dergree_two_eq_sqr' :  Module.finrank K L = 2 ↔ ∃ x : E, x ^ 2 ∈ K ∧ ¬(x ∈ K) ∧ L = IntermediateField.adjoin K {x} := by {
  sorry
}

end degree_two



lemma fixedField_bot {k : Type*} {K : Type*} [Field k] [Field K] [Algebra k K] [IsGalois k K] :
      IntermediateField.fixedField (⊤ : Subgroup (K ≃ₐ[k] K)) = ⊥ := by sorry
lemma fixedField_top {k : Type*} {K : Type*} [Field k] [Field K] [Algebra k K] [IsGalois k K] :
      IntermediateField.fixedField (⊥ : Subgroup (K ≃ₐ[k] K)) = ⊤ := by sorry


lemma algebraic_constructable_iff (M : Set ℂ) (z : ℂ) (h₀: 0 ∈ M) (h₁:1 ∈ M)
  (L :IntermediateField (K_zero M) ℂ) (h₃ : IsAlgebraic (K_zero M) z)
  (h₄ : Polynomial.IsSplittingField (K_zero M) L (minpoly (K_zero M) z)):
  z ∈ M_inf M ↔ ∃ (n : ℕ), ((2 : ℕ) ^ n) = Module.finrank (K_zero M) L := by {
    let minz := minpoly (K_zero M) z
    have irr_minz : Irreducible minz := by
      apply minpoly.irreducible
      apply IsAlgebraic.isIntegral h₃
    constructor
    · intro hz
      obtain ⟨n, F, h1, h2, h3, h4⟩ := (Classfication_z_in_M_inf M z h₀ h₁).mp hz
      have root_const :(((minpoly (K_zero M) z)).rootSet ℂ)  ⊆ M_inf M := by{
        intro r hr
        have minz_fact : Fact ((Polynomial.Splits (algebraMap ↥(K_zero M) ℂ) minz) ):= by
          rw[fact_iff]
          apply Polynomial.splits_of_isScalarTower ℂ (Polynomial.IsSplittingField.splits L minz)

        obtain trans_act := Polynomial.Gal.galAction_isPretransitive minz ℂ irr_minz
        sorry
      }
      sorry
    · intro h
      have z_in_L : z ∈ L := by
        apply IsIntegral.mem_intermediateField_of_minpoly_splits
        · rw[← isAlgebraic_iff_isIntegral]
          exact h₃
        · exact h₄.1
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
      obtain⟨tow_f, ⟨tow_bot,tow_top,⟨sub,relind⟩⟩⟩ := @ord_pow_two_tower' Gal _ _ n L_galdeg
      rw[Classfication_z_in_M_inf _ _ h₀ h₁]
      let f_L := fun m ↦IntermediateField.restrictScalars ℚ (IntermediateField.lift (IntermediateField.fixedField (tow_f m)))
      have f_L_tower : ∀ (i : ℕ), f_L i ≤ f_L (i+1) := by {
        intro i
        specialize sub i
        simp[f_L]
        have base_gal: fixedField (tow_f i) ≤ fixedField (tow_f (i+1)) := by
          rw[IntermediateField.le_iff_le, IntermediateField.fixingSubgroup_fixedField]
          exact sub
        have wts: lift (fixedField (tow_f i)) ≤ lift (fixedField (tow_f (i+1))) := by
          apply IntermediateField.map_mono L.val
          exact base_gal
        exact fun x a ↦ wts ((@IntermediateField.mem_restrictScalars ℚ ℂ (K_zero M) _ _ _ _ _ _ _ (lift (fixedField (tow_f i)))).mp a)
      }
      have f_L_n : z ∈ f_L n := by
        simp[f_L, tow_top]
        rw[(@IntermediateField.mem_lift (K_zero M) ℂ _ _ _ L (fixedField ⊥) ⟨z, z_in_L⟩ ),fixedField_top]
        simp
      have f_L_0 : K_zero M = f_L 0 := by
        simp[f_L,tow_bot]
        rw[fixedField_bot]
        simp
      have f_L_rank : ∀ i < n, (f_L i).relfinrank (f_L (i + 1)) = 2 := by
        intro i hin
        unfold relfinrank
        specialize relind i hin
        sorry
      use n, f_L

}




      -- use n, f_L, f_L_tower
      -- refine ⟨?_,?_,?_⟩
      -- · simp[f_L,tow_top]
      --   sorry
      -- · simp[f_L,tow_bot]
      --   sorry
      -- · intro i hin
      --   sorry





  #check IsGalois.intermediateFieldEquivSubgroup
  #check IntermediateField.extendScalars.orderIso
  #check WithTop.coe_le_coe
  #check IntermediateField.mem_lift
  #check IsGalois.card_fixingSubgroup_eq_finrank

import Project.Polygon
import Project.Robin
import Mathlib.RingTheory.Polynomial.Cyclotomic.Basic

open Construction IntermediateField





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
  have ζ_alg : IsAlgebraic (↥(K_zero M)) ζ := by
    apply @IsAlgebraic.tower_top ℚ (K_zero M)
    use (Polynomial.X)^n-1
    sorry
  have poly_same : Polynomial.cyclotomic n (K_zero M) = (minpoly (K_zero M) ζ) := by
    refine @IsPrimitiveRoot.minpoly_eq_cyclotomic_of_irreducible (K_zero M) _ ℂ _ _ ζ n _ ?_ ?_ ?_
    · exact Complex.isPrimitiveRoot_exp n n_neq_0
    · sorry
    · apply @NeZero.charZero (K_zero M) n (neZero_iff.mpr n_neq_0)
  have L_tot : Module.finrank (K_zero M) L = n.totient := by
    obtain poly_deg:= @IntermediateField.adjoin.finrank (K_zero M) _ ℂ _ _ ζ (IsAlgebraic.isIntegral ζ_alg)
    rw[poly_deg,← poly_same]
    rw[← Polynomial.degree_eq_iff_natDegree_eq]
    · exact Polynomial.degree_cyclotomic n (K_zero M)
    · exact Polynomial.cyclotomic_ne_zero n (K_zero M)
  rw[← phi_pow_two_iff]
  have h₀ : 0 ∈ M := by exact Set.mem_insert 0 {1}
  have h₁ : 1 ∈ M := by exact Set.mem_insert_of_mem 0 rfl
  have h₄ : Polynomial.IsSplittingField (K_zero M) L (minpoly (K_zero M) ζ) := by sorry
  obtain ζ_struct := algebraic_constructable_iff M ζ h₀ h₁ L ζ_alg h₄
  rw[ζ_struct]
  simp_rw[L_tot]
  tauto

}

#check Nat.fermatNumber

-- intro hz
--       obtain ⟨n, F, h1, h2, h3, h4⟩ := (Classfication_z_in_M_inf M z h₀ h₁).mp hz
--       let NC := @normalClosure (K_zero M) (F n) ℂ _ _ _ ?_ _
--       have root_const :(((minpoly (K_zero M) z)).rootSet NC)  ⊆ M_inf M := by{
--         intro r hr
--         have minz_fact : Fact ((Polynomial.Splits (algebraMap ↥(K_zero M) NC) minz) ):= by
--           rw[fact_iff]
--           apply Polynomial.splits_of_isScalarTower NC (Polynomial.IsSplittingField.splits L minz)

--         obtain trans_act := Polynomial.Gal.galAction_isPretransitive minz ℂ irr_minz
--         have z_root : z ∈ (((minpoly (K_zero M) z)).rootSet NC) := by
--           rw[Polynomial.mem_rootSet_of_ne]
--           · apply minpoly.aeval
--           · exact Polynomial.ne_zero_of_mem_rootSet hr
--         obtain σ := @MulAction.exists_smul_eq minz.Gal _ (Polynomial.Gal.smul minz NC) trans_act
--         obtain ⟨σ, hσ⟩ := σ ⟨z, z_root⟩ ⟨r,hr⟩
--         obtain := Polynomial.Gal.restrict_surjective minz NC


-- intro hz
--       obtain ⟨n, F, h1, h2, h3, h4⟩ := (Classfication_z_in_M_inf M z h₀ h₁).mp hz
--       have root_const :(((minpoly (K_zero M) z)).rootSet ℂ)  ⊆ M_inf M := by{
--         intro r hr
--         have minz_fact : Fact ((Polynomial.Splits (algebraMap ↥(K_zero M) ℂ) minz) ):= by
--           rw[fact_iff]
--           apply Polynomial.splits_of_isScalarTower ℂ (Polynomial.IsSplittingField.splits L minz)

--         obtain trans_act := Polynomial.Gal.galAction_isPretransitive minz ℂ irr_minz
--         have z_root : z ∈ (((minpoly (K_zero M) z)).rootSet ℂ) := by
--           rw[Polynomial.mem_rootSet_of_ne]
--           · apply minpoly.aeval
--           · exact Polynomial.ne_zero_of_mem_rootSet hr
--         obtain σ := @MulAction.exists_smul_eq minz.Gal _ (Polynomial.Gal.smul minz ℂ) trans_act
--         obtain ⟨σ, hσ⟩ := σ ⟨z, z_root⟩ ⟨r,hr⟩
--         obtain := Polynomial.Gal.restrict_surjective minz ℂ






      -- obtain ⟨n, F, h1, h2, h3, h4⟩ := (Classfication_z_in_M_inf M z h₀ h₁).mp hz
      -- have wts: L ≤ extendScalars (K_zero_in_MField M h₀ h₁) := by{
      --   rw[← (IntermediateField.lift_top (K_zero M) L)]
      --   obtain L_adj := (isSplittingField_iff_intermediateField.mp h₄).2
      --   rw[← L_adj, IntermediateField.lift_adjoin, IntermediateField.adjoin_le_iff]
      --   -- rw[IntermediateField.coe_extendScalars]
      --   intro r hr
      --   simp
      --   have type_thing : ∀ (y: ℂ), y ∈ @Subfield.toIntermediateField ℚ ℂ _ _ _ (MField M h₀ h₁) (fun x ↦ SubfieldClass.ratCast_mem (MField M h₀ h₁) x) ↔  y ∈ M_inf M := by{
      --     intro y
      --     constructor
      --     · exact fun a ↦ a
      --     · intro hy
      --       exact hy
      --   }
      --   rw[type_thing r]
      --   have k_zero_fn : (K_zero M) ≤ (F n) := by
      --     obtain fmono := monotone_nat_of_le_succ h1
      --     rw[h3]
      --     aesop
      --   let NC := @normalClosure (K_zero M) (extendScalars k_zero_fn) ℂ _ _ _ _ _
      --   -- have minz_fact : Fact ((Polynomial.Splits (algebraMap ↥(K_zero M) NC) minz) ):= by
      --   --   rw[fact_iff]
      --   --   apply Polynomial.splits_of_isScalarTower NC (Polynomial.IsSplittingField.splits L minz)
      --   have z_nc : z ∈ NC := by
      --     obtain fn_lt_NC:= SetLike.coe_subset_coe.mpr (@IntermediateField.le_normalClosure (K_zero M) ℂ _ _ _ (extendScalars k_zero_fn))
      --     simp[NC]
      --     have this: z ∈ extendScalars k_zero_fn := h2
      --     apply fn_lt_NC this
      --   have z_root : ⟨z, z_nc⟩ ∈ (((minpoly (K_zero M) z)).rootSet NC) := by
      --     refine (Polynomial.mem_rootSet_of_ne ?hp).mpr ?_
      --     · apply minpoly.ne_zero (IsAlgebraic.isIntegral h₃)
      --     · sorry
      --   --   rw[Polynomial.mem_rootSet_of_ne]
      --   --   · apply minpoly.aeval
      --   --   · exact Polynomial.ne_zero_of_mem_rootSet hr
      --   have NC_nc : IsNormalClosure (K_zero M) (extendScalars k_zero_fn) NC := by
      --     refine @Algebra.IsAlgebraic.isNormalClosure_normalClosure _ _ _ _ _ _ _ _ ?_ ?_
      --     · sorry
      --       -- apply @Algebra.IsAlgebraic.tower_top ℚ
      --     · sorry
      --   have minz_fact : Fact ((Polynomial.Splits (algebraMap ↥(K_zero M) ℂ) minz) ):= by
      --     rw[fact_iff]
      --     apply Polynomial.splits_of_isScalarTower ℂ (Polynomial.IsSplittingField.splits L minz)
      --   obtain trans_act := Polynomial.Gal.galAction_isPretransitive minz ℂ irr_minz
      --   obtain σ := @MulAction.exists_smul_eq minz.Gal _ (Polynomial.Gal.smul minz ℂ) trans_act
      --   obtain ⟨σ, hσ⟩ := σ ⟨z, z_root⟩ ⟨r,hr⟩




      --   sorry
      -- }
      -- have h_sep: (minpoly (K_zero M) z ).Separable := by
      --   apply Irreducible.separable
      --   apply minpoly.irreducible
      --   apply IsAlgebraic.isIntegral
      --   exact h₃
      -- have L_galois : IsGalois (K_zero M) L := by
      --   apply IsGalois.of_separable_splitting_field h_sep
      -- obtain L_sep := (isGalois_iff.mp L_galois).1
      -- obtain this := @Field.exists_primitive_element (K_zero M) L _ _ _ (Polynomial.IsSplittingField.finiteDimensional L minz) _
      -- sorry

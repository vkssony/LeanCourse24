import LeanCourse.Common
import Mathlib.Data.Complex.Exponential
noncomputable section
open Real Function BigOperators Set Finset
open Classical


/-

* From Mathematics in Lean https://leanprover-community.github.io/mathematics_in_lean
  Read chapters 7 and 8.1.
  Chapter 7 explains some of the design decisions for classes in Mathlib.

* Do the exercises corresponding to these sections in the `LeanCourse/MIL` folder.
  There are solutions in the solution folder in case you get stuck.

* Hand in the solutions to the exercises under "Exercises to hand-in". Deadline: 19.11.

* Make sure the file you hand-in compiles without error.
  Use `sorry` if you get stuck on an exercise.
-/


/-! # Exercises to practice. -/


/- Prove the following exercises about functions where the domain/codomain are
subtypes. -/

abbrev PosReal : Type := {x : ℝ // x > 0}

/- Codomain is a subtype (usually not recommended). -/
example (f : ℝ → PosReal) (hf : Monotone f) :
    Monotone (fun x ↦ log (f x)) := by {
  sorry
  }

/- Specify that the range is a subset of a given set (recommended). -/
example (f : ℝ → ℝ) (hf : range f ⊆ {x | x > 0}) (h2f : Monotone f) :
  Monotone (log ∘ f) := by {
  sorry
  }

/- Domain is a subtype (not recommended). -/
example (f : PosReal → ℝ) (hf : Monotone f) :
    Monotone (fun x ↦ f ⟨exp x, exp_pos x⟩) := by {
  sorry
  }

/- Only specify that a function is well-behaved on a subset of its domain (recommended). -/
example (f : ℝ → ℝ) (hf : MonotoneOn f {x | x > 0}) :
    Monotone (fun x ↦ f (exp x)) := by {
  sorry
  }



variable {G H K : Type*} [Group G] [Group H] [Group K]
open Subgroup


/- State and prove that the preimage of `U` under the composition of `φ` and `ψ` is a preimage
of a preimage of `U`. This should be an equality of subgroups! -/
example (φ : G →* H) (ψ : H →* K) (U : Subgroup K) : sorry := sorry

/- State and prove that the image of `S` under the composition of `φ` and `ψ`
is a image of an image of `S`. -/
example (φ : G →* H) (ψ : H →* K) (S : Subgroup G) : sorry := sorry



/- Define the conjugate of a subgroup, as the elements of the form `xhx⁻¹` for `h ∈ H`. -/
def conjugate (x : G) (H : Subgroup G) : Subgroup G := sorry


/- Now let's prove that a group acts on its own subgroups by conjugation. -/

lemma conjugate_one (H : Subgroup G) : conjugate 1 H = H := by {
  sorry
  }

lemma conjugate_mul (x y : G) (H : Subgroup G) :
    conjugate (x * y) H = conjugate x (conjugate y H) := by {
  sorry
  }


/- Saying that a group `G` acts on a set `X` can be done with `MulAction`.
The two examples below show the two properties that a group action must satisfy. -/
#print MulAction

variable (G : Type*) {X : Type*} [Group G] [MulAction G X]
example (g g' : G) (x : X) : (g * g') • x = g • (g' • x) := by exact?
example (x : X) : (1 : G) • x = x := by exact?

/- Now show that `conjugate` specifies a group action from `G` onto its subgroups. -/
instance : MulAction G (Subgroup G) := sorry



/-! # Exercises to hand-in. -/


/- A `Setoid` is the name for an equivalence relation in Lean.
Let's define the smallest equivalence relation on a type `X`. -/
def myEquivalenceRelation (X : Type*) : Setoid X where
  r x y := x = y
  iseqv := {
    refl := by exact fun x ↦ rfl
    symm := by exact fun {x y} a ↦ id (Eq.symm a)
    trans := by {
      intro x y z hxy hyz
      rw [hxy]
      exact hyz
    }
  } -- Here you have to show that this is an equivalence.
                 -- If you click on the `sorry`, a lightbulb will appear to give the fields

/- This simp-lemma will simplify `x ≈ y` to `x = y` in the lemma below. -/
@[simp] lemma equiv_iff_eq (X : Type*) (x y : X) :
  letI := myEquivalenceRelation X; x ≈ y ↔ x = y := by rfl

/-
Now let's prove that taking the quotient w.r.t. this equivalence relation is
equivalent to the original type.

Use `Quotient.mk` to define a map into a quotient (or its notation `⟦_⟧`)
Use `Quotient.lift` to define a map out of a quotient.
Use `Quotient.sound` to prove that two elements of the quotient are equal.
Use `Quotient.ind` to prove something for all elements of a quotient.
You can use this using the induction tactic: `induction x using Quotient.ind; rename_i x`.
-/
def quotient_equiv_subtype (X : Type*) :
    Quotient (myEquivalenceRelation X) ≃ X where
      toFun := Quotient.lift (fun x ↦ x) (by simp)
      invFun := Quotient.mk (myEquivalenceRelation X)
      left_inv := by
        apply Quotient.ind
        simp
      right_inv := by
        unfold Function.RightInverse LeftInverse
        simp


section GroupActions

variable (G : Type*) {X : Type*} [Group G] [MulAction G X]

/- Below is the orbit of an element `x ∈ X` w.r.t. a group action by `G`.
Prove that the orbits of two elements are equal
precisely when one element is in the orbit of the other. -/
def orbitOf (x : X) : Set X := range (fun g : G ↦ g • x)

lemma orbitOf_eq_iff (x y : X) : orbitOf G x = orbitOf G y ↔ y ∈ orbitOf G x := by {
  constructor
  · intro h
    have h2 : y ∈ orbitOf G y := by {
      unfold orbitOf Set.range
      refine mem_setOf.mpr ?_
      use 1
      exact MulAction.one_smul y
    }
    rw [← h] at h2
    exact h2
  · intro h
    unfold orbitOf Set.range at h
    have h2 : ∃ g₁, (fun g : G ↦ g • x) g₁ = y := by exact h
    unfold orbitOf Set.range
    ext x₁
    constructor
    · intro h3
      simp at h3 ⊢
      obtain ⟨g, hg⟩ := h2
      obtain ⟨g1, hg1⟩ := h3
      have h4 : x = g⁻¹ • y := by exact eq_inv_smul_iff.mpr hg
      use g1 * g⁻¹
      calc (g1 * g⁻¹) • y = g1 • (g⁻¹ • y)  := by exact mul_smul g1 g⁻¹ y
                        _ = g1 • x          := by rw [h4]
                        _ = x₁              := by rw [hg1]
    · intro h3
      simp at h3 ⊢
      obtain ⟨g, hg⟩ := h2
      obtain ⟨g1, hg1⟩ := h3
      have h4 : y = g • x := by exact id (Eq.symm hg)
      use g1 * g
      calc (g1 * g) • x = g1 • (g • x)  := by exact mul_smul g1 g x
                        _ = g1 • y          := by rw [h4]
                        _ = x₁              := by rw [hg1]
  }

/- Define the stabilizer of an element `x` as the subgroup of elements
`g ∈ G` that satisfy `g • x = x`. -/
def stabilizerOf (x : X) : Subgroup G where
  carrier := {g : G | g • x = x}
  mul_mem' := by {
    intro a b ha hb
    simp at ha hb ⊢
    rw [mul_smul a b x, hb, ha]
  }
  one_mem' := by simp
  inv_mem' := by {
    simp
    intro g hg
    calc g⁻¹ • x  = g⁻¹ • (g • x) := by rw [hg]
                _ = (g⁻¹ * g) • x := by exact smul_smul g⁻¹ g x
                _ = (1:G) • x := by group
                _ = x := by exact MulAction.one_smul x
  }

-- This is a lemma that allows `simp` to simplify `x ≈ y` in the proof below.
@[simp] theorem leftRel_iff {x y : G} {s : Subgroup G} :
    letI := QuotientGroup.leftRel s; x ≈ y ↔ x⁻¹ * y ∈ s :=
  QuotientGroup.leftRel_apply

/- Let's probe the orbit-stabilizer theorem.

Hint: Only define the forward map (as a separate definition),
and use `Equiv.ofBijective` to get an equivalence.
(Note that we are coercing `orbitOf G x` to a (sub)type in the right-hand side) -/

def orbit_stabilizer_theorem (x : X) : G ⧸ stabilizerOf G x ≃ orbitOf G x where
  toFun := sorry
  invFun := sorry
  left_inv := sorry
  right_inv := sorry


end GroupActions

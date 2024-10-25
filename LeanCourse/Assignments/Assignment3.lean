import LeanCourse.Common
import Mathlib.Data.Complex.Exponential
open Real Function Set Nat

/-

* From Mathematics in Lean https://leanprover-community.github.io/mathematics_in_lean
  Read chapter 3, sections 2, 3, 5, 6.
  Read chapter 4, section 1.

* Do the exercises corresponding to these sections in the `LeanCourse/MIL` folder.
  There are solutions in the solution folder in case you get stuck.

* Hand in the solutions to the exercises below. Deadline: 29.10.2023.

* Make sure the file you hand-in compiles without error.
  Use `sorry` if you get stuck on an exercise.
-/


/-! # Exercises to practice. -/


example {p : ℝ → Prop} (h : ∀ x, p x) : ∃ x, p x := by {
  sorry
  }


example {α : Type*} {p q : α → Prop} (h : ∀ x, p x → q x) :
    (∃ x, p x) → (∃ x, q x) := by {
  sorry
  }

/- Prove the following with basic tactics, without using `tauto` or lemmas from Mathlib. -/
example {α : Type*} {p : α → Prop} {r : Prop} :
    ((∃ x, p x) → r) ↔ (∀ x, p x → r) := by {
  sorry
  }

/- Prove the following with basic tactics, without using `tauto` or lemmas from Mathlib. -/
example {α : Type*} {p : α → Prop} {r : Prop} :
    (∃ x, p x ∧ r) ↔ ((∃ x, p x) ∧ r) := by {
  sorry
  }

/- Prove the following without using `push_neg` or lemmas from Mathlib.
You will need to use `by_contra` in the proof. -/
example {α : Type*} (p : α → Prop) : (∃ x, p x) ↔ (¬ ∀ x, ¬ p x) := by {
  sorry
  }

def SequentialLimit (u : ℕ → ℝ) (l : ℝ) : Prop :=
  ∀ ε > 0, ∃ N, ∀ n ≥ N, |u n - l| < ε

example (a : ℝ) : SequentialLimit (fun n : ℕ ↦ a) a := by {
  sorry
  }

/-
`(n)!` denotes the factorial function on the natural numbers.
The parentheses are mandatory when writing.
Use `calc` to prove this.
You can use `exact?` to find lemmas from the library,
such as the fact that factorial is monotone. -/
example (n m k : ℕ) (h : n ≤ m) : (n)! ∣ (m + 1)! := by {
  sorry
  }

section Set

variable {α β : Type*} {s t : Set α}

/- Prove the following statements about sets. -/

example {f : β → α} : f '' (f ⁻¹' s) ⊆ s := by {
  sorry
  }

example {f : β → α} (h : Surjective f) : s ⊆ f '' (f ⁻¹' s) := by {
  sorry
  }

example {f : α → β} (h : Injective f) : f '' s ∩ f '' t ⊆ f '' (s ∩ t) := by {
  sorry
  }

example {I : Type*} (f : α → β) (A : I → Set α) : (f '' ⋃ i, A i) = ⋃ i, f '' A i := by {
  sorry
  }

example : (fun x : ℝ ↦ x ^ 2) '' univ = { y : ℝ | y ≥ 0 } := by {
  sorry
  }

end Set

/-! # Exercises to hand-in. -/


/- Prove the following with basic tactics, without using `tauto` or lemmas from Mathlib. -/
lemma exists_distributes_over_or {α : Type*} {p q : α → Prop} :
    (∃ x, p x ∨ q x) ↔ (∃ x, p x) ∨ (∃ x, q x) := by {
  constructor
  · intro h
    obtain ⟨x, hx⟩  := h
    obtain hp|hq := hx
    · left
      use x
    · right
      use x
  · intro h
    obtain hep|heq := h
    · obtain ⟨x,hx⟩ := hep
      use x
      left
      exact hx
    · obtain ⟨x,hx⟩ := heq
      use x
      right
      exact hx

  }

section Surjectivity

/- Lean's mathematical library knows what a surjective function is,
but let's define it here ourselves and prove some things about it. -/
def SurjectiveFunction (f : ℝ → ℝ) : Prop :=
  ∀ (y : ℝ), ∃ (x : ℝ), f x = y

variable {f g : ℝ → ℝ} {x : ℝ}

/- `rfl` or `simp` can compute the following.
`simp` is a very useful tactic that can simplify many expressions. -/
example : (g ∘ f) x = g (f x) := by simp

lemma surjective_composition (hf : SurjectiveFunction f) :
    SurjectiveFunction (g ∘ f) ↔ SurjectiveFunction g := by {
  unfold SurjectiveFunction
  constructor
  · intro h z
    obtain ⟨x,hx⟩ := h z
    use f x
    apply hx
  · intro hg z
    obtain ⟨y,hy⟩ := hg z
    obtain ⟨x,hx⟩ := hf y
    rw[← hx] at hy
    use x
    apply hy
  }

/- When composing a surjective function by a linear function
to the left and the right, the result will still be a
surjective function. The `ring` tactic will be very useful here! -/
lemma surjective_linear (hf : SurjectiveFunction f) :
    SurjectiveFunction (fun x ↦ 2 * f (3 * (x + 4)) + 1) := by {
  unfold SurjectiveFunction
  unfold SurjectiveFunction at hf
  intro z
  obtain ⟨x,hx⟩ := hf ((z-1)/2)
  let y := (x/3)-4
  use y
  ring
  rw[hx]
  ring
  }

/- Let's prove Cantor's theorem:
there is no surjective function from any set to its power set.
Hint: use `let R := {x | x ∉ f x}` to consider the set `R` of elements `x`
that are not in `f x`
-/
lemma exercise_cantor (α : Type*) (f : α → Set α) : ¬ Surjective f := by {
  let R := {x | x ∉ f x}
  intro h
  obtain ⟨a, ha⟩ := h R
  by_cases haR : a ∈ f a
  · rw[ha] at haR
    have hanR: a ∉ R := by
      rw[mem_setOf, ha] at haR
      assumption -- compress possible?
    apply hanR haR
  · rw[ha] at haR
    have hanR: a ∈ R := by
      rw[mem_setOf, ha] at haR
      apply not_not_mem.mp at haR
      assumption
    apply haR hanR
  }

end Surjectivity

/- Prove that the sum of two converging sequences converges. -/
lemma sequentialLimit_add {s t : ℕ → ℝ} {a b : ℝ}
      (hs : SequentialLimit s a) (ht : SequentialLimit t b) :
    SequentialLimit (fun n ↦ s n + t n) (a + b) := by {
  unfold SequentialLimit
  intro ε hεp
  unfold SequentialLimit at hs ht
  obtain ⟨Ns, hNs⟩ := hs (ε/2) (half_pos hεp)
  obtain ⟨Nt, hNt⟩ := ht (ε/2) (half_pos hεp)
  let N := max Ns Nt
  use N
  intro n hn
  have hnNs : n ≥ Ns := by
    trans N
    · assumption
    · apply le_max_left
  have hnNt : n ≥ Nt := by
    trans N
    · assumption
    · apply le_max_right
  specialize hNs n hnNs
  specialize hNt n hnNt
  simp
  have hnice := calc
   |s n + t n - (a + b)|=|(s n - a) + (t n - b)| := by ring
   _ ≤ |s n - a| + |t n - b| := by apply abs_add
   _ < ε/2 + ε/2 := by gcongr
   _ = ε := by ring
  exact hnice
  }

/- It may be useful to case split on whether `c = 0` is true. -/
lemma sequentialLimit_mul_const {s : ℕ → ℝ} {a : ℝ} (c : ℝ) (hs : SequentialLimit s a) :
    SequentialLimit (fun n ↦ c * s n) (c * a) := by {
  by_cases hcz : c = 0
  · rw[hcz]
    simp
    unfold SequentialLimit
    intro ε hεp
    use 1
    intro n hn
    simp
    exact hεp
  · intro ε hεp
    have hεc : ε/|c|  > 0 := by
      apply mul_pos
      · assumption
      · refine inv_pos_of_pos ?hb.a
        apply abs_pos.mpr
        apply hcz
    obtain ⟨N, hN⟩ := hs (ε/|c|) hεc
    use N
    intro n hn
    simp
    specialize hN n hn
    have hred := calc
      |c * s n - c * a| = |c*(s n - a)| := by ring
      _ = |c| * |s n - a| := by apply abs_mul
      _ < |c| * (ε/|c|) := by apply mul_lt_mul_of_pos_left hN (abs_pos.mpr hcz)
      _ = ε/|c| * |c| := by ring
      _ = ε := by apply div_mul_cancel₀
                  apply abs_ne_zero.mpr
                  apply hcz -- ask for help unifying this nicer
    exact hred

  }





section Growth

variable {s t : ℕ → ℕ} {k : ℕ}

/- `simp` can help you simplify expressions like the following. -/
example : (fun n ↦ n * s n) k = k * s k := by simp
example (a b c : ℕ) : c ≥ max a b ↔ c ≥ a ∧ c ≥ b := by simp

/- Given two sequences of natural numbers `s` and `t`.
We say that `s` eventually grows faster than `t` if for all `k : ℕ`,
`s_n` will be at least as large as `k * t_n` for large enough `n`. -/
def EventuallyGrowsFaster (s t : ℕ → ℕ) : Prop :=
  ∀ k : ℕ, ∃ N : ℕ, ∀ n ≥ N, k * t n ≤ s n

/- show that `n * s n` grows (eventually) faster than `s n`. -/
lemma eventuallyGrowsFaster_mul_left :
    EventuallyGrowsFaster (fun n ↦ n * s n) s := by {
  sorry
  }

/- Show that if `sᵢ` grows eventually faster than `tᵢ` then
`s₁ + s₂` grows eventually faster than `t₁ + t₂`. -/
lemma eventuallyGrowsFaster_add {s₁ s₂ t₁ t₂ : ℕ → ℕ}
    (h₁ : EventuallyGrowsFaster s₁ t₁) (h₂ : EventuallyGrowsFaster s₂ t₂) :
    EventuallyGrowsFaster (s₁ + s₂) (t₁ + t₂) := by {
  sorry
  }

/- Find a positive function that grows faster than itself when shifted by one. -/
lemma eventuallyGrowsFaster_shift : ∃ (s : ℕ → ℕ),
    EventuallyGrowsFaster (fun n ↦ s (n+1)) s ∧ ∀ n, s n ≠ 0 := by {
  sorry
  }

end Growth

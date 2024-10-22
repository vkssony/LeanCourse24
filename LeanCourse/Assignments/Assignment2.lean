import LeanCourse.Common
import Mathlib.Data.Complex.Exponential
open Real

/-

* From Mathematics in Lean https://leanprover-community.github.io/mathematics_in_lean
  Read chapter 2, sections 2, 3, 4 and 5
  Read chapter 3, sections 1, 4.

* Do the exercises corresponding to these sections in the `LeanCourse/MIL` folder.
  There are solutions in the solution folder in case you get stuck.

* Hand in the solutions to the exercises below. Deadline: 22.10.2023.

* Make sure the file you hand-in compiles without error.
  Use `sorry` if you get stuck on an exercise.
-/

/-! # Exercises to practice. -/

example {a b : ℝ} (h1 : a + 2 * b = 4) (h2 : a - b = 1) : a = 2 := by {
  linarith
  }

example {u v : ℝ} (h1 : u + 1 = v) : u ^ 2 + 3 * u + 1 = v ^ 2 + v - 1 := by {
  rw [←h1]
  ring
  }

example (a b c x y : ℝ) (h : a ≤ b) (h2 : b < c) (h3 : x ≤ y) :
    a + exp x ≤ c + exp (y + 2) := by {
  have hac : a < c := by exact lt_of_le_of_lt h h2
  have hxy : x < y + 2 := by linarith
  gcongr
  }

/-- Prove the following using `linarith`.
Note that `linarith` cannot deal with implication or if and only if statements. -/
example (a b c : ℝ) : a + b ≤ c ↔ a ≤ c - b := by {
  constructor
  · intro
    linarith
  · intro
    linarith
  }

/- Note: for purely numerical problems, you can use `norm_num`
(although `ring` or `linarith` also work in some cases). -/
example : 2 + 3 * 4 + 5 ^ 6 ≤ 7 ^ 8 := by norm_num
example (x : ℝ) : (1 + 1) * x + (7 ^ 2 - 35 + 1) = 2 * x + 15 := by norm_num

/- You can prove many equalities and inequalities by being smart with calculations.
In this case `linarith` can also prove this, but `calc` can be a lot more flexible. -/
example {x y : ℝ} (hx : x + 3 ≤ 2) (hy : y + 2 * x ≥ 3) : y > 3 := by
  calc
    y = y + 2 * x - 2 * x := by ring
    _ ≥ 3 - 2 * x := by gcongr
    _ = 9 - 2 * (x + 3) := by ring
    _ ≥ 9 - 2 * 2 := by gcongr
    _ > 3 := by norm_num

/-- It can be useful to add a `+ 0` in a calculational proof for `gcongr` -/
example {m n : ℤ} : n ≤ n + m ^ 2 := by
  -- gcongr doesn't make progress here
  calc
    n = n + 0 := by ring
    _ ≤ n + m ^ 2 := by gcongr; exact sq_nonneg m

/- Sometimes `congr`/`gcongr` goes too deep into a term.
In that case, you can give `gcongr` a pattern with how deep it should enter the terms.
When the pattern contains `?_`, it creates a subgoal with the corresponding terms
on each side of the inequality.
For `congr` you can also do this using the tactic `congrm`. -/
example {a₁ a₂ b₁ b₂ c₁ c₂ : ℝ} (hab : a₁ + a₂ = b₁ + b₂) (hbc : b₁ + b₂ ≤ c₁ + c₂) :
    a₁ + a₂ + 1 ≤ c₁ + c₂ + 1 := by
  calc a₁ + a₂ + 1 = b₁ + b₂ + 1 := by congrm ?_ + 1; exact hab
    _ ≤ c₁ + c₂ + 1 := by gcongr ?_ + 1 -- gcongr automatically applies `hbc`.


example (x : ℝ) (hx : x = 3) : x ^ 2 + 3 * x - 5 = 13 := by
  rw [hx]
  norm_num

example {m n : ℤ} : n - m ^ 2 ≤ n + 3 := by {
  have h : m ^ 2 ≥ 0 := by exact sq_nonneg m
  have h1 : - m ^ 2 ≤ 0 := by linarith
  calc n - m ^ 2  ≤ n - 0 := by linarith
                _ ≤ n + 3 := by linarith
  }

example {a : ℝ} (h : ∀ b : ℝ, a ≥ -3 + 4 * b - b ^ 2) : a ≥ 1 := by {
  calc a >= -3 + 4*2 - 2^2 := by apply h
        _ = 1 := by norm_num
  }

example {a₁ a₂ a₃ b₁ b₂ b₃ : ℝ} (h₁₂ : a₁ + a₂ + 1 ≤ b₁ + b₂) (h₃ : a₃ + 2 ≤ b₃) :
  exp (a₁ + a₂) + a₃ + 1 ≤ exp (b₁ + b₂) + b₃ + 1 := by {
  have h3 : a₁ + a₂ ≤ a₁ + a₂ + 1 := by norm_num
  have h4 : a₃ ≤ a₃ + 2 := by norm_num
  calc exp (a₁ + a₂) + a₃ + 1 ≤ exp (a₁ + a₂ + 1) + a₃ + 1 := by gcongr
                            _ ≤ exp (b₁ + b₂) + a₃ + 1 := by gcongr
                            _ ≤ exp (b₁ + b₂) + b₃ + 1 := by linarith
  }


/- Divisibility also gives an order. Warning: divisibility uses a unicode character,
which can be written using `\|`. -/

/-- Prove this using calc. -/
lemma exercise_division (n m k l : ℕ) (h₁ : n ∣ m) (h₂ : m = k) (h₃ : k ∣ l) : n ∣ l := by {
  rcases h₃ with ⟨a, da⟩
  rcases h₁ with ⟨b, db⟩
  use a * b
  calc l  = k * a := by rw [←da]
        _ = m * a := by rw [h₂]
        _ = (n * b) * a := by rw [← db]
        _ = n * (a * b) := by ring
  }


/- We can also work with abstract partial orders. -/

section PartialOrder

variable {X : Type*} [PartialOrder X]
variable (x y z : X)

/- A partial order is defined to be an order relation `≤` with the following axioms -/
#check x ≤ y
#check (le_refl x : x ≤ x)
#check (le_trans : x ≤ y → y ≤ z → x ≤ z)
#check (le_antisymm : x ≤ y → y ≤ x → x = y)

/- every preorder comes automatically with an associated strict order -/
example : x < y ↔ x ≤ y ∧ x ≠ y := lt_iff_le_and_ne

/- the reverse order `≥`/`>` is defined from `≤`/`<`.
In Mathlib we usually state lemmas using `≤`/`<` instead of `≥`/`>`. -/
example : x ≥ y ↔ y ≤ x := by rfl
example : x > y ↔ y < x := by rfl


example (hxy : x ≤ y) (hyz : y ≤ z) (hzx : z ≤ x) : x = y ∧ y = z ∧ x = z := by {
  sorry
  -- have hyx : y ≤ x := by exact Preorder.le_trans y z x hyz hzx
  -- have hzy : z ≤ y := by exact Preorder.le_trans z x y hzx hxy
  -- have h1 : x = y := by apply le_antisymm hxy hyx

  }


end PartialOrder


/-! # Exercises to hand-in. -/

/- Prove this using a calculation. -/
lemma exercise_calc_real {t : ℝ} (ht : t ≥ 10) : t ^ 2 - 3 * t - 17 ≥ 5 := by {
  calc t^2-3*t-17 = (t-10)^2 + 20*t - 100 -3*t -17 := by ring
  _ = (t-10)^2 + (20-3)*t + (-100-17) := by ring
  _ = (t-10)^2 + 17*t + (-117) := by norm_num
  _ ≥ (t-10)^2 + 170 + (-117) := by linarith
  _ ≥ 0 + 170 + (-117) := by gcongr; apply sq_nonneg
  _ ≥ 5 := by norm_num
  }

/- Prove this using a calculation.
The arguments `{R : Type*} [CommRing R] {t : R}` mean
"let `t` be an element of an arbitrary commutative ring `R`." -/
lemma exercise_calc_ring {R : Type*} [CommRing R] {t : R}
    (ht : t ^ 2 - 4 = 0) :
    t ^ 4 + 3 * t ^ 3 - 3 * t ^ 2 - 2 * t - 2 = 10 * t + 2 := by {
  calc t ^ 4 + 3 * t ^ 3 - 3 * t ^ 2 - 2 * t - 2 = (t^2-4+4)^2 + 3*t*(t^2-4+4)-3*(t^2-4+4)-2*t-2 := by ring
  _ = (0+4)^2+3*t*(0+4)-3*(0+4)-2*t-2 := by rw[ht]
  _ = 16 + 3 * t * 4 - 12 - 2 * t -2 := by norm_num
  _ = (3*4-2)*t +(16 -12 -2) := by ring
  _ = 10 * t +2 := by norm_num

  }

/-- Prove this using a calculation. -/
lemma exercise_square {m n k : ℤ} (h : m ^ 2 + n ≤ 2) : n + 1 ≤ 3 + k ^ 2 := by {
  calc n + 1 = - m^2 + (m^2 + n) +1 := by ring
  _ ≤ -m^2 + 2+ 1 := by gcongr -m^2 + ?_ + 1;
  _ ≤ -0 + 2 + 1 := by gcongr; exact sq_nonneg m
  _ ≤ 3 + 0:= by norm_num
  _ ≤ 3 + k^2 := by gcongr; exact sq_nonneg k
  }



section Min
variable (a b c : ℝ)

/- The following theorems characterize `min`.
Let's this characterization it to prove that `min` is commutative and associative.
Don't use other lemmas about `min` from Mathlib! -/
#check (min : ℝ → ℝ → ℝ)
#check (min_le_left a b : min a b ≤ a)
#check (min_le_right a b : min a b ≤ b)
#check (le_min : c ≤ a → c ≤ b → c ≤ min a b)

lemma exercise_min_comm : min a b = min b a := by {
  have h1 : min a b ≤ min b a := by apply le_min (min_le_right a b) (min_le_left a b)
  have h2 : min b a ≤ min a b := by apply le_min (min_le_right b a) (min_le_left b a)
  exact le_antisymm h1 h2
  }

lemma exercise_min_assoc : min a (min b c) = min (min a b) c := by {
  have h11 : min a (min b c) ≤ min a b := by apply le_min (min_le_left a (min b c)) (le_trans (min_le_right a (min b c)) (min_le_left b c))
  have h12 : min a (min b c) ≤ c := by apply le_trans (min_le_right a (min b c)) (min_le_right b c)
  have h1 : min a (min b c) ≤ min (min a b) c := by apply le_min h11 h12

  have h21 : min (min a b) c ≤ a := by apply le_trans (min_le_left (min a b) c) (min_le_left a b)
  have h22 : min (min a b) c ≤ min b c := by apply le_min (le_trans (min_le_left (min a b) c) (min_le_right a b)) (min_le_right (min a b) c)
  have h2 : min (min a b) c ≤ min a (min b c) := by apply le_min h21 h22

  exact le_antisymm h1 h2
  }

end Min

/- Prove that the following function is continuous.
You can use `Continuous.div` as the first step,
and use the search techniques to find other relevant lemmas.
`ne_of_lt`/`ne_of_gt` will be useful to prove the inequality. -/
lemma exercise_continuity : Continuous (fun x ↦ (sin (x ^ 5) * cos x) / (x ^ 2 + 1)) := by {

  have h1 : (0 : ℝ) < (1 : ℝ) := by norm_num

  apply Continuous.div
  · apply Continuous.mul
    · apply Continuous.comp'
      · exact continuous_sin
      · exact continuous_pow 5
    · exact continuous_cos
  · apply Continuous.add
    · exact continuous_pow 2
    · exact continuous_const
  · intro x
    have h2 : x ^ 2 + 1 > 0 := by {
      calc x ^ 2 + 1  ≥ 0 + 1 := by rel [sq_nonneg x]
                    _ > 0 + 0 := by rel [h1]
                    _ = 0 := by ring
    }
    apply ne_of_gt h2
  }

/- Prove this only using `intro`/`constructor`/`obtain`/`exact` -/
lemma exercise_and_comm : ∀ (p q : Prop), p ∧ q ↔ q ∧ p := by {
  intro p q
  constructor
  · intro hpq
    · obtain ⟨hp, hq⟩ := hpq
      · constructor
        · exact hq
        · exact hp
  · intro hqp
    · obtain ⟨hq, hp⟩ := hqp
      · constructor
        · exact hp
        · exact hq

  }


/-- Prove the following properties of nondecreasing functions. -/
def Nondecreasing (f : ℝ → ℝ) : Prop := ∀ x₁ x₂ : ℝ, x₁ ≤ x₂ → f x₁ ≤ f x₂

lemma exercise_nondecreasing_comp (f g : ℝ → ℝ) (hg : Nondecreasing g) (hf : Nondecreasing f) :
    Nondecreasing (g ∘ f) := by {
  unfold Nondecreasing
  intro x y
  intro hxy
  unfold Nondecreasing at hf hg
  have h1 : f x ≤ f y := by exact hf x y hxy
  calc (g ∘ f) x  = g (f x) := by exact rfl
                _ ≤ g (f y) := by exact hg (f x) (f y) h1
                _ = (g ∘ f) y := by exact rfl
  }


/-- Note: `f + g` is the function defined by `(f + g)(x) := f(x) + g(x)`.
  `simp` can simplify `(f + g) x` to `f x + g x`. -/
lemma exercise_nondecreasing_add (f g : ℝ → ℝ) (hf : Nondecreasing f) (hg : Nondecreasing g) :
    Nondecreasing (f + g) := by {
  unfold Nondecreasing
  intro x y
  unfold Nondecreasing at hf hg
  intro hxy
  calc (f + g) x = f x + g x := by exact rfl
                _ ≤ f y + g x := by apply add_le_add_right (hf x y hxy)
                _ ≤ f y + g y := by apply add_le_add_left (hg x y hxy)
                _ = (f + g) y := by exact rfl
  }



/-- Prove the following property of even. -/
def EvenFunction (f : ℝ → ℝ) : Prop :=
  ∀ x, f x = f (-x)

lemma exercise_even_iff (f g : ℝ → ℝ) (hf : EvenFunction f) :
    EvenFunction (f + g) ↔ EvenFunction g := by {
  unfold EvenFunction
  simp
  unfold EvenFunction at hf
  constructor
  · intro hfg
    intro x
    obtain hfgx := hfg x
    obtain hfx := hf x
    rw[hfx] at hfgx
    apply add_left_cancel at hfgx
    exact hfgx
  · intro hg
    intro x
    obtain hfx := hf x
    obtain hgx := hg x
    rw[hfx, hgx]
  }

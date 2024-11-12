import LeanCourse.Common
import Mathlib.Data.Complex.Exponential
noncomputable section
open Real Function Nat BigOperators Set Finset
open Classical


/-

* From Mathematics in Lean https://leanprover-community.github.io/mathematics_in_lean
  Read chapters 5 (mostly section 2) and 6 (mostly sections 1 and 2).

* Do the exercises corresponding to these sections in the `LeanCourse/MIL` folder.
  There are solutions in the solution folder in case you get stuck.

* Hand in the solutions to the exercises under "Exercises to hand-in". Deadline: 12.11.

* Make sure the file you hand-in compiles without error.
  Use `sorry` if you get stuck on an exercise.
-/


/-! # Exercises to practice. -/

/- A note on definitions -/

lemma my_lemma : 3 + 1 = 4 := rfl
def myThree : ℕ := 3

/-
Tactics like `simp` and `rw` will not unfold definitions unless instructed to.
Tactics like `exact` and `apply` will unfold definitions if needed.
Uncomment the following lines one-by-one to see the difference. -/

example : myThree + 1 = 4 := by
  -- rw [my_lemma] -- fails
  -- simp [my_lemma] -- fails to use `my_lemma`
  -- exact my_lemma -- works
  -- apply my_lemma -- works
  -- rw [myThree, my_lemma] -- works after instructing `rw` to unfold the definition
  -- simp [myThree] -- works after instructing `simp` to unfold the definition
                    -- (it doesn't need `my_lemma` to then prove the goal)
  sorry


/- The following exercises are to practice with casts. -/
example (n : ℤ) (h : (n : ℚ) = 3) : 3 = n := by {
  sorry
  }

example (n m : ℕ) (h : (n : ℚ) + 3 ≤ 2 * m) : (n : ℝ) + 1 < 2 * m := by {
  sorry
  }

example (n m : ℕ) (h : (n : ℚ) = m ^ 2 - 2 * m) : (n : ℝ) + 1 = (m - 1) ^ 2 := by {
  sorry
  }

example (n m : ℕ) : (n : ℝ) < (m : ℝ) ↔ n < m := by {
  sorry
  }

example (n m : ℕ) (hn : 2 ∣ n) (h : n / 2 = m) : (n : ℚ) / 2 = m := by {
  sorry
  }

example (q q' : ℚ) (h : q ≤ q') : exp q ≤ exp q' := by {
  sorry
  }

example (n : ℤ) (h : 0 < n) : 0 < Real.sqrt n := by {
  sorry
  }

/- Working with `Finset` is very similar to working with `Set`.
However, some notation, such as `f '' s` or `𝒫 s` doesn't exist for `Finset`. -/
example (s t : Finset ℕ) : (s ∪ t) ∩ t = (s ∩ t) ∪ t := by {
  sorry
  }

example {α β : Type*} (f : α → β) (s : Finset α) (y : β) : y ∈ s.image f ↔ ∃ x ∈ s, f x = y := by {
  sorry
  }

/- `Disjoint` can be used to state that two (fin)sets are disjoint.
Use `Finset.disjoint_left` (or `Set.disjoint_left`) to unfold its definition.
If you have `x ∈ t \ s` apply `simp` first to get a conjunction of two conditions.
-/
example {α : Type*} (s t : Finset α) : Disjoint s (t \ s) := by {
  sorry
  }


/- Let's define the Fibonacci sequence -/
def fibonacci : ℕ → ℕ
  | 0 => 0
  | 1 => 1
  | (n + 2) => fibonacci (n + 1) + fibonacci n

/- Prove the following exercises by induction. -/

example (n : ℕ) : ∑ i in range n, fibonacci (2 * i + 1) = fibonacci (2 * n) := by {
  sorry
  }

example (n : ℕ) : ∑ i in range n, (fibonacci i : ℤ) = fibonacci (n + 1) - 1 := by {
  sorry
  }

example (n : ℕ) : 6 * ∑ i in range (n + 1), i ^ 2 = n * (n + 1) * (2 * n + 1) := by {
  sorry
  }

def fac : ℕ → ℕ
  | 0       => 1
  | (n + 1) => (n + 1) * fac n

theorem pow_two_le_fac (n : ℕ) : 2 ^ n ≤ fac (n + 1) := by {
  sorry
  }

example (n : ℕ) : fac n = ∏ i in range n, (i + 1) := by {
  sorry
  }

example (n : ℕ) : fac (2 * n) = fac n * 2 ^ n * ∏ i in range n, (2 * i + 1) := by {
  sorry
  }





/- **Exercise**.
Define scalar multiplication of a real number and a `Point`. -/

@[ext] structure Point where
  x : ℝ
  y : ℝ
  z : ℝ

-- give definition here


/- **Exercise**.Define Pythagorean triples, i.e. triples `a b c : ℕ` with `a^2 + b^2 = c^2`.
Give an example of a Pythagorean triple, and show that multiplying a Pythagorean triple by a
constant gives another Pythagorean triple. -/

-- give definition here



/- Prove that triples of equivalent types are equivalent. -/

@[ext] structure Triple (α : Type*) where
  x : α
  y : α
  z : α

example (α β : Type*) (e : α ≃ β) : Triple α ≃ Triple β := sorry



/- 5. Show that if `G` is an abelian group then triples from elements of `G` is an abelian group. -/

class AbelianGroup' (G : Type*) where
  add (x : G) (y : G) : G
  comm (x y : G) : add x y = add y x
  assoc (x y z : G) : add (add x y) z = add x (add y z)
  zero : G
  add_zero : ∀ x : G, add x zero = x
  neg : G → G
  add_neg : ∀ x : G, add x (neg x) = zero

example (G : Type*) [AbelianGroup' G] : AbelianGroup' (Triple G) := sorry



/-! # Exercises to hand-in. -/

/- **Exercise**.
Define the structure of "strict bipointed types", i.e. a type together with 2 unequal points
`x₀ ≠ x₁` in it.
Then state and prove the lemma that for any element of a strict bipointed type we have
`∀ z, z ≠ x₀ ∨ z ≠ x₁.` -/

-- give the definition here

@[ext] structure StrictBipointedType (α : Type*) where
  x₀ : α
  x₁ : α
  noteq : x₀ ≠ x₁


#check StrictBipointedType
-- state and prove the lemma here
lemma SBT_disjunction (α : Type*) (x : StrictBipointedType α) : ∀ z, z ≠ x.x₀ ∨ z ≠ x.x₁ := by {
  intro z
  by_cases h : z = x.x₀
  · right; subst z
    exact x.noteq
  · tauto

}



/- Prove by induction that `∑_{i = 0}^{n} i^3 = (∑_{i=0}^{n} i) ^ 2`. -/
open Finset in

lemma gauss_sum (n : ℕ) : ∑ i in range (n + 1), (i : ℚ) = n * (n + 1) / 2 := by {
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, ih]
    field_simp
    ring
  }

lemma sum_cube_eq_sq_sum (n : ℕ) :
    (∑ i in range (n + 1), (i : ℚ) ^ 3) = (∑ i in range (n + 1), (i : ℚ)) ^ 2 := by {
  induction n with
  | zero => simp
  | succ n ih =>
    rw[sum_range_succ (fun x ↦ (x ^ 3 : ℚ)) (n+1), sum_range_succ (fun x ↦ (x : ℚ))]
    rw[add_pow_two, ih, add_assoc, add_left_cancel_iff, gauss_sum]
    norm_cast
    ring
    norm_cast
    ring
  }

/-
Suppose `(A i)_i` is a sequence of sets indexed by a well-ordered type
(this is an order where every nonempty set has a minimum element).
We now define a new sequence by `C n = A n \ (⋃ i < n, A i)`.
In this exercise, we show that the new sequence is pairwise disjoint but has the same union as the
original sequence.
-/
lemma disjoint_unions {ι α : Type*} [LinearOrder ι] [wf : WellFoundedLT ι] (A C : ι → Set α)
  (hC : ∀ i, C i = A i \ ⋃ j < i, A j) : Pairwise (Disjoint on C) ∧ ⋃ i, C i = ⋃ i, A i := by {
  have h := wf.wf.has_min -- this hypothesis allows you to use well-orderedness
  constructor
  · intro i j hij
    unfold Disjoint
    simp
    intro hnull hnull1 hnull2
    ext x
    constructor
    · have hci : C i = A i \ ⋃ k < i, A k := by exact hC i
      have hcj : C j = A j \ ⋃ k < j, A k := by exact hC j
      intro hx
      specialize hnull1 hx
      specialize hnull2 hx
      rw[hci] at hnull1
      rw[hcj] at hnull2
      obtain ⟨hxai, hxanoti⟩ := hnull1
      obtain ⟨hxaj, hxanotj⟩ := hnull2
      by_cases hiltj : i < j
      · apply hxanotj
        exact Set.mem_biUnion hiltj hxai
      · have hjltj : j < i := by
          apply LE.le.lt_of_ne
          · exact not_lt.mp hiltj
          · tauto
        apply hxanoti
        exact Set.mem_biUnion hjltj hxaj
    · tauto
  · ext x
    constructor
    · intro hx
      obtain ⟨aj, haj1, haj2⟩ := hx
      simp at haj1
      obtain ⟨y, hy⟩ := haj1
      specialize hC y
      subst aj
      rw[hC] at haj2
      obtain ⟨hxay, hxanot⟩ := haj2
      exact mem_iUnion_of_mem y hxay
    · intro hx
      simp at hx
      obtain ⟨i, hi⟩ := hx
      let g := {i : ι | x ∈ A i}
      have gnemp : g.Nonempty := nonempty_of_mem hi
      specialize h g gnemp
      obtain ⟨a, ha1, ha2⟩ := h
      simp
      use a
      specialize hC a
      rw[hC]
      simp
      constructor
      · exact ha1
      · exact fun x_1 a a_1 ↦ ha2 x_1 a_1 a



  }



/- Next, we'll prove that if `2 ^ n - 1` is prime, then `n` is prime.
The first exercise is a preparation, and I've given you a skeleton of the proof for the
second exercise. Note how we do some computations in the integers, since the subtraction on `ℕ`
is less well-behaved.
(The converse is not true, because `89 ∣ 2 ^ 11 - 1`) -/

lemma not_prime_iff (n : ℕ) :
    ¬ Nat.Prime n ↔ n = 0 ∨ n = 1 ∨ ∃ a b : ℕ, 2 ≤ a ∧ 2 ≤ b ∧ n = a * b := by {
  constructor
  · intro h
    by_cases hzero_one : n = 0 ∨ n = 1
    · rw[← or_assoc]; left; assumption
    · push_neg at hzero_one
      right; right
      contrapose! h
      have ngeq2: n ≥ 2 := (two_le_iff n).mpr hzero_one
      apply Nat.prime_def_lt'.mpr
      constructor
      · exact ngeq2
      · intro m hm1 hm2 mdvd
        specialize h m
        have hmprop : m ∈ n.properDivisors := Nat.mem_properDivisors.mpr ⟨mdvd,hm2⟩
        obtain ⟨d, mfac⟩ := mdvd
        have hmn : n/m = d := by
          apply Nat.div_eq_of_eq_mul_right
          linarith; assumption
        have hnm1 : 1 < n/m := Nat.one_lt_div_of_mem_properDivisors hmprop
        have dgeq2 : d ≥ 2 := by
          rw[hmn] at hnm1
          exact hnm1
        specialize h d hm1 dgeq2
        contradiction
  · rintro (hn0|hn1|⟨a,b,ha,hb,hab⟩)
    · intro np
      rw[hn0] at np
      exact Nat.not_prime_zero np
    · intro np
      rw[hn1] at np
      exact Nat.not_prime_one np
    · intro np
      have a_dvd_n : a∣n := by exact Dvd.intro b (id (Eq.symm hab))
      have b_dvd_n : b∣n := by exact Dvd.intro_left a (id (Eq.symm hab))
      have aeqn : a = n := (dvd_prime_two_le np ha).mp a_dvd_n
      have beqn : b = n := (dvd_prime_two_le np hb).mp b_dvd_n
      rw[aeqn, beqn] at hab
      have n01 : n = 0 ∨ n = 1 := by
        apply eq_zero_or_one_of_sq_eq_self
        exact IsIdempotentElem.pow_succ_eq 1 (id (Eq.symm hab))
      have nneq01 : n ≠ 1 ∧ n ≠ 0 :=  ⟨Nat.Prime.ne_one np, Nat.Prime.ne_zero np⟩
      tauto






  }

lemma prime_of_prime_two_pow_sub_one (n : ℕ) (hn : Nat.Prime (2 ^ n - 1)) : Nat.Prime n := by {
  by_contra h2n
  rw [not_prime_iff] at h2n
  obtain rfl|rfl|⟨a, b, ha, hb, rfl⟩ := h2n
  · norm_num at hn
  · norm_num at hn
  have h : (2 : ℤ) ^ a - 1 ∣ (2 : ℤ) ^ (a * b) - 1
  · rw [← Int.modEq_zero_iff_dvd]
    calc (2 : ℤ) ^ (a * b) - 1
        ≡ ((2 : ℤ) ^ a) ^ b - 1 [ZMOD (2 : ℤ) ^ a - 1] := by
          apply Int.ModEq.add_right
          rw[pow_mul]
      _ ≡ (1 : ℤ) ^ b - 1 [ZMOD (2 : ℤ) ^ a - 1] := by
          apply Int.ModEq.add_right
          apply Int.ModEq.pow
          apply Int.ModEq.add_right_cancel' (-1 : ℤ )

      _ ≡ 0 [ZMOD (2 : ℤ) ^ a - 1] := by simp
  have h2 : 2 ^ 2 ≤ 2 ^ a := by refine pow_le_pow_of_le_right ?hx ha; norm_num
  have h3 : 1 ≤ 2 ^ a := by norm_num at h2; linarith
  have h4 : 2 ^ a - 1 ≠ 1 := by zify; simp [h3]; linarith
  have h5 : 2 ^ a - 1 < 2 ^ (a * b) - 1 := by
    apply tsub_lt_tsub_right_of_le h3
    apply Nat.pow_lt_pow_of_lt
    norm_num
    apply (Nat.lt_mul_iff_one_lt_right ?w.ha).mpr hb
    linarith
  have h6' : 2 ^ 0 ≤ 2 ^ (a * b) := by
    refine pow_le_pow_of_le_right ?twozero ?hab
    norm_num
    exact Nat.zero_le (a * b)
  have h6 : 1 ≤ 2 ^ (a * b) := h6'
  have h' : 2 ^ a - 1 ∣ 2 ^ (a * b) - 1 := by norm_cast at h
  rw [Nat.prime_def_lt] at hn
  obtain ⟨hn2ab, hprime⟩ := hn
  specialize hprime (2 ^ a - 1) h5 h'
  contradiction
  }

/- Prove that for positive `a` and `b`, `a^2 + b` and `b^2 + a` cannot both be squares.
Prove it on paper first! -/
lemma not_isSquare_sq_add_or (a b : ℕ) (ha : 0 < a) (hb : 0 < b) :
    ¬ IsSquare (a ^ 2 + b) ∨ ¬ IsSquare (b ^ 2 + a) := by {
      by_contra! h
      -- obtain ⟨a2bsq, b2asq⟩ := h
      -- unfold IsSquare at a2bsq b2asq

      have hneq : ∀ x > 0, ∀ y ≥ x, ¬ (IsSquare (x ^ 2 + y) ∧ IsSquare (y ^ 2 + x) ):= by
        intro x hx y hy
        have hsq1: y * y < x + y ^ 2:= by linarith
        have hsq2 : x + y ^ 2 < (y + 1) * (y + 1) := by linarith
        rw[not_and_or]
        right
        unfold IsSquare
        rw[add_comm]
        have hneg : ¬∃ t, t * t = x + y ^ 2 := Nat.not_exists_sq hsq1 hsq2
        intro hr
        obtain ⟨r, hr2⟩ := hr
        apply hneg
        use r
        symm
        exact hr2
      by_cases hab : a ≤ b
      · specialize hneq a ha b hab
        contradiction
      · have hab2 : b ≤ a := by linarith
        specialize hneq b hb a hab2
        symm at h
        contradiction

  }


/-- Let's prove that the positive reals form a group under multiplication.
Note: in this exercise `rw` and `simp` will not be that helpful, since the definition is hidden
behind notation. But you can use apply to use the lemmas about real numbers. -/

abbrev PosReal : Type := {x : ℝ // 0 < x}

def groupPosReal : Group PosReal where
  inv x := by
    unfold PosReal
    obtain ⟨a, ha⟩ := x
    use a⁻¹
    exact inv_pos_of_pos ha
  inv_mul_cancel a := by
    unfold PosReal at a
    obtain ⟨x,hx⟩ := a
    refine Eq.symm (Subtype.eq ?mk.a)
    simp
    refine (eq_inv_mul_iff_mul_eq₀ ?mk.a.hb).mpr ?mk.a.a
    · linarith
    · ring




/-
Compute by induction the cardinality of the powerset of a finite set.

Hints:
* Use `Finset.induction` as the induction principle, using the following pattern:
```
  induction s using Finset.induction with
  | empty => sorry
  | @insert x s hxs ih => sorry
```
* You will need various lemmas about the powerset, search them using Loogle.
  The following queries will be useful for the search:
  `Finset.powerset, insert _ _`
  `Finset.card, Finset.image`
  `Finset.card, insert _ _`
* As part of the proof, you will need to prove an injectivity condition
  and a disjointness condition.
  Separate these out as separate lemmas or state them using `have` to break up the proof.
* Mathlib already has `card_powerset` as a simp-lemma, so we remove it from the simp-set,
  so that you don't actually simplify with that lemma.
-/
attribute [-simp] card_powerset
#check Finset.induction
#check Finset.image
#check Finset.instInsert
#check Insert
#check insert

lemma fintype_card_powerset (α : Type*) (s : Finset α) :
    Finset.card (powerset s) = 2 ^ Finset.card s := by {
  induction s using Finset.induction with
  | empty =>
    simp[Finset.card_empty, Finset.powerset_empty]
  | @insert x s hxs ih =>
    simp[Finset.powerset_insert, Finset.card_union]
    have hdisj : s.powerset ∩ Finset.image (insert x) s.powerset = ∅ := by
      ext a
      constructor
      · simp
        rintro has y hy hnot
        have hxina : x ∈ a := by
          rw[← hnot]
          exact mem_insert_self x y
        have hxscontra : x ∈ s := by exact has hxina
        contradiction
      · tauto
    have hinj : InjOn (insert x) (s.powerset : Set (Finset α)) := by
      rintro a ha b hb hab
      simp at ha hb
      ext z
      constructor
      · intro haz
        have hz_ins : z ∈ insert x a := Finset.mem_insert_of_mem haz
        rw[hab] at hz_ins
        have zneqx : z ≠ x := by exact ne_of_mem_of_not_mem (ha haz) hxs
        exact Finset.mem_of_mem_insert_of_ne hz_ins zneqx
      · intro hbz
        have hz_ins : z ∈ insert x b := Finset.mem_insert_of_mem hbz
        rw[← hab] at hz_ins
        have zneqx : z ≠ x := by exact ne_of_mem_of_not_mem (hb hbz) hxs
        exact Finset.mem_of_mem_insert_of_ne hz_ins zneqx
    rw[hdisj, Finset.card_image_of_injOn hinj]
    simp[Finset.card_insert_of_not_mem hxs, ih]
    ring
  }

/- Copyright (c) Heather Macbeth, 2023.  All rights reserved. -/
import Mathlib.Data.Real.Basic
import Library.Basic
import Library.Tactic.Rel

math2001_init
set_option pp.funBinderTypes true


example (P Q : Prop) : ¬ (P ∧ Q) ↔ (¬ P ∨ ¬ Q) := by
  constructor
  · intro h
    by_cases hP : P
    · right
      intro hQ
      have hPQ : P ∧ Q
      · constructor
        · apply hP
        · apply hQ
      contradiction
    · left
      apply hP
  · intro h
    obtain h1|h2:=h
    · intro ⟨h3,h4⟩
      contradiction
    · intro ⟨h3,h4⟩
      contradiction

example :
    ¬(∀ m : ℤ, m ≠ 2 → ∃ n : ℤ, n ^ 2 = m) ↔ ∃ m : ℤ, m ≠ 2 ∧ ∀ n : ℤ, n ^ 2 ≠ m :=
  calc ¬(∀ m : ℤ, m ≠ 2 → ∃ n : ℤ, n ^ 2 = m)
      ↔ ∃ m : ℤ, ¬(m ≠ 2 → ∃ n : ℤ, n ^ 2 = m) := by rel [not_forall]
    _ ↔ ∃ m : ℤ, m ≠ 2 ∧ ¬(∃ n : ℤ, n ^ 2 = m) := by rel [not_imp]
    _ ↔ ∃ m : ℤ, m ≠ 2 ∧ ∀ n : ℤ, n ^ 2 ≠ m := by rel [not_exists]


example : ¬(∀ n : ℤ, ∃ m : ℤ, n ^ 2 < m ∧ m < (n + 1) ^ 2)
    ↔ ∃ n : ℤ, ∀ m : ℤ, n ^ 2 ≥ m ∨ m ≥ (n + 1) ^ 2 :=
  calc
    ¬(∀ n : ℤ, ∃ m : ℤ, n ^ 2 < m ∧ m < (n + 1) ^ 2) ↔ ∃ n : ℤ, ¬(∃ m : ℤ, n ^ 2 < m ∧ m < (n + 1) ^ 2) := by rel [not_forall]
    _↔∃ n : ℤ,∀ m : ℤ,¬(n ^ 2 < m ∧ m < (n + 1) ^ 2):=by rel[not_exists]
    _↔∃ n : ℤ,∀ m : ℤ,(¬(n ^ 2 < m)∨¬(m < (n + 1) ^ 2)):=by rel[not_and_or]
    _↔∃ n : ℤ,∀ m : ℤ, n ^ 2 ≥ m ∨ m ≥ (n + 1) ^ 2:=by rel[not_lt]

#push_neg ¬(∀ m : ℤ, m ≠ 2 → ∃ n : ℤ, n ^ 2 = m)
  -- ∃ m : ℤ, m ≠ 2 ∧ ∀ (n : ℤ), n ^ 2 ≠ m

#push_neg ¬(∀ n : ℤ, ∃ m : ℤ, n ^ 2 < m ∧ m < (n + 1) ^ 2)
  -- ∃ n : ℤ, ∀ m : ℤ, m ≤ n ^ 2 ∨ (n + 1) ^ 2 ≤ m


#push_neg ¬(∃ m n : ℤ, ∀ t : ℝ, m < t ∧ t < n)
#push_neg ¬(∀ a : ℕ, ∃ x y : ℕ, x * y ∣ a → x ∣ a ∧ y ∣ a)
#push_neg ¬(∀ m : ℤ, m ≠ 2 → ∃ n : ℤ, n ^ 2 = m)


example : ¬ (∃ n : ℕ, n ^ 2 = 2) := by
  push_neg
  intro n
  have hn := le_or_succ_le n 1
  obtain hn | hn := hn
  · apply ne_of_lt
    calc
      n ^ 2 ≤ 1 ^ 2 := by rel [hn]
      _ < 2 := by numbers
  · apply ne_of_gt
    calc
      2<2^2:=by numbers
      _<=n^2:=by rel[hn]


/-! # Exercises -/


example (P : Prop) : ¬ (¬ P) ↔ P := by
  constructor
  · intro h
    by_cases h1:P
    · apply h1
    · contradiction
  · intro H h1
    contradiction

example (P Q : Prop) : ¬ (P → Q) ↔ (P ∧ ¬ Q) := by
  constructor
  · intro h1
    constructor
    · by_cases h2:P
      · apply h2
      · have h3:P->Q
        · intro h4
          contradiction
        contradiction
    · by_cases h2:Q
      · have h3:P->Q
        · intro h4
          apply h2
        contradiction
      · apply h2
  · intro h1
    obtain ⟨h2,h3⟩:=h1
    intro h4
    have h5: Q := h4 h2
    contradiction


example (P : α → Prop) : ¬ (∀ x, P x) ↔ ∃ x, ¬ P x := by
  constructor
  · intro h1
    by_cases h2: (∃ x, ¬ P x)
    · apply h2
    · have h3: (∀ x, P x)
      · intro x
        by_cases h4: P x
        · apply h4
        · have h5: (∃ x, ¬ P x)
          · use x
            apply h4
          contradiction
      contradiction
  · intro⟨x,h1⟩
    intro h2
    have h3:P x:=h2 x
    contradiction


example : (¬ ∀ a b : ℤ, a * b = 1 → a = 1 ∨ b = 1)
    ↔ ∃ a b : ℤ, a * b = 1 ∧ a ≠ 1 ∧ b ≠ 1 :=
  calc (¬ ∀ a b : ℤ, a * b = 1 → a = 1 ∨ b = 1)
      ↔ ∃ a : ℤ, ¬ (∀ b : ℤ, a * b = 1 → a = 1 ∨ b = 1):=by rel[not_forall]
    _ ↔ ∃ a b : ℤ, ¬ (a * b = 1 → a = 1 ∨ b = 1):=by rel[not_forall]
    _ ↔ ∃ a b : ℤ, a * b = 1 ∧ ¬(a = 1 ∨ b = 1):=by rel[not_imp]
    _ ↔ ∃ a b : ℤ, a * b = 1 ∧ a ≠ 1 ∧ b ≠ 1:=by rel[not_or]


example : (¬ ∃ x : ℝ, ∀ y : ℝ, y ≤ x) ↔ (∀ x : ℝ, ∃ y : ℝ, y > x) :=
  calc (¬ ∃ x : ℝ, ∀ y : ℝ, y ≤ x)
      ↔ ∀ x : ℝ, ¬(∀ y : ℝ, y ≤ x) := by rel[not_exists]
    _ ↔ ∀ x : ℝ, ∃ y : ℝ, ¬(y ≤ x) := by rel[not_forall]
    _ ↔ ∀ x : ℝ, ∃ y : ℝ, y > x := by rel[not_le]

example : ¬ (∃ m : ℤ, ∀ n : ℤ, m = n + 5) ↔ ∀ m : ℤ, ∃ n : ℤ, m ≠ n + 5 :=
  calc ¬ (∃ m : ℤ, ∀ n : ℤ, m = n + 5)
      ↔ ∀ m : ℤ, ¬(∀ n : ℤ, m = n + 5) := by rel[not_exists]
    _ ↔ ∀ m : ℤ, ∃ n : ℤ, m ≠ n + 5 := by rel[not_forall]

#push_neg ¬(∀ n : ℕ, n > 0 → ∃ k l : ℕ, k < n ∧ l < n ∧ k ≠ l)
#push_neg ¬(∀ m : ℤ, m ≠ 2 → ∃ n : ℤ, n ^ 2 = m)
#push_neg ¬(∃ x : ℝ, ∀ y : ℝ, ∃ m : ℤ, x < y * m ∧ y * m < m)
#push_neg ¬(∃ x : ℝ, ∀ q : ℝ, q > x → ∃ m : ℕ, q ^ m > x)


example : ¬ (∀ x : ℝ, x ^ 2 ≥ x) := by
  push_neg
  use 0.5
  numbers

example : ¬ (∃ t : ℝ, t ≤ 4 ∧ t ≥ 5) := by
  push_neg
  intro t
  obtain h1|h1:=le_or_lt t 4
  · right
    addarith[h1]
  · left
    apply h1

example : ¬ Int.Even 7 := by
  dsimp [Int.Even]
  push_neg
  intro k
  obtain h1|h1:=le_or_succ_le k 3
  · apply ne_of_gt
    calc 2*k<=2*3:=by rel[h1]
      _<7:=by numbers
  · apply ne_of_lt
    calc 7<2*4:=by numbers
      _<=2*k:=by rel[h1]

example {p : ℕ} (k : ℕ) (hk1 : k ≠ 1) (hkp : k ≠ p) (hk : k ∣ p) : ¬ Prime p := by
  dsimp [Prime]
  push_neg
  obtain h1|h1:=le_or_succ_le p 1
  · left
    addarith[h1]
  · right
    use k
    constructor
    · apply hk
    · constructor
      · apply hk1
      · apply hkp

example : ¬ ∃ a : ℤ, ∀ n : ℤ, 2 * a ^ 3 ≥ n * a + 7 := by
  push_neg
  intro a
  use 2*a^2
  conv => ring
  extra

example {p : ℕ} (hp : ¬ Prime p) (hp2 : 2 ≤ p) : ∃ m, 2 ≤ m ∧ m < p ∧ m ∣ p := by
  have H : ¬ (∀ (m : ℕ), 2 ≤ m → m < p → ¬m ∣ p)
  · intro h
    have h1: Prime p := prime_test hp2 h
    contradiction
  push_neg at H
  apply H

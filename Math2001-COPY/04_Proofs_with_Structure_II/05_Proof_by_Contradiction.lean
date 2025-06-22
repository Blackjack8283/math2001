/- Copyright (c) Heather Macbeth, 2023.  All rights reserved. -/
import Mathlib.Data.Real.Basic
import Library.Theory.ParityModular
import Library.Basic
import Library.Tactic.ModEq

math2001_init

open Int


example : ¬ (∀ x : ℝ, x ^ 2 ≥ x) := by
  intro h
  have : 0.5 ^ 2 ≥ 0.5 := h 0.5
  numbers at this


example : ¬ 3 ∣ 13 := by
  intro H
  obtain ⟨k, hk⟩ := H
  obtain h4 | h5 := le_or_succ_le k 4
  · have h :=
    calc 13 = 3 * k := hk
      _ ≤ 3 * 4 := by rel [h4]
    numbers at h
  · have h :=
    calc 13 = 3 * k := hk
      _ >= 3 * 5 := by rel [h5]
    numbers at h

example {x y : ℝ} (h : x + y = 0) : ¬(x > 0 ∧ y > 0) := by
  intro h
  obtain ⟨hx, hy⟩ := h
  have H :=
  calc 0 = x + y := by rw [h]
    _ > 0 := by extra
  numbers at H

example : ¬ (∃ n : ℕ, n ^ 2 = 2) := by
  intro h
  obtain ⟨n, hn⟩ := h
  obtain h1 | h2 := le_or_succ_le n 1
  · have H:=
    calc
      1=1^2:=by ring
      _>=n^2:=by rel[h1]
      _=2:=hn
    numbers at H
  · have H:=
    calc
      4=2^2:=by ring
      _<=n^2:=by rel[h2]
      _=2:=hn
    numbers at H

example (n : ℤ) : Int.Even n ↔ ¬ Int.Odd n := by
  constructor
  · intro h1 h2
    rw [Int.even_iff_modEq] at h1
    rw [Int.odd_iff_modEq] at h2
    have h :=
    calc 0 ≡ n [ZMOD 2] := by rel [h1]
      _ ≡ 1 [ZMOD 2] := by rel [h2]
    numbers at h -- contradiction!
  · intro h
    obtain h1 | h2 := Int.even_or_odd n
    · apply h1
    · contradiction

example (n : ℤ) : Int.Odd n ↔ ¬ Int.Even n := by
  constructor
  · intro h1 h2
    rw [Int.odd_iff_modEq] at h1
    rw [Int.even_iff_modEq] at h2
    have h:=
    calc 0 ≡ n[ZMOD 2]:=by rel[h2]
      _≡1[ZMOD 2]:=by rel[h1]
    numbers at h
  · intro h
    obtain h1 | h2 := Int.even_or_odd n
    · contradiction
    · apply h2


example (n : ℤ) : ¬(n ^ 2 ≡ 2 [ZMOD 3]) := by
  intro h
  mod_cases hn : n % 3
  · have h :=
    calc (0:ℤ) = 0 ^ 2 := by numbers
      _ ≡ n ^ 2 [ZMOD 3] := by rel [hn]
      _ ≡ 2 [ZMOD 3] := by rel [h]
    numbers at h -- contradiction!
  · have h :=
    calc (1:ℤ) = 1 ^ 2 := by numbers
      _ ≡ n ^ 2 [ZMOD 3] := by rel [hn]
      _ ≡ 2 [ZMOD 3] := by rel [h]
    numbers at h -- contradiction!
  · have h :=
    calc (1:ℤ) ≡ 1+3*1[ZMOD 3]:=by extra
      _ = 2 ^ 2 := by ring
      _ ≡ n ^ 2 [ZMOD 3] := by rel [hn]
      _ ≡ 2 [ZMOD 3] := by rel [h]
    numbers at h -- contradiction!

example {p : ℕ} (k l : ℕ) (hk1 : k ≠ 1) (hkp : k ≠ p) (hkl : p = k * l) :
    ¬(Prime p) := by
  have hk : k ∣ p
  · use l
    apply hkl
  intro h
  obtain ⟨h2, hfact⟩ := h
  have : k = 1 ∨ k = p := hfact k hk
  obtain hk1' | hkp' := this
  · contradiction
  · contradiction


example (a b : ℤ) (h : ∃ q, b * q < a ∧ a < b * (q + 1)) : ¬b ∣ a := by
  intro H
  obtain ⟨k, hk⟩ := H
  obtain ⟨q, hq₁, hq₂⟩ := h
  have hb :=
  calc 0 = a - a := by ring
    _ < b * (q + 1) - b * q := by rel [hq₁, hq₂]
    _ = b := by ring
  have h1 :=
  calc b * k = a := by rw [hk]
    _ < b * (q + 1) := hq₂
  cancel b at h1
  have h2:=
  calc b*q<a:=hq₁
    _=b*k:=hk
  cancel b at h2
  have h3: ¬k<q+1:=by addarith[h2]
  contradiction


example {p : ℕ} (hp : 2 ≤ p)  (T : ℕ) (hTp : p < T ^ 2)
    (H : ∀ (m : ℕ), 1 < m → m < T → ¬ (m ∣ p)) :
    Prime p := by
  apply prime_test hp
  intro m hm1 hmp
  obtain hmT | hmT := lt_or_le m T
  · apply H m hm1 hmT
  intro h_div
  obtain ⟨l, hl⟩ := h_div
  have : l ∣ p
  · use m
    rw[hl]
    ring
  have hl1 :=
    calc m * 1 = m := by ring
      _ < p := hmp
      _ = m * l := hl
  cancel m at hl1
  have hl2:=
    calc
      T*l<=m*l:=by rel[hmT]
      _=p:=by rw[hl]
      _<T^2:=hTp
      _=T*T:=by ring
  cancel T at hl2
  have : ¬ l ∣ p := H l hl1 hl2
  contradiction


example : Prime 79 := by
  apply better_prime_test (T := 9)
  · numbers
  · numbers
  intro m hm1 hm2
  apply Nat.not_dvd_of_exists_lt_and_lt
  interval_cases m
  · use 39
    constructor <;> numbers
  · use 26
    constructor <;> numbers
  · use 19
    constructor <;> numbers
  · use 15
    constructor <;> numbers
  · use 13
    constructor <;> numbers
  · use 11
    constructor <;> numbers
  · use 9
    constructor <;> numbers

/-! # Exercises -/


example : ¬ (∃ t : ℝ, t ≤ 4 ∧ t ≥ 5) := by
  intro h
  obtain⟨t,h1,h2⟩:=h
  have h3:¬t>=5:=by addarith[h1]
  contradiction

example : ¬ (∃ a : ℝ, a ^ 2 ≤ 8 ∧ a ^ 3 ≥ 30) := by
  intro h
  obtain⟨a,h1,h2⟩:=h
  obtain ha1 | ha2 := lt_or_le a 0
  · have h3:=
    calc a^3=a*(a^2):=by ring
      _<=0*(a^2):=by rel[ha1]
      _=0:=by ring
    have h4: ¬a^3>=30:=by addarith[h3]
    contradiction
  · have h3:=
    calc a^2<=8:=h1
      _<3^2:=by numbers
    cancel 2 at h3
    have h4:=
    calc a^3<3^3:=by rel[h3]
      _=27:=by numbers
    have h5: ¬a^3>=30:=by addarith[h4]
    contradiction


example : ¬ Int.Even 7 := by
  intro h
  rw [Int.even_iff_modEq] at h
  have h1:=
  calc 1≡1+2*3[ZMOD 2]:=by extra
    _=7:=by ring
    _≡0[ZMOD 2]:=h
  numbers at h1

example {n : ℤ} (hn : n + 3 = 7) : ¬ (Int.Even n ∧ n ^ 2 = 10) := by
  have h1:n=4:=by addarith[hn]
  intro ⟨h2,h3⟩
  rw[h1] at h3
  numbers at h3

example {x : ℝ} (hx : x ^ 2 < 9) : ¬ (x ≤ -3 ∨ x ≥ 3) := by
  intro h
  obtain hx1 | hx2 := h
  · have h1:-x>=3:=by addarith[hx1]
    have h2:=
    calc x^2=(-x)*(-x):=by ring
      _>=3*3:=by rel[h1]
      _=9:=by ring
    have h3:¬x^2<9:=by addarith[h2]
    contradiction
  · have h2:=
    calc x^2=x*x:=by ring
      _>=3*3:=by rel[hx2]
      _=9:=by ring
    have h3:¬x^2<9:=by addarith[h2]
    contradiction

example : ¬ (∃ N : ℕ, ∀ k > N, Nat.Even k) := by
  intro h
  obtain⟨n,h1⟩:=h
  have h2:n>=0:=by extra
  have h3:=
  calc n*2+1=n+n+1:=by ring
    _>=n+0+1:=by rel[h2]
    _=n+1:=by ring
    _>n:=by extra
  have h4:Nat.Even (n*2+1:ℕ):=h1 (n*2+1:ℕ) h3
  have h5:Nat.Odd (n*2+1:ℕ)
  · use n
    ring
  rw[Nat.odd_iff_not_even] at h5
  contradiction

example (n : ℤ) : ¬(n ^ 2 ≡ 2 [ZMOD 4]) := by
  intro h
  mod_cases hn : n % 4
  · have h :=
    calc (0:ℤ) = 0 ^ 2 := by numbers
      _ ≡ n ^ 2 [ZMOD 4] := by rel [hn]
      _ ≡ 2 [ZMOD 4] := by rel [h]
    numbers at h -- contradiction!
  · have h :=
    calc (1:ℤ) = 1 ^ 2 := by numbers
      _ ≡ n ^ 2 [ZMOD 4] := by rel [hn]
      _ ≡ 2 [ZMOD 4] := by rel [h]
    numbers at h -- contradiction!
  · have h :=
    calc (0:ℤ) ≡ 0+4*1[ZMOD 4]:=by extra
      _ = 2 ^ 2 := by ring
      _ ≡ n ^ 2 [ZMOD 4] := by rel [hn]
      _ ≡ 2 [ZMOD 4] := by rel [h]
    numbers at h -- contradiction!
  · have h :=
    calc (1:ℤ) ≡ 1+4*2[ZMOD 4]:=by extra
      _ = 3 ^ 2 := by ring
      _ ≡ n ^ 2 [ZMOD 4] := by rel [hn]
      _ ≡ 2 [ZMOD 4] := by rel [h]
    numbers at h -- contradiction!


example : ¬ Prime 1 := by
  intro h
  obtain⟨h1,h2⟩:=h
  numbers at h1

example : Prime 97 := by
  apply better_prime_test (T := 10)
  · numbers
  · numbers
  intro m hm1 hm2
  apply Nat.not_dvd_of_exists_lt_and_lt
  interval_cases m
  · use 48
    constructor <;> numbers
  · use 32
    constructor <;> numbers
  · use 24
    constructor <;> numbers
  · use 19
    constructor <;> numbers
  · use 16
    constructor <;> numbers
  · use 13
    constructor <;> numbers
  · use 12
    constructor <;> numbers
  · use 10
    constructor <;> numbers

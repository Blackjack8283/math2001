/- Copyright (c) Heather Macbeth, 2022.  All rights reserved. -/
import Mathlib.Data.Real.Basic
import Library.Basic

math2001_init


example {a : ℚ} (h : ∃ b : ℚ, a = b ^ 2 + 1) : a > 0 := by
  obtain ⟨b, hb⟩ := h
  calc
    a = b ^ 2 + 1 := hb
    _ > 0 := by extra


example {t : ℝ} (h : ∃ a : ℝ, a * t < 0) : t ≠ 0 := by
  obtain ⟨x, hxt⟩ := h
  have H := le_or_gt x 0
  obtain hx | hx := H
  · have hxt' : 0 < (-x) * t := by addarith [hxt]
    have hx' : 0 ≤ -x := by addarith [hx]
    cancel -x at hxt'
    apply ne_of_gt
    apply hxt'

  · have hxt': 0<x*(-t)
    calc
      0<(-x)*t:= by addarith[hxt]
      _=x*(-t):=by ring
    cancel x at hxt'
    apply ne_of_lt
    addarith[hxt']


example : ∃ n : ℤ, 12 * n = 84 := by
  use 7
  numbers


example (x : ℝ) : ∃ y : ℝ, y > x := by
  use x + 1
  extra


example : ∃ m n : ℤ, m ^ 2 - n ^ 2 = 11 := by
  use 6
  use 5
  numbers

example (a : ℤ) : ∃ m n : ℤ, m ^ 2 - n ^ 2 = 2 * a + 1 := by
  use a+1
  use a
  ring

example {p q : ℝ} (h : p < q) : ∃ x, p < x ∧ x < q := by
  use (q+p)/2
  constructor
  calc
    p=(p+p)/2:=by ring
    _<(q+p)/2:=by rel[h]
  calc
    (q+p)/2<(q+q)/2:=by rel[h]
    _=q:=by ring

example : ∃ a b c d : ℕ,
    a ^ 3 + b ^ 3 = 1729 ∧ c ^ 3 + d ^ 3 = 1729 ∧ a ≠ c ∧ a ≠ d := by
  use 1, 12, 9, 10
  constructor
  numbers
  constructor
  numbers
  constructor
  numbers
  numbers

/-! # Exercises -/


example : ∃ t : ℚ, t ^ 2 = 1.69 := by
  use 1.3
  numbers

example : ∃ m n : ℤ, m ^ 2 + n ^ 2 = 85 := by
  use 2
  use 9
  numbers

example : ∃ x : ℝ, x < 0 ∧ x ^ 2 < 1 := by
  use -0.5
  constructor
  numbers
  numbers

example : ∃ a b : ℕ, 2 ^ a = 5 * b + 1 := by
  use 4
  use 3
  numbers

-- //(x+1/2)
example (x : ℚ) : ∃ y : ℚ, y ^ 2 > x := by
  use x+1/2
  calc
    (x+1/2)^2=x^2+1/4+x:=by ring
    _>x:=by extra

example {t : ℝ} (h : ∃ a : ℝ, a * t + 1 < a + t) : t ≠ 1 := by
  obtain ⟨x, hx⟩ := h
  have h2: (1-x)*(t-1)>0:=
  calc
    (1-x)*(t-1)=-x*t+x+t-1:=by ring
    _>0 :=by addarith[hx]
  obtain h1|h1:=le_or_gt x 1
  have h3: 1-x>=0:=by addarith[h1]
  cancel 1-x at h2
  apply ne_of_gt
  addarith[h2]

  have h2':(x-1)*(1-t)>0:=
  calc
    (x-1)*(1-t)=(1-x)*(t-1):=by ring
    _>0:=h2
  have h3:x-1>0:=by addarith[h1]
  cancel x-1 at h2'
  apply ne_of_lt
  addarith[h2']

example {m : ℤ} (h : ∃ a, 2 * a = m) : m ≠ 5 := by
  obtain ⟨x,h1⟩:=h
  obtain h2|h2:=le_or_succ_le x 2
  apply ne_of_lt
  calc
    m=2*x:=by addarith[h1]
    _<=2*2:=by rel[h2]
    _=4:=by ring
    _<5:=by numbers
  apply ne_of_gt
  calc
    m=2*x:=by addarith[h1]
    _>=2*3:=by rel[h2]
    _=6:=by ring
    _>5:=by numbers

example {n : ℤ} : ∃ a, 2 * a ^ 3 ≥ n * a + 7 := by
  have h:=le_or_succ_le n 0
  obtain h|h := h
  use 2
  calc
    n*2+7<=0*2+7:=by rel[h]
    _<=16:=by numbers
    _=2*2^3:=by ring

  use 2*n
  calc
    2*(2*n)^3=16*n^3:=by ring
    _=2*n^3+14*n^3:=by ring
    _>=2*(n^3)+14*1^3:=by rel[h]
    _=n*(2*n)*n+14:=by ring
    _>=n*(2*n)*1+14:=by rel[h]
    _=n*(2*n)+7+7:=by ring
    _>=n*(2*n)+7:=by extra

example {a b c : ℝ} (ha : a ≤ b + c) (hb : b ≤ a + c) (hc : c ≤ a + b) :
    ∃ x y z, x ≥ 0 ∧ y ≥ 0 ∧ z ≥ 0 ∧ a = y + z ∧ b = x + z ∧ c = x + y := by
  use (-a+b+c)/2
  use (a-b+c)/2
  use (a+b-c)/2
  have ha': -a+b+c>=0:=by addarith[ha]
  have hb': a-b+c>=0:=by addarith[hb]
  have hc': a+b-c>=0:=by addarith[hc]
  constructor
  calc
    (-a+b+c)/2>=0/2:=by rel[ha']
    _=0:=by ring
  constructor
  calc
    (a-b+c)/2>=0/2:=by rel[hb']
    _=0:=by ring
  constructor
  calc
    (a+b-c)/2>=0/2:=by rel[hc']
    _=0:=by ring
  constructor
  ring
  constructor
  ring
  ring

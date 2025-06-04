/- Copyright (c) Heather Macbeth, 2022.  All rights reserved. -/
import Library.Basic

math2001_init


example {n : ℤ} (hn : 8 ∣ 5 * n) : 8 ∣ n := by
  obtain ⟨a, ha⟩ := hn
  use -3 * a + 2 * n
  calc
    n = -3 * (5 * n) + 16 * n := by ring
    _ = -3 * (8 * a) + 16 * n := by rw [ha]
    _ = 8 * (-3 * a + 2 * n) := by ring


example {n : ℤ} (hn : 8 ∣ 5 * n) : 8 ∣ n := by
  obtain ⟨a, ha⟩ := hn
  use -11*a+7*n
  calc
    n=-11 * (5 * n) + 56 * n := by ring
    _=-11*(8*a)+56*n:=by rw[ha]
    _=8*(-11*a+7*n):=by ring

example {n : ℤ} (h1 : 5 ∣ 3 * n) : 5 ∣ n := by
  obtain ⟨a, ha⟩ := h1
  use 2*n-3*a
  calc
    n=10*n-3*(3*n):=by ring
    _=10*n-3*(5*a):=by rw[ha]
    _=5*(2*n-3*a):=by ring


example {m : ℤ} (h1 : 8 ∣ m) (h2 : 5 ∣ m) : 40 ∣ m := by
  obtain ⟨a, ha⟩ := h1
  obtain ⟨b, hb⟩ := h2
  use -3 * a + 2 * b
  calc
    m = -15 * m + 16 * m := by ring
    _ = -15 * (8 * a) + 16 * m := by rw [ha]
    _ = -15 * (8 * a) + 16 * (5 * b) := by rw [hb]
    _ = 40 * (-3 * a + 2 * b) := by ring

/-! # Exercises -/


example {n : ℤ} (hn : 6 ∣ 11 * n) : 6 ∣ n := by
  obtain ⟨a, ha⟩ := hn
  use 2*n-a
  calc
    n=12*n-11*n:=by ring
    _=12*n-6*a:=by rw[ha]
    _=6*(2*n-a):=by ring

example {a : ℤ} (ha : 7 ∣ 5 * a) : 7 ∣ a := by
  obtain ⟨x, hx⟩ := ha
  use -2*a+3*x
  calc
    a=-14*a+3*(5*a):=by ring
    _=-14*a+3*(7*x):=by rw[hx]
    _=7*(-2*a+3*x):=by ring

example {n : ℤ} (h1 : 7 ∣ n) (h2 : 9 ∣ n) : 63 ∣ n := by
  obtain ⟨x, hx⟩ := h1
  obtain ⟨y, hy⟩ := h2
  use 4*x-5*y
  calc
    n=36*n-35*n:=by ring
    _=36*(7*x)-35*n:=by rw[hx]
    _=36*(7*x)-35*(9*y):=by rw[hy]
    _=63*(4*x-5*y):= by ring

example {n : ℤ} (h1 : 5 ∣ n) (h2 : 13 ∣ n) : 65 ∣ n := by
  obtain ⟨x, hx⟩ := h1
  obtain ⟨y, hy⟩ := h2
  use 2*x-5*y
  calc
    n=26*n-25*n:=by ring
    _=26*(5*x)-25*n:=by rw[hx]
    _=26*(5*x)-25*(13*y):=by rw[hy]
    _=65*(2*x-5*y):= by ring

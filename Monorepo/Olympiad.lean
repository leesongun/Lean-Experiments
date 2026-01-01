import Mathlib.Tactic
import Mathlib.Algebra.Order.Ring.Basic
import Canonical

variable {R : Type*} [CommRing R] [LinearOrder R] [IsStrictOrderedRing R]

theorem vasc (a b c : R) :
    (a^2 + b^2 + c^2)^2 ≥ 3 * (a^3 * b + b^3 * c + c^3 * a) := by
  let f (a b c : R) := a * (a - b) - (c - a) * (c - b)
  have : (f a b c)^2 + (f b c a)^2 + (f c a b)^2 ≥ 0 := by nlinarith
  unfold f at this
  linarith


structure VietaData (k : ℕ) where
  a : ℕ
  b : ℕ
  h : k * (a * b + 1) = a * a + b * b

private def vietaSwap (d : VietaData k) : VietaData k :=
  {a := d.b, b := d.a, h := by simp_all[Nat.mul_comm, Nat.add_comm, d.h]}

private def vietaInv (d : VietaData k) : d.b = 0 ∨ d.a ≤ k * d.b := by
  have := d.h
  by_contra
  simp_all only [not_or]
  have : (k * d.b + 1 ≤ d.a) := Nat.le_of_lt_succ (by linarith)
  have : d.b ≥ 1 := Nat.one_le_iff_ne_zero.mpr (by simp_all)
  nlinarith

private def vietaStep (d : VietaData k) (h : d.b > 0): VietaData k :=
  {a := d.b, b := (k * d.b - d.a), h := by
    cases vietaInv d with
    | inl => simp_all only [lt_self_iff_false]
    | inr h' => nlinarith[d.h, Nat.add_sub_cancel' h']
  }

def vieta (a b k : ℕ) : (k * (a * b + 1) = a * a + b * b) → (Nat.gcd a b) ^ 2 = k := by
  wlog h : a ≤ b generalizing a b
  · have h₃ := this b a (Nat.le_of_not_le h)
    intro h'
    rw [Nat.gcd_comm]
    apply h₃
    ring_nf at h' ⊢
    exact h'
  · induction h : a using Nat.strong_induction_on
    by_cases ha : a > 0
    · intro h₄
      simp_all
      let c := (k * a : ℤ) - b
      have : c * (b * b - k) = a := by
        unfold c
        ring_nf
        simp_all
        canonical
    · simp_all
      intro
      ring

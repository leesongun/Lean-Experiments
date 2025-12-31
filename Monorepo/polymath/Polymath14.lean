import Mathlib.Data.Real.Basic
import Mathlib.Data.Real.Archimedean
import Mathlib.Data.Real.Sqrt
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Tactic.Group
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp

open scoped BigOperators

variable [Group G]

class Pseudonorm (f : G → ℝ) where
  norm_mul x y : f (x * y) ≤ f x + f y
  norm_sq x    : f (x ^ 2) ≥ 2 * f x - 1

variable (f : G → ℝ) [p : Pseudonorm f]

-- should we remove n - 0 and use Nat.twoStepInduction?
lemma pow_upper x (k : ℕ) : f (x ^ k) ≤ k * f x + f 1:= by
  induction k with
  | zero => simp
  | succ n ih =>
    have h1 : f (x ^ (n + 1)) ≤ f (x ^ n) + f x := by
      simpa [pow_succ] using p.norm_mul (x ^ n) x
    have h2 : f (x ^ n) ≤ (n : ℝ) * f x + f 1 := by
      simpa using ih
    have h3 : f (x ^ (n + 1)) ≤ (n : ℝ) * f x + f 1 + f x := by
      linarith [h1, h2]
    have h4 : (n : ℝ) * f x + f 1 + f x = (n + 1 : ℝ) * f x + f 1 := by
      calc
        (n : ℝ) * f x + f 1 + f x = ((n : ℝ) + 1) * f x + f 1 := by
          ring
        _ = (n + 1 : ℝ) * f x + f 1 := by
          simp
    simpa [h4] using h3

lemma pow_lower x k : f (x^(2^k)) ≥ (2^k) * f x + 1 - (2^k) := by
  induction k with
  | zero => simp
  | succ n _ =>
    calc f (x ^ (2 ^ (n + 1))) = f ((x ^ (2 ^ n)) ^ 2) := by simp_all[pow_succ, pow_mul]
      _ ≥ 2 * f (x ^ (2 ^ n)) - 1 := p.norm_sq _
      _ ≥ 2 * ((2 ^ n) * f x + 1 - 2 ^ n) - 1 := by simp_all
      _ = (2 ^ (n + 1)) * f x + 1 - (2 ^ (n + 1)) := by ring

lemma rearrange x k : f x ≤ f (x ^ (2 ^ k))/(2 ^ k) + 1 := by
  have h := pow_lower f x k
  have hpos : (2 ^ k : ℝ) ≠ 0 := by positivity
  field_simp [hpos]
  linarith

@[simp] lemma conj_pow_group (x y : G) (n : ℕ) : (y * x * y⁻¹)^n = y * (x^n) * y⁻¹ := by
  induction n with
  | zero      => simp
  | succ _ ih => rw [pow_succ, ih]; group

lemma aux_lemma_real_bound (x y : ℝ) : (∀(n:ℕ), (2^n) * x ≤ y) → x ≤ 0 := by
  intro hv
  by_contra h
  simp_all
  have ⟨n, hn⟩ := exists_lt_nsmul h y
  have _ : y < y := by
    calc
    y < n • x := hn
    _ < 2^n • x := nsmul_lt_nsmul_left h Nat.lt_two_pow_self
    _ = 2^n * x := by simp
    _ ≤ y := hv n
  simp_all

lemma approx_conjugation (x y : G) : f (y * x * y⁻¹) ≤ f x + 1 := by
  suffices f (y * x * y⁻¹) - 1 - f x ≤ 0 by simp_all
  apply aux_lemma_real_bound _ (f 1 + f y + f y⁻¹ - 1)
  intro k
  suffices 2^k * f (y * x * y⁻¹) - 2^k + 1 ≤ f y + (2^k * f x + f 1) + f y⁻¹ by ring_nf at *; linarith
  calc
    2^k * f (y * x * y⁻¹) - 2^k + 1
      ≤ f ((y * x * y⁻¹)^(2^k)) := by linarith[pow_lower f (y * x * y⁻¹) k]
    _ = f (y * (x^(2^k)) * y⁻¹) := by rw[conj_pow_group]
    _ ≤ f (y * x^(2^k)) + f y⁻¹ := p.norm_mul _ _
    _ ≤ f y + f (x^(2^k)) + f y⁻¹  := by simp[p.norm_mul]
    _ ≤ f y + (2^k * f x + f 1) + f y⁻¹ := by
      have := pow_upper f x (2^k)
      simpa

section splitting_lemma
variable (n : ℕ)

lemma aux_lemma_ind s t w y z : f ((w * y)^n * s⁻¹ * t * (z * w⁻¹)^n) ≤ f (s⁻¹ * t) + n * (f y + f z + 1) := by
  induction n with
  | zero => simp
  | succ k ih =>
  calc
    f ((w * y)^(k + 1) * s⁻¹ * t * (z * w⁻¹)^(k + 1))
    _ = f ((w * y)^(1 + k) * s⁻¹ * t * (z * w⁻¹)^(k + 1)) := by ring_nf
    _ = f (((w * y) * (w * y)^k) * s⁻¹ * t * ((z * w⁻¹)^k * (z * w⁻¹))) := by simp [pow_add]
    _ = f (w * (y * ((w * y)^k * s⁻¹ * t * (z * w⁻¹)^k) * z) * w⁻¹) := by group
    _ ≤ f (y * ((w * y)^k * s⁻¹ * t * (z * w⁻¹)^k) * z) + 1 := approx_conjugation _ _ _
    _ ≤ f (y * ((w * y)^k * s⁻¹ * t * (z * w⁻¹)^k)) + f z + 1 := by simp[p.norm_mul]
    _ ≤ f y + f ((w * y)^k * s⁻¹ * t * (z * w⁻¹)^k) + f z + 1 := by simp[p.norm_mul]
    _ ≤ f y + (f (s⁻¹ * t) + k * (f y + f z + 1)) + f z + 1 := by linarith[ih]
    _ = f (s⁻¹ * t) + (k + 1) * (f y + f z + 1) := by ring
  simp

lemma aux_lemma_bound_fx : (x = s * w * y * s⁻¹) → (x = t * z * w⁻¹ * t⁻¹) →
  2 ^ (n + 1) * f x - 2 ^ (n + 1) ≤ (2 ^ n) * (f y + f z + 1) + (f s + f t⁻¹ + f (s⁻¹ * t)) := by
  intros
  calc
    2 ^ (n + 1) * f x - 2 ^ (n + 1)
    _ ≤ f (x ^ 2 ^ (n + 1)) := by linarith[pow_lower f x (n+1)]
    _ = f (x ^ 2 ^ n * x ^ 2 ^ n) := by simp [pow_add, pow_mul, pow_two]
    _ = f ((s * w * y * s⁻¹) ^ 2 ^ n * (t * z * w⁻¹ * t⁻¹) ^ 2 ^ n) := by simp_all
    _ = f ((s * (w * y) * s⁻¹) ^ 2 ^ n * (t * (z * w⁻¹) * t⁻¹) ^ 2 ^ n) := by group
    _ = f ((s * (w * y) ^ (2 ^ n) * s⁻¹)  * (t * (z * w⁻¹) ^ (2 ^ n) * t⁻¹)) := by simp_all
    _ = f (s * ((w * y) ^ (2 ^ n) * s⁻¹ * t * (z * w⁻¹) ^ (2 ^ n)) * t⁻¹) := by group
    _ ≤ f (s * ((w * y) ^ (2 ^ n) * s⁻¹ * t * (z * w⁻¹) ^ (2 ^ n))) + f t⁻¹ := by simp[p.norm_mul]
    _ ≤ f s + f ((w * y) ^ (2 ^ n) * s⁻¹ * t * (z * w⁻¹) ^ (2 ^ n)) + f t⁻¹ := by simp[p.norm_mul]
    _ ≤ f s + (f (s⁻¹ * t) + (2 ^ n) * (f y + f z + 1)) + f t⁻¹ := by
      have := aux_lemma_ind f (2^n) s t w y z
      simp_all
    _ = (2 ^ n) * (f y + f z + 1) + (f s + f t⁻¹ + f (s⁻¹ * t)) := by ring

end splitting_lemma

lemma splitting_lemma x y z w s t
  (h₁ : x = s * w * y * s⁻¹)
  (h₂ : x = t * z * w⁻¹ * t⁻¹) :
  2 * f x ≤ f y + f z + 3 := by
  suffices 2 * f x - f y - f z - 3 ≤ 0 by linarith
  apply aux_lemma_real_bound _ (f s + f t⁻¹ + f (s⁻¹ * t))
  intro n
  have := aux_lemma_bound_fx f n h₁ h₂
  simp_all[pow_add]
  linarith

section RandomWalk

variable (x y : G)

def g (n m : ℤ) := (x^n * (x * y * x⁻¹ * y⁻¹)^m)
theorem split_g (n m : ℤ) : 2 * f (g x y n m) ≤ f (g x y (n - 1) m) + f (g x y (n + 1) (m - 1)) + 4 := by
  calc
    2 * f (g x y n m)
      ≤ f (g x y (n - 1) m) + f (y⁻¹ * g x y n (m - 1) * x * y) + 3 :=
        splitting_lemma f (g x y n m) (g x y (n - 1) m) (y⁻¹ * (g x y n (m - 1)) * x * y) x 1 y
        (by unfold g; group) (by unfold g; rw[zpow_sub_one]; group)
    _ ≤ f (g x y (n - 1) m) + f ((x * y)⁻¹ * g x y (n + 1) (m - 1) * (x * y)⁻¹⁻¹) + 3 := by
        suffices y⁻¹ * g x y n (m - 1) * x * y = (x * y)⁻¹ * g x y (n + 1) (m - 1) * (x * y)⁻¹⁻¹ by simp_all
        unfold g
        group
    _ ≤ f (g x y (n - 1) m) + f (g x y (n + 1) (m - 1)) + 4 := by
        have := approx_conjugation f (g x y (n + 1) (m - 1)) (x * y)⁻¹
        linarith

def A : ℝ := max (max (f x) (f x⁻¹)) (max (f (x * y * x⁻¹ * y⁻¹)) (f (x * y * x⁻¹ * y⁻¹)⁻¹))

lemma pow_upper_Z x (k : ℤ) : f (x ^ k) ≤ |k| * max (f x) (f x⁻¹) + f 1 := by
  cases k with
  | ofNat l =>
    simp_all
    trans
    · exact pow_upper f x l
    · simp
      refine mul_le_mul_of_nonneg_left (by simp) (by simp)
  | negSucc l =>
    have _ : |Int.negSucc l| = l + 1 := by rfl
    simp_all
    trans
    · have h := pow_upper f x⁻¹ (l + 1)
      simp at h
      exact h
    · simp_all
      refine mul_le_mul_of_nonneg_left (by simp) (by linarith)

theorem bound_g_1 (n m : ℤ) : f (g x y n m) ≤ (|n| + |m|) * (A f x y) + 2 * f 1 := by
  let c := x * y * x⁻¹ * y⁻¹
  calc
    f (g x y n m)
      ≤ f (x^n) + f (c^m) := p.norm_mul _ _
    _ ≤ |n| * max (f x) (f x⁻¹) + |m| * max (f c) (f c⁻¹) + 2 * f 1 := by linarith[pow_upper_Z f x n, pow_upper_Z f c m]
  simp_all
  have h₁ : max (f x) (f x⁻¹) ≤ A f x y := by unfold A; simp_all
  have h₂ : max (f c) (f c⁻¹) ≤ A f x y := by unfold A; unfold c; simp_all
  have h₃ := mul_le_mul_of_nonneg_left h₁ $ abs_nonneg (n : ℝ)
  have h₄ := mul_le_mul_of_nonneg_left h₂ $ abs_nonneg (m : ℝ)
  linarith

lemma A_nonneg : 0 ≤ A f x y := by
  have h1 : 0 ≤ f 1 := by
    have h := p.norm_mul (1 : G) 1
    have h' : f 1 ≤ f 1 + f 1 := by simpa using h
    linarith
  have hsum_x : 0 ≤ f x + f x⁻¹ := by
    have h := p.norm_mul x x⁻¹
    have h' : f 1 ≤ f x + f x⁻¹ := by simpa using h
    linarith [h1, h']
  have hmax : (f x + f x⁻¹) / 2 ≤ max (f x) (f x⁻¹) := by
    have hleft : f x ≤ max (f x) (f x⁻¹) := le_max_left _ _
    have hright : f x⁻¹ ≤ max (f x) (f x⁻¹) := le_max_right _ _
    linarith
  have hx : 0 ≤ max (f x) (f x⁻¹) := by
    linarith [hsum_x, hmax]
  exact le_trans hx (le_max_left _ _)

def stepVal (b : Bool) : ℤ := if b then 1 else -1
def stepValR (b : Bool) : ℝ := if b then 1 else -1

def walkSumZ (n : ℕ) (s : Fin n → Bool) : ℤ := ∑ i, stepVal (s i)
def countTrueZ (n : ℕ) (s : Fin n → Bool) : ℤ := ∑ i, (if s i then 1 else 0)
def countFalseZ (n : ℕ) (s : Fin n → Bool) : ℤ := ∑ i, (if s i then 0 else 1)
def walkSumR (n : ℕ) (s : Fin n → Bool) : ℝ := ∑ i, stepValR (s i)

@[simp] lemma stepVal_cast (b : Bool) : (stepVal b : ℝ) = stepValR b := by
  cases b <;> simp [stepVal, stepValR]

@[simp] lemma stepValR_not (b : Bool) : stepValR (!b) = - stepValR b := by
  cases b <;> simp [stepValR]

@[simp] lemma stepValR_sq (b : Bool) : stepValR b * stepValR b = (1 : ℝ) := by
  cases b <;> simp [stepValR]

lemma walkSumR_eq (n : ℕ) (s : Fin n → Bool) : walkSumR n s = (walkSumZ n s : ℝ) := by
  classical
  simp [walkSumR, walkSumZ, stepVal_cast]

lemma stepVal_eq_sub (b : Bool) :
    stepVal b = (if b then 1 else 0) - (if b then 0 else 1) := by
  cases b <;> simp [stepVal]

lemma countTrueZ_add_countFalseZ (n : ℕ) (s : Fin n → Bool) :
    countTrueZ n s + countFalseZ n s = n := by
  classical
  calc
    countTrueZ n s + countFalseZ n s
        = ∑ i : Fin n, ((if s i then 1 else 0 : ℤ) + (if s i then 0 else 1)) := by
            simp [countTrueZ, countFalseZ, Finset.sum_add_distrib]
    _ = ∑ _i : Fin n, (1 : ℤ) := by
          refine Finset.sum_congr rfl ?_
          intro i _hi
          by_cases h : s i <;> simp [h]
    _ = n := by
          simp

lemma walkSumZ_eq (n : ℕ) (s : Fin n → Bool) :
    walkSumZ n s = 2 * countTrueZ n s - n := by
  classical
  have hsum : countTrueZ n s + countFalseZ n s = n := countTrueZ_add_countFalseZ (n := n) s
  have hdiff : walkSumZ n s = countTrueZ n s - countFalseZ n s := by
    simp [walkSumZ, countTrueZ, countFalseZ, stepVal_eq_sub, Finset.sum_sub_distrib]
  have hfalse : countFalseZ n s = n - countTrueZ n s := by linarith [hsum]
  calc
    walkSumZ n s = countTrueZ n s - countFalseZ n s := hdiff
    _ = countTrueZ n s - (n - countTrueZ n s) := by simp [hfalse]
    _ = 2 * countTrueZ n s - n := by ring

lemma walkSumZ_eq_neg_two (n : ℕ) (s : Fin (2 * n) → Bool) :
    (walkSumZ (2 * n) s : ℝ) = -2 * ((n : ℤ) - countTrueZ (2 * n) s : ℝ) := by
  have h := walkSumZ_eq (n := 2 * n) s
  have h' : (walkSumZ (2 * n) s : ℝ) =
      (2 : ℝ) * (countTrueZ (2 * n) s : ℝ) - (2 * n : ℝ) := by
    simpa using (congrArg (fun z : ℤ => (z : ℝ)) h)
  calc
    (walkSumZ (2 * n) s : ℝ) = (2 : ℝ) * (countTrueZ (2 * n) s : ℝ) - (2 * n : ℝ) := h'
    _ = (2 : ℝ) * (countTrueZ (2 * n) s : ℝ) - (2 : ℝ) * ((n : ℤ) : ℝ) := by
        simp
    _ = -2 * ((n : ℤ) - countTrueZ (2 * n) s : ℝ) := by ring

lemma abs_countTrue_le (n : ℕ) (s : Fin (2 * n) → Bool) :
    |((n : ℤ) - countTrueZ (2 * n) s : ℝ)|
      ≤ |(walkSumZ (2 * n) s : ℝ)| := by
  have h := walkSumZ_eq_neg_two (n := n) s
  have habs : |(walkSumZ (2 * n) s : ℝ)| =
      2 * |((n : ℤ) - countTrueZ (2 * n) s : ℝ)| := by
    calc
      |(walkSumZ (2 * n) s : ℝ)| = |-2 * ((n : ℤ) - countTrueZ (2 * n) s : ℝ)| := by
        simp [h]
      _ = |(-2 : ℝ)| * |((n : ℤ) - countTrueZ (2 * n) s : ℝ)| := by simp [abs_mul]
      _ = 2 * |((n : ℤ) - countTrueZ (2 * n) s : ℝ)| := by simp
  have hnonneg : 0 ≤ |((n : ℤ) - countTrueZ (2 * n) s : ℝ)| := by
    exact abs_nonneg _
  calc
    |((n : ℤ) - countTrueZ (2 * n) s : ℝ)|
        ≤ 2 * |((n : ℤ) - countTrueZ (2 * n) s : ℝ)| := by linarith
    _ = |(walkSumZ (2 * n) s : ℝ)| := by symm; exact habs

def flipAt {n : ℕ} (i : Fin n) (s : Fin n → Bool) : Fin n → Bool :=
  fun j => if j = i then ! s j else s j

lemma sum_stepValR_mul (N : ℕ) (i j : Fin N) :
    ∑ s : (Fin N → Bool), stepValR (s i) * stepValR (s j) =
      if i = j then (2 ^ N : ℝ) else 0 := by
  classical
  by_cases h : i = j
  · subst h
    have : ∀ s : Fin N → Bool, stepValR (s i) * stepValR (s i) = (1 : ℝ) := by
      intro s; cases s i <;> simp [stepValR]
    simp [this]
  · have hj : j ≠ i := by exact ne_comm.mp h
    let g : (Fin N → Bool) → (Fin N → Bool) := flipAt i
    have hneg :
        ∀ s, stepValR (s i) * stepValR (s j) + stepValR (g s i) * stepValR (g s j) = 0 := by
      intro s
      have hi' : stepValR (g s i) = - stepValR (s i) := by
        simp [g, flipAt]
      have hj' : stepValR (g s j) = stepValR (s j) := by
        simp [g, flipAt, hj]
      calc
        stepValR (s i) * stepValR (s j) + stepValR (g s i) * stepValR (g s j)
            = stepValR (s i) * stepValR (s j) + (-stepValR (s i)) * stepValR (s j) := by
                rw [hi', hj']
        _ = 0 := by ring
    have hneq : ∀ s, stepValR (s i) * stepValR (s j) ≠ 0 → g s ≠ s := by
      intro s _ hgs
      have := congrArg (fun t => t i) hgs
      cases s i <;> simp [g, flipAt] at this
    have hsum := Finset.sum_ninvolution (s := (Finset.univ : Finset (Fin N → Bool)))
      (f := fun s => stepValR (s i) * stepValR (s j)) (g := g) hneg hneq (by intro s; simp)
      (by intro s; ext k; by_cases hk : k = i <;> simp [g, flipAt, hk])
    simpa [h] using hsum

lemma sum_walkSum_sq (N : ℕ) :
    ∑ s : (Fin N → Bool), (walkSumR N s)^2 = (2 ^ N : ℝ) * N := by
  classical
  calc
    ∑ s : (Fin N → Bool), (walkSumR N s)^2
        = ∑ s : (Fin N → Bool), (∑ i : Fin N, stepValR (s i)) *
            (∑ j : Fin N, stepValR (s j)) := by
            simp [walkSumR, pow_two]
    _ = ∑ s : (Fin N → Bool), ∑ i : Fin N, ∑ j : Fin N, stepValR (s i) * stepValR (s j) := by
            simp [Finset.sum_mul_sum]
    _ = ∑ i : Fin N, ∑ j : Fin N, ∑ s : (Fin N → Bool), stepValR (s i) * stepValR (s j) := by
            rw [Finset.sum_comm]
            refine Finset.sum_congr rfl ?_
            intro i _hi
            rw [Finset.sum_comm]
    _ = ∑ i : Fin N, ∑ j : Fin N, (if i = j then (2 ^ N : ℝ) else 0) := by
            simp [sum_stepValR_mul]
    _ = ∑ i : Fin N, (2 ^ N : ℝ) := by
            refine Finset.sum_congr rfl ?_
            intro i _hi
            simp
    _ = (2 ^ N : ℝ) * N := by
            simp [Finset.sum_const, mul_comm]

lemma sum_abs_walkSum_le (N : ℕ) :
    ∑ s : (Fin N → Bool), |walkSumR N s| ≤ (2 ^ N : ℝ) * Real.sqrt N := by
  classical
  have h :=
    Real.sum_mul_le_sqrt_mul_sqrt (s := (Finset.univ : Finset (Fin N → Bool)))
      (f := fun s => |walkSumR N s|) (g := fun _ => (1 : ℝ))
  have h' :
      ∑ s : (Fin N → Bool), |walkSumR N s|
        ≤ Real.sqrt (∑ s : (Fin N → Bool), |walkSumR N s| ^ 2) *
            Real.sqrt (∑ s : (Fin N → Bool), (1 : ℝ) ^ 2) := by
      simpa using h
  have hsq :
      ∑ s : (Fin N → Bool), |walkSumR N s| ^ 2 =
        ∑ s : (Fin N → Bool), (walkSumR N s) ^ 2 := by
      simp [pow_two]
  have hcard : (∑ s : (Fin N → Bool), (1 : ℝ) ^ 2) = (2 ^ N : ℝ) := by
      simp
  calc
    ∑ s : (Fin N → Bool), |walkSumR N s|
        ≤ Real.sqrt (∑ s : (Fin N → Bool), (walkSumR N s) ^ 2) *
            Real.sqrt (2 ^ N : ℝ) := by
              simpa [hsq, hcard] using h'
    _ = Real.sqrt ((2 ^ N : ℝ) * N) * Real.sqrt (2 ^ N : ℝ) := by
              simp [sum_walkSum_sq, mul_comm, mul_left_comm]
    _ = (2 ^ N : ℝ) * Real.sqrt N := by
              have hpos : 0 ≤ (2 ^ N : ℝ) := by positivity
              have hposN : 0 ≤ (N : ℝ) := by positivity
              calc
                Real.sqrt ((2 ^ N : ℝ) * N) * Real.sqrt (2 ^ N : ℝ)
                    = (Real.sqrt (2 ^ N : ℝ) * Real.sqrt (N : ℝ)) *
                        Real.sqrt (2 ^ N : ℝ) := by
                          simp [Real.sqrt_mul, hpos]
                _ = Real.sqrt (N : ℝ) * (Real.sqrt (2 ^ N : ℝ) * Real.sqrt (2 ^ N : ℝ)) := by
                          ring
                _ = Real.sqrt (N : ℝ) * (2 ^ N : ℝ) := by
                          have hsq' : Real.sqrt (2 ^ N : ℝ) * Real.sqrt (2 ^ N : ℝ) =
                              Real.sqrt ((2 ^ N : ℝ) * (2 ^ N : ℝ)) := by
                                symm; exact Real.sqrt_mul hpos (2 ^ N : ℝ)
                          have hsq'' : Real.sqrt ((2 ^ N : ℝ) * (2 ^ N : ℝ)) = (2 ^ N : ℝ) := by
                                simp [Real.sqrt_mul_self hpos]
                          simp [hsq', hsq'']
                _ = (2 ^ N : ℝ) * Real.sqrt N := by ring

def headTailEquiv (n : ℕ) : (Fin (n + 1) → Bool) ≃ (Bool × (Fin n → Bool)) :=
  { toFun := fun s => (s 0, fun i => s i.succ)
    invFun := fun p i => Fin.cases p.1 (fun j => p.2 j) i
    left_inv := by
      intro s; funext i
      cases i using Fin.cases <;> rfl
    right_inv := by
      intro p; cases p with
      | mk b s =>
        ext i <;> rfl }

lemma walkSumZ_headTail (n : ℕ) (p : Bool × (Fin n → Bool)) :
    walkSumZ (n + 1) ((headTailEquiv n).symm p) =
      stepVal p.1 + walkSumZ n p.2 := by
  cases p with
  | mk b s =>
    simp [headTailEquiv, walkSumZ, stepVal, Fin.sum_univ_succ]

lemma countTrueZ_headTail (n : ℕ) (p : Bool × (Fin n → Bool)) :
    countTrueZ (n + 1) ((headTailEquiv n).symm p) =
      (if p.1 then 1 else 0) + countTrueZ n p.2 := by
  cases p with
  | mk b s =>
    classical
    simpa [countTrueZ, headTailEquiv] using
      (Fin.sum_univ_succ (f := fun i : Fin (n + 1) =>
        if (headTailEquiv n).symm (b, s) i then (1 : ℤ) else 0))

omit p in
lemma sum_walk_succ (m k : ℤ) (t : ℕ) :
    ∑ s : (Fin (t + 1) → Bool),
        f (g x y (m + walkSumZ (t + 1) s) (k - countTrueZ (t + 1) s))
      = ∑ s : Fin t → Bool,
          f (g x y (m - 1 + walkSumZ t s) (k - countTrueZ t s)) +
        ∑ s : Fin t → Bool,
          f (g x y (m + 1 + walkSumZ t s) (k - 1 - countTrueZ t s)) := by
  classical
  have hsum :
      ∑ s : (Fin (t + 1) → Bool),
          f (g x y (m + walkSumZ (t + 1) s) (k - countTrueZ (t + 1) s))
        = ∑ p : Bool × (Fin t → Bool),
            f (g x y (m + walkSumZ (t + 1) ((headTailEquiv t).symm p))
              (k - countTrueZ (t + 1) ((headTailEquiv t).symm p))) := by
    refine Fintype.sum_equiv (headTailEquiv t) _ _ ?_
    intro s
    simp
  have hprod :
      ∑ p : Bool × (Fin t → Bool),
          f (g x y (m + walkSumZ (t + 1) ((headTailEquiv t).symm p))
            (k - countTrueZ (t + 1) ((headTailEquiv t).symm p)))
        = ∑ b : Bool, ∑ s : Fin t → Bool,
            f (g x y (m + walkSumZ (t + 1) ((headTailEquiv t).symm (b, s)))
              (k - countTrueZ (t + 1) ((headTailEquiv t).symm (b, s)))) := by
    simpa using (Fintype.sum_prod_type (f := fun p =>
      f (g x y (m + walkSumZ (t + 1) ((headTailEquiv t).symm p))
        (k - countTrueZ (t + 1) ((headTailEquiv t).symm p)))))
  calc
    ∑ s : (Fin (t + 1) → Bool),
        f (g x y (m + walkSumZ (t + 1) s) (k - countTrueZ (t + 1) s))
        = ∑ b : Bool, ∑ s : Fin t → Bool,
            f (g x y (m + walkSumZ (t + 1) ((headTailEquiv t).symm (b, s)))
              (k - countTrueZ (t + 1) ((headTailEquiv t).symm (b, s)))) := by
              simpa [hsum] using hprod
    _ = ∑ s : Fin t → Bool,
          f (g x y (m + (1 + walkSumZ t s)) (k - (1 + countTrueZ t s))) +
        ∑ s : Fin t → Bool,
          f (g x y (m + (-1 + walkSumZ t s)) (k - countTrueZ t s)) := by
          simp [walkSumZ_headTail, countTrueZ_headTail, stepVal]
    _ = ∑ s : Fin t → Bool,
          f (g x y (m + 1 + walkSumZ t s) (k - 1 - countTrueZ t s)) +
        ∑ s : Fin t → Bool,
          f (g x y (m - 1 + walkSumZ t s) (k - countTrueZ t s)) := by
          have hneg (a : ℤ) : m + (-1 + a) = m - 1 + a := by ring
          have hpos (a : ℤ) : m + (1 + a) = m + 1 + a := by ring
          have hcnt (a : ℤ) : k - (1 + a) = k - 1 - a := by ring
          simp [hneg, hpos, hcnt]
    _ = ∑ s : Fin t → Bool,
          f (g x y (m - 1 + walkSumZ t s) (k - countTrueZ t s)) +
        ∑ s : Fin t → Bool,
          f (g x y (m + 1 + walkSumZ t s) (k - 1 - countTrueZ t s)) := by
          simp [add_comm]

lemma iter_split_g (m k : ℤ) :
    ∀ t : ℕ,
      f (g x y m k) ≤ 2 * t +
        (1 / (2 ^ t : ℝ)) *
          ∑ s : Fin t → Bool, f (g x y (m + walkSumZ t s) (k - countTrueZ t s)) := by
  intro t
  induction t generalizing m k with
  | zero =>
      simp [walkSumZ, countTrueZ]
  | succ t ih =>
      have hsplit :
          f (g x y m k) ≤
            2 + (f (g x y (m - 1) k) + f (g x y (m + 1) (k - 1))) / 2 := by
        have h := split_g (f := f) (x := x) (y := y) (n := m) (m := k)
        linarith
      set sum1 : ℝ :=
        ∑ s : Fin t → Bool, f (g x y (m - 1 + walkSumZ t s) (k - countTrueZ t s))
      set sum2 : ℝ :=
        ∑ s : Fin t → Bool, f (g x y (m + 1 + walkSumZ t s) (k - 1 - countTrueZ t s))
      have h1 : f (g x y (m - 1) k) ≤ 2 * t + (1 / (2 ^ t : ℝ)) * sum1 := by
        simpa [sum1] using (ih (m - 1) k)
      have h2 : f (g x y (m + 1) (k - 1)) ≤ 2 * t + (1 / (2 ^ t : ℝ)) * sum2 := by
        simpa [sum2] using (ih (m + 1) (k - 1))
      have hsum :
          f (g x y (m - 1) k) + f (g x y (m + 1) (k - 1))
            ≤ 4 * (t : ℝ) + (1 / (2 ^ t : ℝ)) * (sum1 + sum2) := by
        linarith [h1, h2]
      have hdiv :
          (f (g x y (m - 1) k) + f (g x y (m + 1) (k - 1))) / 2
            ≤ (4 * (t : ℝ) + (1 / (2 ^ t : ℝ)) * (sum1 + sum2)) / 2 := by
        have hmul := mul_le_mul_of_nonneg_right hsum (by norm_num : (0 : ℝ) ≤ (1 / 2 : ℝ))
        simpa [div_eq_mul_inv] using hmul
      have hrewrite :
          (4 * (t : ℝ) + (2 ^ t : ℝ)⁻¹ * (sum1 + sum2)) / 2 =
            2 * (t : ℝ) + ((2 ^ t : ℝ)⁻¹ / 2) * (sum1 + sum2) := by
        ring
      have hpow : ((2 ^ t : ℝ)⁻¹ / 2) = (2 ^ (t + 1) : ℝ)⁻¹ := by
        simp [pow_succ, div_eq_mul_inv, mul_comm]
      have hdiv' :
          (f (g x y (m - 1) k) + f (g x y (m + 1) (k - 1))) / 2
            ≤ 2 * (t : ℝ) + (1 / (2 ^ (t + 1) : ℝ)) * (sum1 + sum2) := by
        simpa [hrewrite, hpow] using hdiv
      have hcomb :
          f (g x y m k) ≤ 2 * (t + 1) + (1 / (2 ^ (t + 1) : ℝ)) * (sum1 + sum2) := by
        have htmp : f (g x y m k) ≤ 2 + (2 * (t : ℝ) + (1 / (2 ^ (t + 1) : ℝ)) * (sum1 + sum2)) := by
          linarith [hsplit, hdiv']
        nlinarith [htmp]
      have hsum :
          ∑ s : Fin (t + 1) → Bool,
              f (g x y (m + walkSumZ (t + 1) s) (k - countTrueZ (t + 1) s))
            = sum1 + sum2 := by
        simpa [sum1, sum2] using (sum_walk_succ (f := f) (x := x) (y := y) (m := m) (k := k) t)
      simpa [hsum] using hcomb

theorem bound_g (n : ℕ) :
    f (g x y 0 (n : ℤ)) ≤
      Real.sqrt (2 * (n : ℝ)) * (2 * A f x y) + 4 * (n : ℝ) + 2 * f 1 := by
  set N : ℕ := 2 * n
  have hiter :=
    iter_split_g (f := f) (x := x) (y := y) (m := 0) (k := (n : ℤ)) N
  have hN : (2 * (N : ℝ)) = (4 * (n : ℝ)) := by
    calc
      (2 * (N : ℝ)) = 2 * ((2 * n : ℕ) : ℝ) := by simp [N]
      _ = 2 * ((2 : ℝ) * (n : ℝ)) := by simp [Nat.cast_mul]
      _ = 4 * (n : ℝ) := by ring
  have hiter' :
      f (g x y 0 (n : ℤ)) ≤
        4 * (n : ℝ) +
          (1 / (2 ^ N : ℝ)) *
            ∑ s : Fin N → Bool, f (g x y (walkSumZ N s) ((n : ℤ) - countTrueZ N s)) := by
    simpa [hN] using hiter
  have hA : 0 ≤ A f x y := A_nonneg (f := f) (x := x) (y := y)
  have hterm :
      ∀ s : Fin N → Bool,
        f (g x y (walkSumZ N s) ((n : ℤ) - countTrueZ N s)) ≤
          (2 * A f x y) * |(walkSumZ N s : ℝ)| + 2 * f 1 := by
    intro s
    have h := bound_g_1 (f := f) (x := x) (y := y)
      (n := walkSumZ N s) (m := (n : ℤ) - countTrueZ N s)
    have h' :
        f (g x y (walkSumZ N s) ((n : ℤ) - countTrueZ N s)) ≤
          (|((walkSumZ N s : ℝ))| + |((n : ℤ) - countTrueZ N s : ℝ)|) * (A f x y) + 2 * f 1 := by
      simpa using h
    have hle : |((n : ℤ) - countTrueZ N s : ℝ)| ≤ |(walkSumZ N s : ℝ)| := by
      simpa [N] using abs_countTrue_le (n := n) (s := s)
    have hsum :
        |(walkSumZ N s : ℝ)| + |((n : ℤ) - countTrueZ N s : ℝ)|
          ≤ |(walkSumZ N s : ℝ)| + |(walkSumZ N s : ℝ)| := by
      have hsum' := add_le_add_right hle |(walkSumZ N s : ℝ)|
      simpa [add_comm] using hsum'
    have hmul :
        (|(walkSumZ N s : ℝ)| + |((n : ℤ) - countTrueZ N s : ℝ)|) * (A f x y)
          ≤ (|(walkSumZ N s : ℝ)| + |(walkSumZ N s : ℝ)|) * (A f x y) := by
      exact mul_le_mul_of_nonneg_right hsum hA
    have hmul' :
        (|(walkSumZ N s : ℝ)| + |(walkSumZ N s : ℝ)|) * (A f x y)
          = (2 * A f x y) * |(walkSumZ N s : ℝ)| := by
      ring
    linarith [h', hmul, hmul']
  have hsum_bound :
      ∑ s : Fin N → Bool, f (g x y (walkSumZ N s) ((n : ℤ) - countTrueZ N s))
        ≤ ∑ s : Fin N → Bool,
            ((2 * A f x y) * |(walkSumZ N s : ℝ)| + 2 * f 1) := by
    classical
    simpa using
      (Finset.sum_le_sum (s := (Finset.univ : Finset (Fin N → Bool)))
        (by
          intro s _hs
          exact hterm s))
  have hsum_abs :
      ∑ s : Fin N → Bool, |(walkSumZ N s : ℝ)| ≤ (2 ^ N : ℝ) * Real.sqrt N := by
    simpa [walkSumR_eq] using sum_abs_walkSum_le (N := N)
  have hcard : (Fintype.card (Fin N → Bool) : ℝ) = 2 ^ N := by
    simp
  have hsum_scaled :
      (1 / (2 ^ N : ℝ)) *
          (∑ s : Fin N → Bool,
            ((2 * A f x y) * |(walkSumZ N s : ℝ)| + 2 * f 1))
        ≤ (2 * A f x y) * Real.sqrt N + 2 * f 1 := by
    have hpos : 0 ≤ (1 / (2 ^ N : ℝ)) := by positivity
    have hposN' : (2 ^ N : ℝ) ≠ 0 := by positivity
    have hsum1 :
        (1 / (2 ^ N : ℝ)) *
            ∑ s : Fin N → Bool, (2 * A f x y) * |(walkSumZ N s : ℝ)|
          ≤ (2 * A f x y) * Real.sqrt N := by
      have hposA : 0 ≤ (2 * A f x y : ℝ) := by nlinarith [hA]
      have hdiv :
          (1 / (2 ^ N : ℝ)) *
              ∑ s : Fin N → Bool, |(walkSumZ N s : ℝ)|
            ≤ (1 / (2 ^ N : ℝ)) * ((2 ^ N : ℝ) * Real.sqrt N) := by
        exact mul_le_mul_of_nonneg_left hsum_abs hpos
      have hsum_const :
          ∑ s : Fin N → Bool, (2 * A f x y) * |(walkSumZ N s : ℝ)|
            = (2 * A f x y) * ∑ s : Fin N → Bool, |(walkSumZ N s : ℝ)| := by
        classical
        symm
        simpa using
          (Finset.mul_sum (s := (Finset.univ : Finset (Fin N → Bool)))
            (a := (2 * A f x y))
            (f := fun s => |(walkSumZ N s : ℝ)|))
      calc
        (1 / (2 ^ N : ℝ)) *
            ∑ s : Fin N → Bool, (2 * A f x y) * |(walkSumZ N s : ℝ)|
            = (1 / (2 ^ N : ℝ)) *
                ((2 * A f x y) * ∑ s : Fin N → Bool, |(walkSumZ N s : ℝ)|) := by
              simp [hsum_const]
        _ = (2 * A f x y) * ((1 / (2 ^ N : ℝ)) *
              ∑ s : Fin N → Bool, |(walkSumZ N s : ℝ)|) := by
              ring
        _ ≤ (2 * A f x y) * ((1 / (2 ^ N : ℝ)) * ((2 ^ N : ℝ) * Real.sqrt N)) := by
              exact mul_le_mul_of_nonneg_left hdiv hposA
        _ = (2 * A f x y) * Real.sqrt N := by
              field_simp [hposN']
    have hsum2 :
        (1 / (2 ^ N : ℝ)) *
            ∑ s : Fin N → Bool, (2 * f 1)
          ≤ 2 * f 1 := by
      have hsum2_eq :
          (1 / (2 ^ N : ℝ)) *
              ∑ s : Fin N → Bool, (2 * f 1)
            = 2 * f 1 := by
        classical
        calc
          (1 / (2 ^ N : ℝ)) *
              ∑ s : Fin N → Bool, (2 * f 1)
              = (1 / (2 ^ N : ℝ)) *
                  ((Fintype.card (Fin N → Bool) : ℝ) * (2 * f 1)) := by
                    simp [mul_comm, mul_assoc]
          _ = (1 / (2 ^ N : ℝ)) * ((2 ^ N : ℝ) * (2 * f 1)) := by
                simp
          _ = 2 * f 1 := by
                field_simp [hposN']
      linarith [hsum2_eq]
    have hsum3 :
        (1 / (2 ^ N : ℝ)) *
            (∑ s : Fin N → Bool,
              ((2 * A f x y) * |(walkSumZ N s : ℝ)| + 2 * f 1))
          = (1 / (2 ^ N : ℝ)) *
              ∑ s : Fin N → Bool, (2 * A f x y) * |(walkSumZ N s : ℝ)|
            + (1 / (2 ^ N : ℝ)) *
              ∑ s : Fin N → Bool, (2 * f 1) := by
        classical
        simp [Finset.sum_add_distrib, mul_add, add_comm]
    linarith [hsum1, hsum2, hsum3]
  have hsum_final :
      (1 / (2 ^ N : ℝ)) *
          ∑ s : Fin N → Bool, f (g x y (walkSumZ N s) ((n : ℤ) - countTrueZ N s))
        ≤ (2 * A f x y) * Real.sqrt N + 2 * f 1 := by
    have hpos : 0 ≤ (1 / (2 ^ N : ℝ)) := by positivity
    have hsum_scaled' :
        (1 / (2 ^ N : ℝ)) *
            (∑ s : Fin N → Bool,
              ((2 * A f x y) * |(walkSumZ N s : ℝ)| + 2 * f 1))
          ≤ (2 * A f x y) * Real.sqrt N + 2 * f 1 := hsum_scaled
    exact (mul_le_mul_of_nonneg_left hsum_bound hpos).trans hsum_scaled'
  have hsqrtN : Real.sqrt (N : ℝ) = Real.sqrt (2 * (n : ℝ)) := by
    simp [N, Nat.cast_mul]
  have hsum_final' :
      (1 / (2 ^ N : ℝ)) *
          ∑ s : Fin N → Bool, f (g x y (walkSumZ N s) ((n : ℤ) - countTrueZ N s))
        ≤ Real.sqrt (2 * (n : ℝ)) * (2 * A f x y) + 2 * f 1 := by
    simpa [hsqrtN, mul_comm, mul_left_comm, mul_assoc] using hsum_final
  linarith [hiter', hsum_final']

end RandomWalk

theorem polymath14 x y : f (x * y * x⁻¹ * y⁻¹) ≤ 5 := by
  set c : G := x * y * x⁻¹ * y⁻¹
  have h : f c - 5 ≤ 0 := by
    apply aux_lemma_real_bound (x := f c - 5) (y := 2 * A f x y * Real.sqrt 2 + 2 * f 1)
    intro m
    have hpow : f c ≤ f (c ^ (2 ^ (2 * m))) / (2 ^ (2 * m) : ℝ) + 1 := by
      simpa [c] using (rearrange (f := f) (x := c) (k := 2 * m))
    have hbound :
        f (c ^ (2 ^ (2 * m))) ≤
          Real.sqrt (2 * (2 ^ (2 * m) : ℝ)) * (2 * A f x y) +
            4 * (2 ^ (2 * m) : ℝ) + 2 * f 1 := by
      let n : ℕ := 2 ^ (2 * m)
      have h := bound_g (f := f) (x := x) (y := y) (n := n)
      have h' :
          f (c ^ (n : ℤ)) ≤
            Real.sqrt (2 * (n : ℝ)) * (2 * A f x y) + 4 * (n : ℝ) + 2 * f 1 := by
        simpa [g, c] using h
      have h'' :
          f (c ^ n) ≤
            Real.sqrt (2 * (n : ℝ)) * (2 * A f x y) + 4 * (n : ℝ) + 2 * f 1 := by
        simpa [zpow_natCast] using h'
      simpa [n] using h''
    have hcomb :
        f c ≤
          (Real.sqrt (2 * (2 ^ (2 * m) : ℝ)) * (2 * A f x y) +
              4 * (2 ^ (2 * m) : ℝ) + 2 * f 1) / (2 ^ (2 * m) : ℝ) + 1 := by
      have hdiv :
          f (c ^ (2 ^ (2 * m))) / (2 ^ (2 * m) : ℝ) ≤
            (Real.sqrt (2 * (2 ^ (2 * m) : ℝ)) * (2 * A f x y) +
                4 * (2 ^ (2 * m) : ℝ) + 2 * f 1) / (2 ^ (2 * m) : ℝ) := by
        have hpos : 0 ≤ (2 ^ (2 * m) : ℝ)⁻¹ := by positivity
        have hmul := mul_le_mul_of_nonneg_right hbound hpos
        simpa [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using hmul
      have hdiv' :
          f (c ^ (2 ^ (2 * m))) / (2 ^ (2 * m) : ℝ) + 1 ≤
            (Real.sqrt (2 * (2 ^ (2 * m) : ℝ)) * (2 * A f x y) +
                4 * (2 ^ (2 * m) : ℝ) + 2 * f 1) / (2 ^ (2 * m) : ℝ) + 1 :=
        by
          have h := add_le_add_right hdiv 1
          simpa [add_comm, add_left_comm, add_assoc] using h
      exact le_trans hpow hdiv'
    have hpow' : (2 ^ (2 * m) : ℝ) = (2 ^ m : ℝ) ^ 2 := by
      calc
        (2 ^ (2 * m) : ℝ) = (2 : ℝ) ^ (2 * m) := by simp
        _ = (2 : ℝ) ^ (m * 2) := by simp [mul_comm]
        _ = ((2 : ℝ) ^ m) ^ 2 := by simp [pow_mul]
        _ = (2 ^ m : ℝ) ^ 2 := by simp
    have hsqrt :
        Real.sqrt (2 * (2 ^ (2 * m) : ℝ)) = Real.sqrt 2 * (2 ^ m : ℝ) := by
      have hpos : 0 ≤ (2 ^ (2 * m) : ℝ) := by positivity
      calc
        Real.sqrt (2 * (2 ^ (2 * m) : ℝ))
            = Real.sqrt 2 * Real.sqrt (2 ^ (2 * m) : ℝ) := by
                have hpos2 : 0 ≤ (2 : ℝ) := by linarith
                simp [Real.sqrt_mul, hpos2]
        _ = Real.sqrt 2 * (2 ^ m : ℝ) := by
              have : Real.sqrt (2 ^ (2 * m) : ℝ) = |(2 ^ m : ℝ)| := by
                simp [hpow']
              simp [this]
    have hposA : 0 ≤ A f x y := A_nonneg (f := f) (x := x) (y := y)
    have hpow_ge (k : ℕ) : (1 : ℝ) ≤ (2 ^ k : ℝ) := by
      have hnat : (1 : ℕ) ≤ 2 ^ k := by
        exact Nat.one_le_pow k 2 (by decide)
      exact_mod_cast hnat
    have hmain :
        (2 ^ m : ℝ) * (f c - 5) ≤ 2 * A f x y * Real.sqrt 2 + 2 * f 1 := by
      have h1 :
          f c - 5 ≤
            (2 * A f x y * Real.sqrt 2) / (2 ^ m : ℝ) + (2 * f 1) / (2 ^ (2 * m) : ℝ) := by
        have hpow2 : (2 ^ (2 * m) : ℝ) ≠ 0 := by positivity
        have hA' : (Real.sqrt (2 * (2 ^ (2 * m) : ℝ)) * (2 * A f x y)) / (2 ^ (2 * m) : ℝ)
            = (2 * A f x y * Real.sqrt 2) / (2 ^ m : ℝ) := by
            have hposm : (2 ^ m : ℝ) ≠ 0 := by positivity
            calc
              (Real.sqrt (2 * (2 ^ (2 * m) : ℝ)) * (2 * A f x y)) / (2 ^ (2 * m) : ℝ)
                  = ((Real.sqrt 2 * (2 ^ m : ℝ)) * (2 * A f x y)) / (2 ^ (2 * m) : ℝ) := by
                    simp [hsqrt]
              _ = (2 * A f x y * Real.sqrt 2) * (2 ^ m : ℝ) / (2 ^ (2 * m) : ℝ) := by
                    ring
              _ = (2 * A f x y * Real.sqrt 2) * (2 ^ m : ℝ) / ((2 ^ m : ℝ) ^ 2) := by
                    simp [hpow']
              _ = (2 ^ m : ℝ) * (2 * A f x y * Real.sqrt 2) / ((2 ^ m : ℝ) * (2 ^ m : ℝ)) := by
                    simp [pow_two, mul_comm, mul_left_comm, mul_assoc]
              _ = (2 * A f x y * Real.sqrt 2) / (2 ^ m : ℝ) := by
                    simpa [mul_comm, mul_left_comm, mul_assoc] using
                      (mul_div_mul_left (a := (2 * A f x y * Real.sqrt 2))
                        (b := (2 ^ m : ℝ)) (c := (2 ^ m : ℝ)) hposm)
        have hcomb' :
            (Real.sqrt (2 * (2 ^ (2 * m) : ℝ)) * (2 * A f x y) +
                4 * (2 ^ (2 * m) : ℝ) + 2 * f 1) / (2 ^ (2 * m) : ℝ) + 1 =
              (Real.sqrt (2 * (2 ^ (2 * m) : ℝ)) * (2 * A f x y)) / (2 ^ (2 * m) : ℝ) +
                (2 * f 1) / (2 ^ (2 * m) : ℝ) + 5 := by
          field_simp [hpow2]
          ring
        have hcomb'' :
            f c ≤
              (Real.sqrt (2 * (2 ^ (2 * m) : ℝ)) * (2 * A f x y)) / (2 ^ (2 * m) : ℝ) +
                (2 * f 1) / (2 ^ (2 * m) : ℝ) + 5 := by
          have hcomb'' := hcomb
          rw [hcomb'] at hcomb''
          exact hcomb''
        have h1' :
            f c - 5 ≤
              (Real.sqrt (2 * (2 ^ (2 * m) : ℝ)) * (2 * A f x y)) / (2 ^ (2 * m) : ℝ) +
                (2 * f 1) / (2 ^ (2 * m) : ℝ) := by
          linarith [hcomb'']
        have h1'' := h1'
        rw [hA'] at h1''
        exact h1''
      have hpos : 0 ≤ (2 ^ m : ℝ) := by positivity
      have hmul :=
        mul_le_mul_of_nonneg_left h1 hpos
      have hmul' :
          (2 ^ m : ℝ) *
              ((2 * A f x y * Real.sqrt 2) / (2 ^ m : ℝ) +
                (2 * f 1) / (2 ^ (2 * m) : ℝ))
            = 2 * A f x y * Real.sqrt 2 + (2 * f 1) / (2 ^ m : ℝ) := by
        have hposm : (2 ^ m : ℝ) ≠ 0 := by positivity
        field_simp [hposm, hpow']
        ring
      have hmul'' :
          (2 ^ m : ℝ) * (f c - 5) ≤
            2 * A f x y * Real.sqrt 2 + (2 * f 1) / (2 ^ m : ℝ) := by
        simpa [hmul'] using hmul
      have h2m : (2 * f 1) / (2 ^ m : ℝ) ≤ 2 * f 1 := by
        have hposf : 0 ≤ (2 * f 1 : ℝ) := by
          have h := p.norm_mul (1 : G) 1
          have h1 : f 1 ≤ f 1 + f 1 := by simpa using h
          have hpos1 : 0 ≤ f 1 := by linarith
          nlinarith
        have := div_le_self hposf (hpow_ge m)
        simpa using this
      linarith [hmul'', h2m]
    simpa using hmain
  linarith [h]

import Monorepo.polymath.DHJ.Definitions
import Monorepo.polymath.DHJ.GR
import Mathlib.Data.Real.Archimedean
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Density Hales-Jewett (proof skeleton)

This file mirrors the structure of arXiv:1209.4986v2. We formalize the
basic combinatorial objects (words, variable words, lines, density) and
prove the density-increment iteration as a standalone lemma. The deep
combinatorial increment step is packaged as a hypothesis; together these
yield a clean, self-contained Lean statement of the density
Hales--Jewett theorem.
-/

open Polymath.DHJ

section GrahamRothschild

/-- Graham--Rothschild, Option-alphabet form (monochromatic parameter set of lines). -/
def graham_rothschild_option {k m : ℕ} :
    Σ n, ∀ L : Set (LineW (Fin k) (Fin n)),
      DecidablePred L →
        {S : SubspaceW (Fin m) (Option (Fin k)) (Fin n) //
          (∀ l, lineOfLineSubspace S l ∈ L) ∨ (∀ l, lineOfLineSubspace S l ∉ L)} := by
  simpa using (Polymath.DHJ.linesMonochromatic_option (k := k) (m := m))

/--
If the monochromatic subspace has no `none` constants, it comes from an actual subspace of `[k]^n`.
This produces a genuine `linesMonochromatic` witness for `L`.
-/
def graham_rothschild {k m : ℕ} (hk : 2 ≤ k) :
    ∀ n, ∀ L : Set (LineW (Fin k) (Fin n)),
      ∀ decL : DecidablePred L,
      ∀ S : SubspaceW (Fin m) (Option (Fin k)) (Fin n),
        (∀ i, S.idxFun i ≠ Sum.inl none) →
        S.IsMono (lineColor L decL) →
          {V : SubspaceW (Fin m) (Fin k) (Fin n) //
            linesMonochromatic V L} := by
  intro n L decL S hS hmono
  refine ⟨Polymath.DHJ.subspaceOfOption (Nat.lt_of_lt_of_le (by decide : 0 < 2) hk) S, ?_⟩
  exact Polymath.DHJ.linesMonochromatic_of_isMono_option hk (L := L) decL (S := S) hS hmono

end GrahamRothschild

lemma line_exists_of_increment
    {k n : ℕ} (hk : 0 < k) {δ γ : ℝ} (hγ : 0 < γ)
    {A : Finset (Word k n)} (hA : density A ≥ δ)
    (hinc :
      ∀ {A : Finset (Word k n)}, density A ≥ δ → ¬ hasLine A →
        {B : Finset (Word k n) // B ⊆ A ∧ density B ≥ density A + γ}) :
    hasLine A := by
  by_contra hline
  have hiter :
      ∀ t : ℕ,
        {B : Finset (Word k n) //
          B ⊆ A ∧ density B ≥ density A + (t : ℝ) * γ ∧ ¬ hasLine B} := by
    intro t
    induction t with
    | zero =>
        refine ⟨A, ?_, ?_, hline⟩
        · intro w hw; exact hw
        · simp
    | succ t ih =>
        obtain ⟨B, hBspec⟩ := ih
        have hBA : B ⊆ A := hBspec.1
        have hBdens : density B ≥ density A + (t : ℝ) * γ := hBspec.2.1
        have hBline : ¬ hasLine B := hBspec.2.2
        have hBdens' : density B ≥ δ := by
          have hnonneg : 0 ≤ (t : ℝ) * γ := by
            have ht : 0 ≤ (t : ℝ) := by exact_mod_cast (Nat.zero_le t)
            exact mul_nonneg ht (le_of_lt hγ)
          linarith [hA, hBdens, hnonneg]
        obtain ⟨C, hCspec⟩ := hinc hBdens' hBline
        have hCB : C ⊆ B := hCspec.1
        have hCdens : density C ≥ density B + γ := hCspec.2
        have hCline : ¬ hasLine C := by
          intro hCline
          exact hline (hasLine_of_subset (by
            intro w hw; exact hBA (hCB hw)) hCline)
        refine ⟨C, ?_, ?_, hCline⟩
        · intro w hw; exact hBA (hCB hw)
        · have hCdens'' : density C ≥ density A + (t : ℝ) * γ + γ := by
            linarith [hBdens, hCdens]
          have hmul : (t : ℝ) * γ + γ = ((t : ℝ) + 1) * γ := by
            calc
              (t : ℝ) * γ + γ = (t : ℝ) * γ + (1 : ℝ) * γ := by simp
              _ = ((t : ℝ) + 1) * γ := by
                symm
                exact add_mul (t : ℝ) 1 γ
          have hCdens''' : density C ≥ density A + ((t : ℝ) + 1) * γ := by
            linarith [hCdens'', hmul]
          simpa [Nat.cast_add] using hCdens'''
  obtain ⟨t, ht⟩ := exists_lt_nsmul hγ (1 - density A)
  have ht' : 1 - density A < (t : ℝ) * γ := by
    simpa using ht
  obtain ⟨B, hBspec⟩ := hiter t
  have hBdens : density B ≥ density A + (t : ℝ) * γ := hBspec.2.1
  have hgt : density B > 1 := by
    have : density A + (t : ℝ) * γ > 1 := by linarith [ht']
    linarith [hBdens, this]
  have hle : density B ≤ 1 := density_le_one (k := k) (n := n) hk B
  exact (not_lt_of_ge hle hgt)

/--
Subtype witness version of `line_exists_of_increment`.
We use `Classical.choice` to extract a concrete line from `hasLine`.
-/
noncomputable def containsLine_of_increment
    {k n : ℕ} (hk : 0 < k) {δ γ : ℝ} (hγ : 0 < γ)
    {A : Finset (Word k n)} (hA : density A ≥ δ)
  (hinc :
    ∀ {A : Finset (Word k n)}, density A ≥ δ → ¬ hasLine A →
      {B : Finset (Word k n) // B ⊆ A ∧ density B ≥ density A + γ}) :
  containsLine A := by
  exact Classical.choice (line_exists_of_increment hk hγ hA hinc)

noncomputable def exists_dense_slice_of_exists_sparse_slice {k m r : ℕ} (hk : 2 ≤ k) (hm : 1 ≤ m)
    {A : Finset (Word k (m + r))} {ε : ℝ} (_hε : 0 < ε)
    (hsmall : {x : Word k m // density (sliceFinset A x) ≤ density A - ε}) :
    {x : Word k m //
      density A + ε / ((k ^ m : ℝ) - 1) ≤ density (sliceFinset A x)} := by
  obtain ⟨x0, hx0⟩ := hsmall
  let S : Finset (Word k m) := Finset.univ
  let f : Word k m → ℝ := fun x => density (sliceFinset A x)
  have hkpos : 0 < k := Nat.lt_of_lt_of_le (by decide : 0 < 2) hk
  have hsum : Finset.sum S f = (k ^ m : ℝ) * density A := by
    simpa [S, f] using
      (sum_density_slice_eq_density (k := k) (n := m) (m := r) hkpos A)
  have hx0mem : x0 ∈ S := by
    simp [S]
  have hsum_erase :
      Finset.sum (S.erase x0) f = (k ^ m : ℝ) * density A - f x0 := by
    simp [S, f, hsum, Finset.sum_erase_eq_sub (s := S) (f := f) hx0mem]
  have hk1 : (1 : ℝ) < (k : ℝ) := by
    exact_mod_cast (lt_of_lt_of_le (by decide : 1 < 2) hk)
  have hm0 : m ≠ 0 := by
    exact Nat.ne_of_gt (lt_of_lt_of_le (by decide : 0 < 1) hm)
  have hkpow1 : (1 : ℝ) < (k : ℝ) ^ m := one_lt_pow₀ hk1 hm0
  have hkpow1' : (1 : ℝ) < (k ^ m : ℝ) := by
    simpa [Nat.cast_pow] using hkpow1
  have hdenom : (k ^ m : ℝ) - 1 ≠ 0 := by
    linarith
  have hsum_erase_ge :
      Finset.sum (S.erase x0) f ≥ (k ^ m : ℝ) * density A - (density A - ε) := by
    have hx0' : f x0 ≤ density A - ε := by
      simpa [f] using hx0
    linarith [hsum_erase, hx0']
  have hcard_erase :
      ((S.erase x0).card : ℝ) = (k ^ m : ℝ) - 1 := by
    have hcard_nat := Finset.card_erase_add_one (s := S) hx0mem
    have hcard_univ : (S.card : ℝ) = (k ^ m : ℝ) := by
      simp [S, Word]
    have hcard_nat' : ((S.erase x0).card : ℝ) + 1 = (S.card : ℝ) := by
      exact_mod_cast hcard_nat
    linarith [hcard_nat', hcard_univ]
  have hsum_const_eq :
      Finset.sum (S.erase x0) (fun _ => density A + ε / ((k ^ m : ℝ) - 1)) =
        (k ^ m : ℝ) * density A - (density A - ε) := by
    calc
      Finset.sum (S.erase x0) (fun _ => density A + ε / ((k ^ m : ℝ) - 1))
          = ((S.erase x0).card : ℝ) * (density A + ε / ((k ^ m : ℝ) - 1)) := by
              simp
      _ = ((k ^ m : ℝ) - 1) * (density A + ε / ((k ^ m : ℝ) - 1)) := by
              simp [hcard_erase]
      _ = (k ^ m : ℝ) * density A - (density A - ε) := by
              calc
                ((k ^ m : ℝ) - 1) * (density A + ε / ((k ^ m : ℝ) - 1))
                    = ((k ^ m : ℝ) - 1) * density A +
                        ((k ^ m : ℝ) - 1) * (ε / ((k ^ m : ℝ) - 1)) := by ring
                _ = ((k ^ m : ℝ) - 1) * density A + ε := by
                        have hmul_div :
                            ((k ^ m : ℝ) - 1) * (ε / ((k ^ m : ℝ) - 1)) = ε := by
                          calc
                            ((k ^ m : ℝ) - 1) * (ε / ((k ^ m : ℝ) - 1))
                                = (((k ^ m : ℝ) - 1) * ε) / ((k ^ m : ℝ) - 1) := by
                                    symm
                                    exact mul_div_assoc ((k ^ m : ℝ) - 1) ε ((k ^ m : ℝ) - 1)
                            _ = ε := by
                                exact mul_div_cancel_left₀ ε hdenom
                        simp [hmul_div]
                _ = (k ^ m : ℝ) * density A - (density A - ε) := by ring
  have hsum_const_le :
      Finset.sum (S.erase x0) (fun _ => density A + ε / ((k ^ m : ℝ) - 1)) ≤
        Finset.sum (S.erase x0) f := by
    linarith [hsum_const_eq, hsum_erase_ge]
  have hcard_pos_real : 0 < ((S.erase x0).card : ℝ) := by
    linarith [hcard_erase, hkpow1']
  have hcard_pos : 0 < (S.erase x0).card := by
    exact_mod_cast hcard_pos_real
  have hnonempty : (S.erase x0).Nonempty := by
    exact Finset.card_pos.1 hcard_pos
  have hx_exists :=
    Finset.exists_le_of_sum_le (s := S.erase x0) hnonempty hsum_const_le
  let x := Classical.choose hx_exists
  have hxge : density A + ε / ((k ^ m : ℝ) - 1) ≤ f x :=
    (Classical.choose_spec hx_exists).2
  refine ⟨x, ?_⟩
  simpa [f] using hxge

/-- Subtype wrapper returning an explicit dense slice witness. -/
noncomputable def denseSliceChoice {k m r : ℕ} (hk : 2 ≤ k) (hm : 1 ≤ m)
    {A : Finset (Word k (m + r))} {ε : ℝ} (hε : 0 < ε)
    (hsmall : {x : Word k m // density (sliceFinset A x) ≤ density A - ε}) :
    {x : Word k m // density A + ε / ((k ^ m : ℝ) - 1) ≤ density (sliceFinset A x)} := by
  simpa using
    (exists_dense_slice_of_exists_sparse_slice hk hm (A := A) (ε := ε) (_hε := hε) hsmall)

def sliceAt {k n l : ℕ} (A : Finset (Word k n)) (hl : l ≤ n) (x : Word k l) :
    Finset (Word k (n - l)) :=
  sliceFinset
    (castWordFinset (k := k) (n := n) (n' := l + (n - l)) (Nat.add_sub_cancel' hl).symm A) x

lemma castWordFinset_congr {k n n' : ℕ} (A : Finset (Word k n)) (h₁ h₂ : n = n') :
    castWordFinset (k := k) h₁ A = castWordFinset (k := k) h₂ A := by
  cases h₁
  cases h₂
  rfl

lemma castWordFinset_congr_add_assoc {k l m r : ℕ} (A : Finset (Word k ((l + m) + r)))
    (h : (l + m) + r = l + (m + r)) :
    castWordFinset (k := k) h A =
      castWordFinset (k := k) (Nat.add_assoc l m r) A := by
  exact castWordFinset_congr A h (Nat.add_assoc l m r)

lemma sliceFinset_castWordFinset_suffix {k l s s' : ℕ} (A : Finset (Word k (l + s)))
    (x : Word k l) (h : s = s') :
    sliceFinset
        (castWordFinset (k := k) (n := l + s) (n' := l + s')
          (by simp [h]) A) x =
      castWordFinset (k := k) (n := s) (n' := s') h (sliceFinset A x) := by
  ext y
  have hA : l + s = l + s' := by
    simp [h]
  simp [mem_sliceFinset, mem_castWordFinset, castWord_comp, wordConcat, Fin.append_cast_right]

lemma sliceAt_castWord {k n l l' : ℕ} (A : Finset (Word k n)) (hl : l ≤ n)
    (h : l = l') (x : Word k l) :
    sliceAt (k := k) (n := n) (l := l') A (by simpa [h] using hl)
        (castWord (k := k) (n := l) (n' := l') h x) =
      castWordFinset (k := k) (n := n - l) (n' := n - l') (by
        simp [h]) (sliceAt (k := k) (n := n) (l := l) A hl x) := by
  cases h
  rfl


@[simp] lemma sliceAt_zero {k n : ℕ} (A : Finset (Word k n)) (hl : 0 ≤ n) (x : Word k 0) :
    sliceAt (k := k) (n := n) (l := 0) A hl x = A := by
  have hx : x = emptyWord k := by
    funext i
    exact (Fin.elim0 i)
  subst hx
  ext y
  simp [sliceAt, Nat.sub_zero, -castWord_comp]

noncomputable def exists_slice_ge_density {k m r : ℕ} (hk : 0 < k) (A : Finset (Word k (m + r))) :
    {x : Word k m // density A ≤ density (sliceFinset A x)} := by
  let S : Finset (Word k m) := Finset.univ
  let f : Word k m → ℝ := fun x => density (sliceFinset A x)
  have hsum : Finset.sum S f = (k ^ m : ℝ) * density A := by
    simpa [S, f] using
      (sum_density_slice_eq_density (k := k) (n := m) (m := r) hk A)
  have hsum_const :
      Finset.sum S (fun _ => density A) = (k ^ m : ℝ) * density A := by
    have hcard_univ : (S.card : ℝ) = (k ^ m : ℝ) := by
      simp [S, Word]
    calc
      Finset.sum S (fun _ => density A)
          = (S.card : ℝ) * density A := by simp
      _ = (k ^ m : ℝ) * density A := by simp [hcard_univ]
  have hsum_le :
      Finset.sum S (fun _ => density A) ≤ Finset.sum S f := by
    simp [hsum_const, hsum]
  have hnonempty : S.Nonempty := by
    refine ⟨fun _ => ⟨0, hk⟩, Finset.mem_univ _⟩
  have hx_exists := Finset.exists_le_of_sum_le (s := S) hnonempty hsum_le
  let x := Classical.choose hx_exists
  have hxge : density A ≤ f x := (Classical.choose_spec hx_exists).2
  exact ⟨x, hxge⟩

noncomputable def dense_slice_step {k m l r : ℕ} (hk : 2 ≤ k) (hm : 1 ≤ m)
    {A : Finset (Word k ((l + m) + r))} {x : Word k l} {ε : ℝ} (hε : 0 < ε)
    (hassoc : (l + m) + r = l + (m + r))
    (hA0 :
      density
          (sliceFinset
            (castWordFinset (k := k) (n := (l + m) + r) (n' := l + (m + r))
              hassoc A) x) ≥ density A)
    (hsmall : {y : Word k m // density (sliceFinset A (wordConcat x y)) ≤ density A - ε}) :
    {y : Word k m //
      density (sliceFinset A (wordConcat x y)) ≥
        density
            (sliceFinset
              (castWordFinset (k := k) (n := (l + m) + r) (n' := l + (m + r))
                hassoc A) x) + ε / ((k ^ m : ℝ) - 1)} := by
  let A0 : Finset (Word k (l + (m + r))) :=
    castWordFinset (k := k) (n := (l + m) + r) (n' := l + (m + r))
      hassoc A
  let ε' : ℝ := density (sliceFinset A0 x) - density A + ε
  have hε'pos : 0 < ε' := by
    dsimp [ε']
    linarith [hA0]
  have hsmall' : {y : Word k m //
      density (sliceFinset (sliceFinset A0 x) y) ≤ density (sliceFinset A0 x) - ε'} := by
    rcases hsmall with ⟨y, hy⟩
    refine ⟨y, ?_⟩
    have hslice :
        sliceFinset (sliceFinset A0 x) y = sliceFinset A (wordConcat x y) := by
      simpa [A0, castWordFinset_congr A hassoc (Nat.add_assoc l m r)] using
        (Polymath.DHJ.sliceFinset_slice (A := A) (x := x) (y := y))
    have hy' : density (sliceFinset (sliceFinset A0 x) y) ≤ density A - ε := by
      have hy' := hy
      rw [← hslice] at hy'
      exact hy'
    have hε'' : density (sliceFinset A0 x) - ε' = density A - ε := by
      dsimp [ε']
      ring
    simpa [hε''] using hy'
  obtain ⟨y, hy⟩ :=
    exists_dense_slice_of_exists_sparse_slice hk hm (A := sliceFinset A0 x) (ε := ε') hε'pos
      hsmall'
  have hk1 : (1 : ℝ) < (k : ℝ) := by
    exact_mod_cast (lt_of_lt_of_le (by decide : 1 < 2) hk)
  have hm0 : m ≠ 0 := by
    exact Nat.ne_of_gt (lt_of_lt_of_le (by decide : 0 < 1) hm)
  have hkpow1 : (1 : ℝ) < (k : ℝ) ^ m := one_lt_pow₀ hk1 hm0
  have hkpow1' : 0 < (k ^ m : ℝ) - 1 := by
    have hkpow1'' : (1 : ℝ) < (k ^ m : ℝ) := by
      simpa [Nat.cast_pow] using hkpow1
    linarith
  have hε'ge : ε ≤ ε' := by
    dsimp [ε']
    linarith [hA0]
  have hdiv_le : ε / ((k ^ m : ℝ) - 1) ≤ ε' / ((k ^ m : ℝ) - 1) := by
    have hdenpos' : 0 < (1 / ((k ^ m : ℝ) - 1)) := by
      exact one_div_pos.2 hkpow1'
    have hmul :
        ε * (1 / ((k ^ m : ℝ) - 1)) ≤ ε' * (1 / ((k ^ m : ℝ) - 1)) :=
      mul_le_mul_of_nonneg_right hε'ge (le_of_lt hdenpos')
    conv_lhs => rw [div_eq_mul_one_div]
    conv_rhs => rw [div_eq_mul_one_div]
    exact hmul
  have hy' :
      density (sliceFinset A (wordConcat x y)) ≥
        density (sliceFinset A0 x) + ε' / ((k ^ m : ℝ) - 1) := by
    have hslice :
        sliceFinset (sliceFinset A0 x) y = sliceFinset A (wordConcat x y) := by
      simpa [A0] using
        (Polymath.DHJ.sliceFinset_slice (A := A) (x := x) (y := y))
    have hy' := hy
    rw [hslice] at hy'
    exact hy'
  refine ⟨y, ?_⟩
  linarith [hy', hdiv_le]

lemma subspaceConcatRight_good {k m l r : ℕ} {δ : ℝ}
    {A : Finset (Word k ((l + m) + r))} {x : Word k l}
    (hgood : ∀ y : Word k m, δ ≤ density (sliceFinset A (wordConcat x y))) :
    ∀ z ∈ subspaceFinset (subspaceConcatRight x (fullSubspace k m)),
      δ ≤ density (sliceFinset A z) := by
  intro z hz
  have hz' : z ∈ (subspaceFinset (fullSubspace k m)).image (fun y => wordConcat x y) := by
    simpa [subspaceFinset_subspaceConcatRight] using hz
  rcases Finset.mem_image.1 hz' with ⟨y, _hy, rfl⟩
  exact hgood y

lemma uniform_slice_subspace_of_steps_exists {k m n : ℕ} (hk : 2 ≤ k) (hm : 1 ≤ m)
    {ε : ℝ} (hε : 0 < ε) (_hε1 : ε < 1)
    {A : Finset (Word k n)} (hA : density A > ε)
    (T : ℕ) (hTn : (T + 1) * m < n)
    (hT : (T : ℝ) * (ε / ((k ^ m : ℝ) - 1)) > 1) :
    Nonempty (Σ lhl : {l : ℕ // l < n},
      {V : SubspaceW (Fin m) (Fin k) (Fin lhl.1) //
        ∀ x ∈ subspaceFinset V,
          density (sliceAt A (Nat.le_of_lt lhl.2) x) ≥ density A - ε}) := by
  by_contra hgood
  have hbad :
      ∀ l, ∀ hl : l < n, ∀ V : SubspaceW (Fin m) (Fin k) (Fin l),
        ∃ x ∈ subspaceFinset V,
          density (sliceAt A (Nat.le_of_lt hl) x) ≤ density A - ε := by
    intro l hl V
    by_contra h
    have h' :
        ∀ x ∈ subspaceFinset V, density (sliceAt A (Nat.le_of_lt hl) x) ≥ density A - ε := by
      intro x hx
      by_contra hlt
      have hlt' : density (sliceAt A (Nat.le_of_lt hl) x) < density A - ε := lt_of_not_ge hlt
      exact h ⟨x, hx, le_of_lt hlt'⟩
    exact hgood ⟨⟨⟨l, hl⟩, ⟨V, h'⟩⟩⟩
  let ρ : ℝ := ε / ((k ^ m : ℝ) - 1)
  have hkpos : 0 < k := Nat.lt_of_lt_of_le (by decide : 0 < 2) hk
  have hmpos : 0 < m := Nat.lt_of_lt_of_le (by decide : 0 < 1) hm
  have hk1 : (1 : ℝ) < (k : ℝ) := by
    exact_mod_cast (lt_of_lt_of_le (by decide : 1 < 2) hk)
  have hm0 : m ≠ 0 := Nat.ne_of_gt hmpos
  have hkpow1 : (1 : ℝ) < (k : ℝ) ^ m := one_lt_pow₀ hk1 hm0
  have hkpow1' : 0 < (k ^ m : ℝ) - 1 := by
    have hkpow1'' : (1 : ℝ) < (k ^ m : ℝ) := by
      simpa [Nat.cast_pow] using hkpow1
    linarith
  have hρpos : 0 < ρ := by
    exact div_pos hε hkpow1'
  have hiter :
      ∀ t ≤ T, Σ x : Word k (t * m),
        {hlt : t * m < n //
          density (sliceAt A (Nat.le_of_lt hlt) x) ≥ density A + (t : ℝ) * ρ} := by
    intro t ht
    induction t with
    | zero =>
        have hlt0 : 0 * m < n := by
          simpa using (lt_of_le_of_lt (Nat.zero_le _) hTn)
        let A0 : Finset (Word k (0 * m + (n - 0 * m))) :=
          castWordFinset (k := k) (n := n) (n' := 0 * m + (n - 0 * m))
            (Nat.add_sub_cancel' (Nat.le_of_lt hlt0)).symm A
        obtain ⟨x, hx⟩ :=
          exists_slice_ge_density (k := k) (m := 0 * m) (r := n - 0 * m) hkpos A0
        have hA0eq : density A0 = density A := by
          simp [A0]
        have hslice : sliceAt A (Nat.le_of_lt hlt0) x = sliceFinset A0 x := by
          simp [sliceAt, A0]
        refine ⟨x, hlt0, ?_⟩
        have hx' : density (sliceFinset A0 x) ≥ density A0 := by
          simpa using hx
        simpa [hslice, hA0eq] using hx'
    | succ t ih =>
        have ht' : t ≤ T := by
          exact Nat.le_trans (Nat.le_of_lt (Nat.lt_succ_self t)) ht
        obtain ⟨x, hltx, hx⟩ := ih ht'
        let l : ℕ := t * m
        have hTm : T * m < n := by
          have hTlt : T * m < (T + 1) * m := by
            simpa [Nat.succ_mul, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using
              (Nat.mul_lt_mul_of_pos_right (Nat.lt_succ_self T) hmpos)
          exact lt_trans hTlt hTn
        have hlt : l + m < n := by
          have hle : (t + 1) * m ≤ T * m := Nat.mul_le_mul_right m ht
          have hle' : l + m ≤ T * m := by
            simpa [l, Nat.succ_mul, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using hle
          exact lt_of_le_of_lt hle' hTm
        let r : ℕ := n - (l + m)
        have hN : (l + m) + r = n := Nat.add_sub_cancel' (Nat.le_of_lt hlt)
        let A0 : Finset (Word k ((l + m) + r)) :=
          castWordFinset (k := k) (n := n) (n' := (l + m) + r) hN.symm A
        let V : SubspaceW (Fin m) (Fin k) (Fin (l + m)) :=
          subspaceConcatRight x (fullSubspace k m)
        have hlow :
            ∃ z ∈ subspaceFinset V,
              density (sliceAt A (Nat.le_of_lt hlt) z) ≤ density A - ε := by
          simpa [V] using (hbad (l + m) hlt V)
        let z := Classical.choose hlow
        have hz_spec := Classical.choose_spec hlow
        have hz : z ∈ subspaceFinset V := hz_spec.1
        have hzdens : density (sliceAt A (Nat.le_of_lt hlt) z) ≤ density A - ε := hz_spec.2
        have hz' :
            z ∈ (subspaceFinset (fullSubspace k m)).image (fun y => wordConcat x y) := by
          simpa [V, subspaceFinset_subspaceConcatRight] using hz
        let hy_exists := Finset.mem_image.1 hz'
        let y := Classical.choose hy_exists
        have hy_spec := Classical.choose_spec hy_exists
        have hy : y ∈ subspaceFinset (fullSubspace k m) := hy_spec.1
        have hconcat : wordConcat x y = z := hy_spec.2
        have hzdens' :
            density (sliceAt A (Nat.le_of_lt hlt) (wordConcat x y)) ≤ density A - ε := by
          simpa [hconcat] using hzdens
        have hsmall :
            {y : Word k m //
              density (sliceFinset A0 (wordConcat x y)) ≤ density A - ε} := by
          refine ⟨y, ?_⟩
          simpa [sliceAt, A0, r, hN] using hzdens'
        have hA0eq : density A0 = density A := by
          simp [A0]
        have hsmall0 :
            {y : Word k m //
              density (sliceFinset A0 (wordConcat x y)) ≤ density A0 - ε} := by
          rcases hsmall with ⟨y, hy⟩
          refine ⟨y, ?_⟩
          simpa [hA0eq] using hy
        have hA0cast :
            castWordFinset (k := k) (n := (l + m) + r) (n' := n) hN A0 = A := by
          simp [A0]
        have hN' : l + (m + r) = n := by
          simpa [Nat.add_assoc] using hN
        have hnl : n - l = m + r := by
          simpa [hN'] using (Nat.add_sub_cancel_left l (m + r))
        have h1' : (l + m) + r = l + (n - l) :=
          hN.trans (Nat.add_sub_cancel' (Nat.le_of_lt hltx)).symm
        have hln : l + (n - l) = l + (m + r) := by
          simp [hnl]
        have h1 : (l + m) + r = l + (m + r) := h1'.trans hln
        have hx_cast :
            density
                (sliceFinset
                  (castWordFinset (k := k) (n := (l + m) + r) (n' := l + (m + r))
                    h1 A0) x) ≥ density A0 + (t : ℝ) * ρ := by
          have hx' :
              density
                  (sliceFinset
                    (castWordFinset (k := k) (n := (l + m) + r) (n' := l + (n - l))
                      h1' A0) x) ≥ density A0 + (t : ℝ) * ρ := by
            simpa [sliceAt, ← hA0cast, castWordFinset_trans, h1'] using hx
          have hcast :
              castWordFinset (k := k) (n := (l + m) + r) (n' := l + (m + r)) h1 A0 =
                castWordFinset (k := k) (n := l + (n - l)) (n' := l + (m + r)) hln
                  (castWordFinset (k := k) (n := (l + m) + r) (n' := l + (n - l)) h1' A0) := by
            simp
          have hslice :
              sliceFinset (castWordFinset (k := k) (n := (l + m) + r) (n' := l + (m + r)) h1 A0) x =
                castWordFinset (k := k) (n := n - l) (n' := m + r) hnl
                  (sliceFinset (castWordFinset (k := k) (n := (l + m) + r) (n' := l + (n - l)) h1' A0) x) := by
            have hslice' :=
              (sliceFinset_castWordFinset_suffix
                (A := castWordFinset (k := k) (n := (l + m) + r) (n' := l + (n - l)) h1' A0)
                (x := x) (h := hnl))
            rw [← hcast] at hslice'
            exact hslice'
          have hx'' :
              density
                  (castWordFinset (k := k) (n := n - l) (n' := m + r) hnl
                    (sliceFinset
                      (castWordFinset (k := k) (n := (l + m) + r) (n' := l + (n - l))
                        h1' A0) x)) ≥ density A0 + (t : ℝ) * ρ := by
            simpa using hx'
          simpa [hslice] using hx''
        have hA0 :
            density
                (sliceFinset
                  (castWordFinset (k := k) (n := (l + m) + r) (n' := l + (m + r))
                    h1 A0) x) ≥ density A0 := by
          have hnonneg : 0 ≤ (t : ℝ) * ρ := by
            have ht0 : 0 ≤ (t : ℝ) := by exact_mod_cast (Nat.zero_le t)
            exact mul_nonneg ht0 (le_of_lt hρpos)
          linarith [hx_cast, hnonneg]
        obtain ⟨y', hy'⟩ :=
          dense_slice_step (k := k) (m := m) (l := l) (r := r) hk hm hε h1 hA0 hsmall0
        have hy'' :
            density (sliceFinset A0 (wordConcat x y')) ≥
              density
                  (sliceFinset
                    (castWordFinset (k := k) (n := (l + m) + r) (n' := l + (m + r))
                      h1 A0) x) + ρ := hy'
        have hy''' :
            density (sliceAt A (Nat.le_of_lt hlt) (wordConcat x y')) ≥
              density A + ((t + 1 : ℕ) : ℝ) * ρ := by
          have hx' :
              density
                  (sliceFinset
                    (castWordFinset (k := k) (n := (l + m) + r) (n' := l + (m + r))
                      h1 A0) x) ≥ density A + (t : ℝ) * ρ := by
            simpa [hA0eq] using hx_cast
          have hy''': density (sliceAt A (Nat.le_of_lt hlt) (wordConcat x y')) =
              density (sliceFinset A0 (wordConcat x y')) := by
            simp [sliceAt, A0, r]
          have hmul : (t : ℝ) * ρ + ρ = ((t + 1 : ℕ) : ℝ) * ρ := by
            calc
              (t : ℝ) * ρ + ρ = (t : ℝ) * ρ + (1 : ℝ) * ρ := by simp
              _ = ((t : ℝ) + 1) * ρ := by
                    symm
                    exact add_mul (t : ℝ) 1 ρ
              _ = ((t + 1 : ℕ) : ℝ) * ρ := by
                    simp [Nat.cast_add]
          have hy''4 :
              density (sliceFinset A0 (wordConcat x y')) ≥ density A + (t : ℝ) * ρ + ρ := by
            linarith [hy'', hx']
          have hy''5 :
              density (sliceFinset A0 (wordConcat x y')) ≥
                density A + ((t + 1 : ℕ) : ℝ) * ρ := by
            have hmul' : density A + (t : ℝ) * ρ + ρ =
                density A + ((t + 1 : ℕ) : ℝ) * ρ := by
              linarith [hmul]
            linarith [hy''4, hmul']
          simpa [hy'''] using hy''5
        have hstep :
            Σ x : Word k (l + m),
              {hlt : l + m < n //
                density (sliceAt A (Nat.le_of_lt hlt) x) ≥
                  density A + ((t + 1 : ℕ) : ℝ) * ρ} := by
          exact ⟨wordConcat x y', hlt, hy'''⟩
        have hlen : (t + 1) * m = t * m + m := by
          simpa using (Nat.succ_mul t m)
        rcases hstep with ⟨x0, hlt0, hx0⟩
        have hlen' : l + m = (t + 1) * m := by
          simpa [l] using hlen.symm
        have hlt' : (t + 1) * m < n := by
          simpa [hlen'] using hlt0
        refine ⟨castWord (k := k) (n := l + m) (n' := (t + 1) * m) hlen' x0, hlt', ?_⟩
        simpa [sliceAt_castWord (A := A) (n := n) (l := l + m) (l' := (t + 1) * m)
          (hl := Nat.le_of_lt hlt0) (h := hlen') (x := x0), -castWord_comp] using hx0
  have hTle : T ≤ T := le_rfl
  obtain ⟨x, hltT, hx⟩ := hiter T hTle
  have hgt : density (sliceAt A (Nat.le_of_lt hltT) x) > 1 := by
    have hApos : 0 < density A := lt_trans hε hA
    have hT' : density A + (T : ℝ) * ρ > 1 := by
      linarith [hT, hApos]
    linarith [hx, hT']
  have hle :
      density (sliceAt A (Nat.le_of_lt hltT) x) ≤ 1 := by
    exact density_le_one (k := k) (n := n - T * m) hkpos
      (sliceAt A (Nat.le_of_lt hltT) x)
  exact (not_lt_of_ge hle hgt)

noncomputable def uniform_slice_subspace_of_steps {k m n : ℕ} (hk : 2 ≤ k) (hm : 1 ≤ m)
    {ε : ℝ} (hε : 0 < ε) (_hε1 : ε < 1)
    {A : Finset (Word k n)} (hA : density A > ε)
    (T : ℕ) (hTn : (T + 1) * m < n)
    (hT : (T : ℝ) * (ε / ((k ^ m : ℝ) - 1)) > 1) :
    Σ lhl : {l : ℕ // l < n},
      {V : SubspaceW (Fin m) (Fin k) (Fin lhl.1) //
        ∀ x ∈ subspaceFinset V,
          density (sliceAt A (Nat.le_of_lt lhl.2) x) ≥ density A - ε} :=
  Classical.choice
    (uniform_slice_subspace_of_steps_exists (k := k) (m := m) (n := n)
      hk hm hε _hε1 hA T hTn hT)

structure DensityIncrementData (k : ℕ) (δ : ℝ) : Type where
  γ : ℝ
  N : ℕ
  γ_pos : 0 < γ
  step :
    ∀ {n : ℕ} (_ : N ≤ n) (A : Finset (Word k n)),
      density A ≥ δ → ¬ hasLine A →
        {B : Finset (Word k n) // B ⊆ A ∧ density B ≥ density A + γ}

structure DHJWitness (k : ℕ) (δ : ℝ) : Type where
  N : ℕ
  line :
    ∀ n ≥ N, ∀ A : Finset (Word k n),
      density A ≥ δ → containsLine A

structure MDHJWitness (k m : ℕ) (δ : ℝ) : Type where
  N : ℕ
  subspace :
    ∀ n ≥ N, ∀ A : Finset (Word k n),
      density A ≥ δ → @containsSubspace k n m A

def mdhj_of_dhj {k : ℕ} {δ : ℝ} (h : DHJWitness k δ) : MDHJWitness k 1 δ := by
  refine ⟨h.N, ?_⟩
  intro n hn A hA
  exact containsSubspace_of_containsLine (h.line n hn A hA)

noncomputable def mdhj_of_dhj_succ {k : ℕ} (hk : 2 ≤ k)
    (dhj : ∀ δ, 0 < δ → δ ≤ 1 → DHJWitness k δ) :
    ∀ m δ, 0 < δ → δ ≤ 1 → MDHJWitness k (m + 1) δ := by
  intro m
  induction m with
  | zero =>
      intro δ hδ hδ1
      simpa using (mdhj_of_dhj (h := dhj δ hδ hδ1))
  | succ m ih =>
      intro δ hδ hδ1
      let δ1 : ℝ := δ / 2
      have hδ1pos : 0 < δ1 := by
        dsimp [δ1]
        linarith
      have hδ1le : δ1 ≤ 1 := by
        dsimp [δ1]
        linarith
      let dhj1 := dhj δ1 hδ1pos hδ1le
      let M : ℕ := dhj1.N
      let δ2 : ℝ := δ1 / ((M + 1 : ℝ) * (k + 1 : ℝ) ^ M)
      have hkpos : 0 < k := Nat.lt_of_lt_of_le (by decide : 0 < 2) hk
      have hk1pos : 0 < (k + 1 : ℝ) := by
        exact_mod_cast Nat.succ_pos k
      have hMpos : 0 < (M + 1 : ℝ) := by
        exact_mod_cast Nat.succ_pos M
      have hkpowpos : 0 < ((k + 1) ^ M : ℝ) := pow_pos hk1pos M
      have hdenompos : 0 < ((M + 1 : ℝ) * (k + 1 : ℝ) ^ M) :=
        mul_pos hMpos hkpowpos
      have hδ2pos : 0 < δ2 := by
        exact div_pos hδ1pos hdenompos
      have hδ1nonneg : 0 ≤ δ1 := by linarith
      have hdenom_ge : (1 : ℝ) ≤ (M + 1 : ℝ) * (k + 1 : ℝ) ^ M := by
        have hMge : (1 : ℝ) ≤ (M + 1 : ℝ) := by
          exact_mod_cast Nat.succ_le_succ (Nat.zero_le M)
        have hbase : (1 : ℝ) ≤ (k + 1 : ℝ) := by
          exact_mod_cast Nat.succ_le_succ (Nat.zero_le k)
        have hkpow_ge : (1 : ℝ) ≤ (k + 1 : ℝ) ^ M := one_le_pow₀ hbase
        have hMnonneg : 0 ≤ (M + 1 : ℝ) := by
          exact_mod_cast Nat.zero_le (M + 1)
        calc
          (1 : ℝ) = (1 : ℝ) * 1 := by ring
          _ ≤ (M + 1 : ℝ) * (k + 1 : ℝ) ^ M :=
            mul_le_mul hMge hkpow_ge (by linarith) hMnonneg
      have hδ2le' : δ2 ≤ δ1 := by
        exact div_le_self hδ1nonneg hdenom_ge
      have hδ2le : δ2 ≤ 1 := le_trans hδ2le' hδ1le
      let mdhj2 := ih δ2 hδ2pos hδ2le
      refine ⟨M + mdhj2.N, ?_⟩
      intro n hn A hA
      have hM : M ≤ n := le_trans (Nat.le_add_right _ _) hn
      set n1 : ℕ := n - M with hn1def
      have hMn1 : M + n1 = n := by
        calc
          M + n1 = n1 + M := by ac_rfl
          _ = n := by simpa [n1] using (Nat.sub_add_cancel hM)
      have hn1 : mdhj2.N ≤ n1 := by
        have : M + mdhj2.N ≤ M + n1 := by
          simpa [hMn1] using hn
        exact Nat.le_of_add_le_add_left this
      have hNM : n1 + M = n := by
        simpa [add_comm] using hMn1
      let A' : Finset (Word k (n1 + M)) :=
        castWordFinset (k := k) (n := n) (n' := n1 + M) hNM.symm A
      have hA' : density A' ≥ δ := by
        have hAeq : density A' = density A := by
          simp [A']
        simpa [hAeq] using hA
      have hδnonneg : 0 ≤ δ := le_of_lt hδ
      have hBspec :=
        Polymath.DHJ.denseSliceSet_spec (k := k) (n := n1) (m := M) hkpos hδnonneg A' hA'
      set B : Finset (Word k n1) := denseSliceSet A' (δ / 2)
      have hBdens : density B ≥ δ / 2 := by
        simpa [B] using hBspec.1
      have hBslice : ∀ x ∈ B, δ / 2 ≤ density (sliceFinset A' x) := by
        intro x hx
        have hx' : x ∈ denseSliceSet A' (δ / 2) := by
          simpa [B] using hx
        exact hBspec.2 x hx'
      have hkpowpos' : 0 < (k ^ n1 : ℝ) := by
        have hk' : 0 < (k : ℝ) := by exact_mod_cast hkpos
        exact pow_pos hk' n1
      have hBdens' : δ / 2 ≤ (B.card : ℝ) / (k ^ n1 : ℝ) := by
        simpa [density] using hBdens
      have hBcard : δ / 2 * (k ^ n1 : ℝ) ≤ (B.card : ℝ) :=
        (le_div_iff₀ hkpowpos').1 hBdens'
      have hBcard_pos : 0 < (B.card : ℝ) := by
        have hδ2pos' : 0 < δ / 2 := by linarith
        have hpos : 0 < δ / 2 * (k ^ n1 : ℝ) := mul_pos hδ2pos' hkpowpos'
        exact lt_of_lt_of_le hpos hBcard
      have hBnonempty : B.Nonempty := by
        have hBcard_nat : 0 < B.card := by exact_mod_cast hBcard_pos
        exact Finset.card_pos.1 hBcard_nat
      have hline_x : ∀ x ∈ B, containsLine (sliceFinset A' x) := by
        intro x hx
        have hslice := hBslice x hx
        exact dhj1.line M (by rfl) (sliceFinset A' x) hslice
      let x0 : Word k n1 := Classical.choose hBnonempty
      have hx0 : x0 ∈ B := Classical.choose_spec hBnonempty
      let l0 : LineW (Fin k) (Fin M) := (hline_x x0 hx0).1
      let lineChoice : Word k n1 → LineW (Fin k) (Fin M) :=
        fun x => if hx : x ∈ B then (hline_x x hx).1 else l0
      have hlineChoice : ∀ x ∈ B, lineFinset (lineChoice x) ⊆ sliceFinset A' x := by
        intro x hx
        simpa [lineChoice, hx] using (hline_x x hx).2
      let t : Finset (LineW (Fin k) (Fin M)) := B.image lineChoice
      have ht_nonempty : t.Nonempty := Finset.Nonempty.image hBnonempty lineChoice
      have hmaps : (B : Set (Word k n1)).MapsTo lineChoice t := by
        intro x hx
        exact Finset.mem_image.2 ⟨x, hx, rfl⟩
      have hsum_nat :
          B.card =
            Finset.sum t (fun l => (B.filter (fun x => lineChoice x = l)).card) := by
        simpa using (Finset.card_eq_sum_card_fiberwise (s := B) (t := t) hmaps)
      have hsum :
          (B.card : ℝ) =
            Finset.sum t (fun l => ((B.filter (fun x => lineChoice x = l)).card : ℝ)) := by
        exact_mod_cast hsum_nat
      have htcard : (t.card : ℝ) ≤ (M + 1 : ℝ) * (k + 1 : ℝ) ^ M := by
        have hle_nat :
            t.card ≤ Fintype.card (LineW (Fin k) (Fin M)) :=
          Finset.card_le_univ _
        have hle_real :
            (t.card : ℝ) ≤
              (Fintype.card (LineW (Fin k) (Fin M)) : ℝ) := by
          exact_mod_cast hle_nat
        have hline_card :
            (Fintype.card (LineW (Fin k) (Fin M)) : ℝ) ≤
              (M + 1 : ℝ) * (k + 1 : ℝ) ^ M := by
          exact_mod_cast (card_line_le k M)
        exact le_trans hle_real hline_card
      have hmul1 : (t.card : ℝ) * δ2 ≤ δ1 := by
        have hδ2nonneg : 0 ≤ δ2 := by linarith
        calc
          (t.card : ℝ) * δ2
              = (t.card : ℝ) * (δ1 / ((M + 1 : ℝ) * (k + 1 : ℝ) ^ M)) := by rfl
          _ ≤ ((M + 1 : ℝ) * (k + 1 : ℝ) ^ M) *
                (δ1 / ((M + 1 : ℝ) * (k + 1 : ℝ) ^ M)) := by
                exact mul_le_mul_of_nonneg_right htcard hδ2nonneg
          _ = δ1 := by
                have hdenom_ne :
                    ((M + 1 : ℝ) * (k + 1 : ℝ) ^ M) ≠ 0 := ne_of_gt hdenompos
                calc
                  (M + 1 : ℝ) * (k + 1 : ℝ) ^ M *
                        (δ1 / ((M + 1 : ℝ) * (k + 1 : ℝ) ^ M))
                      = (((M + 1 : ℝ) * (k + 1 : ℝ) ^ M) * δ1) /
                          ((M + 1 : ℝ) * (k + 1 : ℝ) ^ M) := by
                          symm
                          exact mul_div_assoc
                            ((M + 1 : ℝ) * (k + 1 : ℝ) ^ M) δ1
                            ((M + 1 : ℝ) * (k + 1 : ℝ) ^ M)
                  _ = δ1 := by
                        simpa [mul_comm] using (mul_div_cancel_left₀ δ1 hdenom_ne)
      have hmul2 :
          (t.card : ℝ) * (δ2 * (k ^ n1 : ℝ)) ≤ δ1 * (k ^ n1 : ℝ) := by
        have hkpow_nonneg : 0 ≤ (k ^ n1 : ℝ) := by
          exact le_of_lt hkpowpos'
        have hmul1' : (t.card : ℝ) * δ2 ≤ δ1 := hmul1
        have hmul1'' : (t.card : ℝ) * δ2 * (k ^ n1 : ℝ) ≤ δ1 * (k ^ n1 : ℝ) :=
          mul_le_mul_of_nonneg_right hmul1' hkpow_nonneg
        simpa [mul_assoc] using hmul1''
      have hBcard1 :
          δ1 * (k ^ n1 : ℝ) ≤ (B.card : ℝ) := by
        have hBdens1 : δ1 ≤ (B.card : ℝ) / (k ^ n1 : ℝ) := by
          have hBdens1' : δ1 ≤ density B := by
            simpa [δ1] using hBdens
          simpa [density] using hBdens1'
        exact (le_div_iff₀ hkpowpos').1 hBdens1
      have hsum_le :
          Finset.sum t (fun _ => δ2 * (k ^ n1 : ℝ)) ≤
            Finset.sum t (fun l => ((B.filter (fun x => lineChoice x = l)).card : ℝ)) := by
        have htot :
            (t.card : ℝ) * (δ2 * (k ^ n1 : ℝ)) ≤ (B.card : ℝ) :=
          le_trans hmul2 hBcard1
        calc
          Finset.sum t (fun _ => δ2 * (k ^ n1 : ℝ))
              = (t.card : ℝ) * (δ2 * (k ^ n1 : ℝ)) := by simp
          _ ≤ (B.card : ℝ) := htot
          _ = Finset.sum t (fun l => ((B.filter (fun x => lineChoice x = l)).card : ℝ)) := by
                simp [hsum]
      have hl_exists :
          ∃ l ∈ t, δ2 * (k ^ n1 : ℝ) ≤ ((B.filter (fun x => lineChoice x = l)).card : ℝ) :=
        Finset.exists_le_of_sum_le (s := t) ht_nonempty hsum_le
      let l : LineW (Fin k) (Fin M) := Classical.choose hl_exists
      have hl : l ∈ t := (Classical.choose_spec hl_exists).1
      have hlcard :
          δ2 * (k ^ n1 : ℝ) ≤ ((B.filter (fun x => lineChoice x = l)).card : ℝ) :=
        (Classical.choose_spec hl_exists).2
      set C : Finset (Word k n1) := B.filter (fun x => lineChoice x = l)
      have hCcard : δ2 * (k ^ n1 : ℝ) ≤ (C.card : ℝ) := by
        simpa [C] using hlcard
      have hCdens : density C ≥ δ2 := by
        have hCdiv : δ2 ≤ (C.card : ℝ) / (k ^ n1 : ℝ) :=
          (le_div_iff₀ hkpowpos').2 hCcard
        simpa [density] using hCdiv
      rcases mdhj2.subspace n1 hn1 C hCdens with ⟨W, hWsubset⟩
      have hline_on_W :
          ∀ x ∈ subspaceFinset W, lineFinset l ⊆ sliceFinset A' x := by
        intro x hx
        have hxC : x ∈ C := hWsubset hx
        have hxB : x ∈ B := (Finset.mem_filter.1 hxC).1
        have hxline : lineChoice x = l := (Finset.mem_filter.1 hxC).2
        have hline := hlineChoice x hxB
        simpa [hxline] using hline
      have hline_subspace :
          ∀ x ∈ subspaceFinset W,
            subspaceFinset (lineToSubspace l) ⊆ sliceFinset A' x := by
        intro x hx
        have hline := hline_on_W x hx
        simpa [subspaceFinset_lineToSubspace] using hline
      have hVsubset :
          subspaceFinset (subspaceConcat W (lineToSubspace l)) ⊆ A' :=
        subspaceConcat_subset (A := A') W (lineToSubspace l) hline_subspace
      have hV :
          containsSubspace (k := k) (n := n1 + M) (m := m + 1 + 1) A' :=
        ⟨subspaceConcat W (lineToSubspace l), hVsubset⟩
      have hV' :
          containsSubspace (k := k) (n := n) (m := m + 1 + 1)
            (castWordFinset (k := k) hNM A') :=
        containsSubspace_castWordFinset (k := k) (m := m + 1 + 1)
          (n := n1 + M) (n' := n) hNM hV
      simpa [A'] using hV'

noncomputable def density_hales_jewett
    (k : ℕ) (δ : ℝ) (hk : 2 ≤ k) (_hδ : 0 < δ) (_hδ1 : δ ≤ 1)
    (step : DensityIncrementData k δ) :
    DHJWitness k δ := by
  obtain ⟨γ, N, hγ, hinc⟩ := step
  refine ⟨N, ?_⟩
  intro n hn A hA
  have hk' : 0 < k := by
    exact Nat.lt_of_lt_of_le (by decide : 0 < 2) hk
  have hinc' :
      ∀ {A : Finset (Word k n)}, density A ≥ δ → ¬ hasLine A →
        {B : Finset (Word k n) // B ⊆ A ∧ density B ≥ density A + γ} := by
    intro A hA' hline
    exact hinc hn A hA' hline
  exact containsLine_of_increment (k := k) (n := n) hk' hγ hA hinc'

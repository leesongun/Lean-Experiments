import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Finset.Card
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.GroupWithZero.Unbundled.Basic
import Mathlib.Tactic.Linarith
import Monorepo.polymath.DHJ.LineW

open scoped BigOperators

namespace Polymath.DHJ

def Word (k n : ℕ) := Fin n → Fin k

instance (k n : ℕ) : Fintype (Word k n) := by
  dsimp [Word]
  infer_instance

instance (k n : ℕ) : DecidableEq (Word k n) := by
  classical
  dsimp [Word]
  infer_instance

lemma lineW_injective (k n : ℕ) :
    Function.Injective (fun l : LineW (Fin k) (Fin n) => (l.proper.1, l.idxFun)) := by
  intro l₁ l₂ h
  cases l₁ with
  | mk idx₁ prop₁ =>
      cases l₂ with
      | mk idx₂ prop₂ =>
          have hproper : prop₁.1 = prop₂.1 := by
            simpa using congrArg Prod.fst h
          have hidx : idx₁ = idx₂ := by
            simpa using congrArg Prod.snd h
          cases hidx
          have hprop : prop₁ = prop₂ := by
            apply Subtype.ext
            simpa using hproper
          cases hprop
          rfl

noncomputable instance (k n : ℕ) : Fintype (LineW (Fin k) (Fin n)) := by
  classical
  let _ : Finite (LineW (Fin k) (Fin n)) :=
    Finite.of_injective (fun l : LineW (Fin k) (Fin n) => (l.proper.1, l.idxFun))
      (lineW_injective k n)
  exact Fintype.ofFinite (LineW (Fin k) (Fin n))

def wordConcat {k n m : ℕ} (x : Word k n) (y : Word k m) : Word k (n + m) :=
  Fin.append x y

def emptyWord (k : ℕ) : Word k 0 := (Fin.elim0)

def wordPrefix {k n m : ℕ} (w : Word k (n + m)) : Word k n :=
  fun i => w (Fin.castAdd m i)

def wordSuffix {k n m : ℕ} (w : Word k (n + m)) : Word k m :=
  fun i => w (Fin.natAdd n i)

@[simp] lemma wordConcat_left {k n m : ℕ} (x : Word k n) (y : Word k m) (i : Fin n) :
    wordConcat x y (Fin.castAdd m i) = x i := by
  simp [wordConcat]

@[simp] lemma wordConcat_right {k n m : ℕ} (x : Word k n) (y : Word k m) (i : Fin m) :
    wordConcat x y (Fin.natAdd n i) = y i := by
  simp [wordConcat]

@[simp] lemma wordPrefix_wordConcat {k n m : ℕ} (x : Word k n) (y : Word k m) :
    wordPrefix (wordConcat x y) = x := by
  funext i
  simp [wordPrefix]

@[simp] lemma wordSuffix_wordConcat {k n m : ℕ} (x : Word k n) (y : Word k m) :
    wordSuffix (wordConcat x y) = y := by
  funext i
  simp [wordSuffix]

lemma wordConcat_prefix_suffix {k n m : ℕ} (w : Word k (n + m)) :
    wordConcat (wordPrefix w) (wordSuffix w) = w := by
  funext i
  refine Fin.addCases ?_ ?_ i
  · intro i
    simp [wordConcat, wordPrefix]
  · intro i
    simp [wordConcat, wordSuffix]

lemma wordConcat_assoc {k n m r : ℕ} (x : Word k n) (y : Word k m) (z : Word k r) :
    wordConcat (wordConcat x y) z =
      (wordConcat x (wordConcat y z)) ∘ Fin.cast (Nat.add_assoc n m r) := by
  simpa [wordConcat] using (Fin.append_assoc (a := x) (b := y) (c := z))

def wordConcatEquiv {k n m : ℕ} : (Word k n × Word k m) ≃ Word k (n + m) where
  toFun p := wordConcat p.1 p.2
  invFun w := (wordPrefix w, wordSuffix w)
  left_inv p := by
    cases p with
    | mk x y =>
        simp [wordPrefix_wordConcat, wordSuffix_wordConcat]
  right_inv w := by
    simp [wordConcat_prefix_suffix]

lemma wordConcat_injective {k n m : ℕ} :
    Function.Injective (fun p : Word k n × Word k m => wordConcat p.1 p.2) := by
  intro p q h
  exact (wordConcatEquiv (k := k) (n := n) (m := m)).injective h

def concatFinset {k n m : ℕ} (A : Finset (Word k n)) (B : Finset (Word k m)) :
    Finset (Word k (n + m)) :=
  (A.product B).image (fun p => wordConcat p.1 p.2)

lemma mem_concatFinset {k n m : ℕ} {A : Finset (Word k n)} {B : Finset (Word k m)}
    {w : Word k (n + m)} :
    w ∈ concatFinset A B ↔ ∃ x ∈ A, ∃ y ∈ B, wordConcat x y = w := by
  classical
  constructor
  · intro hw
    rcases Finset.mem_image.1 hw with ⟨p, hp, rfl⟩
    rcases Finset.mem_product.1 hp with ⟨hx, hy⟩
    exact ⟨p.1, hx, p.2, hy, rfl⟩
  · rintro ⟨x, hx, y, hy, rfl⟩
    refine Finset.mem_image.2 ?_
    refine ⟨(x, y), ?_, rfl⟩
    exact Finset.mem_product.2 ⟨hx, hy⟩

def sliceFinset {k n m : ℕ} (A : Finset (Word k (n + m))) (x : Word k n) :
  Finset (Word k m) :=
  Finset.filter (fun y => wordConcat x y ∈ A) Finset.univ

@[simp] lemma mem_sliceFinset {k n m : ℕ} (A : Finset (Word k (n + m)))
    (x : Word k n) (y : Word k m) :
    y ∈ sliceFinset A x ↔ wordConcat x y ∈ A := by
  simp [sliceFinset]


lemma mem_sliceFinset_prefix_suffix {k n m : ℕ} (A : Finset (Word k (n + m)))
    (w : Word k (n + m)) :
    wordSuffix w ∈ sliceFinset A (wordPrefix w) ↔ w ∈ A := by
  simp [wordConcat_prefix_suffix]

lemma card_sigma_slices {k n m : ℕ} (A : Finset (Word k (n + m))) :
    (Finset.univ.sigma (fun x => sliceFinset A x)).card =
      Finset.sum (Finset.univ : Finset (Word k n)) (fun x => (sliceFinset A x).card) := by
  classical
  simp

lemma sigma_slices_image {k n m : ℕ} (A : Finset (Word k (n + m))) :
    (Finset.univ.sigma (fun x => sliceFinset A x)).image
      (fun p => wordConcat p.1 p.2) = A := by
  classical
  ext w
  constructor
  · intro hw
    rcases Finset.mem_image.1 hw with ⟨p, hp, rfl⟩
    rcases (Finset.mem_sigma.1 hp) with ⟨hp, hy⟩
    simpa using (Finset.mem_filter.1 hy).2
  · intro hw
    refine Finset.mem_image.2 ?_
    refine ⟨⟨wordPrefix w, wordSuffix w⟩, ?_, ?_⟩
    · apply Finset.mem_sigma.2
      refine ⟨Finset.mem_univ _, ?_⟩
      have : wordConcat (wordPrefix w) (wordSuffix w) ∈ A := by
        simpa [wordConcat_prefix_suffix] using hw
      exact (Finset.mem_filter.2 ⟨Finset.mem_univ _, this⟩)
    · simp [wordConcat_prefix_suffix]

lemma sum_card_slice_eq_card {k n m : ℕ} (A : Finset (Word k (n + m))) :
    Finset.sum (Finset.univ : Finset (Word k n)) (fun x => (sliceFinset A x).card) = A.card := by
  classical
  have hcard :
      (Finset.univ.sigma (fun x => sliceFinset A x)).card = A.card := by
    have hinj : Function.Injective (fun p : Σ x : Word k n, Word k m =>
        wordConcat p.1 p.2) := by
      intro p q h
      have h' : (⟨p.1, p.2⟩ : Word k n × Word k m) =
          (⟨q.1, q.2⟩ : Word k n × Word k m) := wordConcat_injective h
      cases p; cases q
      cases h'
      rfl
    have himage := sigma_slices_image (k := k) (n := n) (m := m) A
    calc
      (Finset.univ.sigma (fun x => sliceFinset A x)).card
          = ((Finset.univ.sigma (fun x => sliceFinset A x)).image
              (fun p => wordConcat p.1 p.2)).card := by
                symm
                exact Finset.card_image_of_injective _ hinj
      _ = A.card := by simp [himage]
  simpa [card_sigma_slices] using hcard


def lineFinset {k n : ℕ} (l : LineW (Fin k) (Fin n)) : Finset (Word k n) :=
  Finset.univ.image (fun a => l a)

def subspaceFinset {k n m : ℕ} (V : SubspaceW (Fin m) (Fin k) (Fin n)) :
    Finset (Word k n) :=
  Finset.univ.image (fun a => V a)

def fullSubspace (k m : ℕ) : SubspaceW (Fin m) (Fin k) (Fin m) where
  idxFun i := Sum.inr i
  proper e := ⟨e, rfl⟩

@[simp] lemma fullSubspace_apply {k m : ℕ} (a : Word k m) (i : Fin m) :
    fullSubspace k m a i = a i := by
  rfl

@[simp] lemma subspaceFinset_fullSubspace {k m : ℕ} :
    subspaceFinset (fullSubspace k m) = (Finset.univ : Finset (Word k m)) := by
  classical
  ext x
  constructor
  · intro _hx
    exact Finset.mem_univ x
  · intro _hx
    refine Finset.mem_image.2 ?_
    refine ⟨x, Finset.mem_univ _, ?_⟩
    funext i
    rfl

def lineConcatRight {k n m : ℕ} (x : Word k n)
    (l : LineW (Fin k) (Fin m)) :
    LineW (Fin k) (Fin (n + m)) where
  idxFun i := Fin.addCases (fun i => some (x i)) (fun i => l.idxFun i) i
  proper := by
    refine ⟨Fin.natAdd n l.proper.1, ?_⟩
    simp [l.proper.2]

@[simp] lemma lineConcatRight_apply {k n m : ℕ} (x : Word k n)
    (l : LineW (Fin k) (Fin m)) (a : Fin k) :
    lineConcatRight x l a = wordConcat x (l a) := by
  funext i
  refine Fin.addCases ?_ ?_ i
  · intro i
    simp [lineConcatRight, wordConcat]
  · intro i
    simp [lineConcatRight, wordConcat]

lemma lineFinset_lineConcatRight {k n m : ℕ} (x : Word k n)
    (l : LineW (Fin k) (Fin m)) :
    lineFinset (lineConcatRight x l) =
      (lineFinset l).image (fun y => wordConcat x y) := by
  classical
  ext w
  constructor
  · intro hw
    rcases Finset.mem_image.1 hw with ⟨a, _ha, rfl⟩
    refine Finset.mem_image.2 ?_
    refine ⟨l a, ?_, ?_⟩
    · exact Finset.mem_image.2 ⟨a, Finset.mem_univ _, rfl⟩
    · simp [lineConcatRight_apply]
  · intro hw
    rcases Finset.mem_image.1 hw with ⟨y, hy, rfl⟩
    rcases Finset.mem_image.1 hy with ⟨a, _ha, rfl⟩
    refine Finset.mem_image.2 ?_
    refine ⟨a, Finset.mem_univ _, ?_⟩
    simp [lineConcatRight_apply]

lemma lineConcatRight_subset {k n m : ℕ} {A : Finset (Word k (n + m))}
    (x : Word k n) (l : LineW (Fin k) (Fin m))
    (h : lineFinset l ⊆ sliceFinset A x) :
    lineFinset (lineConcatRight x l) ⊆ A := by
  intro w hw
  have hw' : w ∈ (lineFinset l).image (fun y => wordConcat x y) := by
    simpa [lineFinset_lineConcatRight] using hw
  rcases Finset.mem_image.1 hw' with ⟨y, hy, rfl⟩
  have : y ∈ sliceFinset A x := h hy
  simpa [mem_sliceFinset] using this

def subspaceConcatRight {k n m n' : ℕ} (x : Word k n)
    (V : SubspaceW (Fin m) (Fin k) (Fin n')) :
    SubspaceW (Fin m) (Fin k) (Fin (n + n')) where
  idxFun i := Fin.addCases (fun i => Sum.inl (x i)) (fun i => V.idxFun i) i
  proper := by
    intro e
    rcases V.proper e with ⟨i, hi⟩
    refine ⟨Fin.natAdd n i, ?_⟩
    simp [hi]

@[simp] lemma subspaceConcatRight_apply {k n m n' : ℕ} (x : Word k n)
    (V : SubspaceW (Fin m) (Fin k) (Fin n'))
    (a : Fin m → Fin k) :
    subspaceConcatRight x V a = wordConcat x (V a) := by
  funext i
  refine Fin.addCases ?_ ?_ i
  · intro i
    simp [subspaceConcatRight, wordConcat, SubspaceW.apply_def]
  · intro i
    simp [subspaceConcatRight, wordConcat, SubspaceW.apply_def]

lemma subspaceFinset_subspaceConcatRight {k n m n' : ℕ} (x : Word k n)
    (V : SubspaceW (Fin m) (Fin k) (Fin n')) :
    subspaceFinset (subspaceConcatRight x V) =
      (subspaceFinset V).image (fun y => wordConcat x y) := by
  classical
  ext w
  constructor
  · intro hw
    rcases Finset.mem_image.1 hw with ⟨a, _ha, rfl⟩
    refine Finset.mem_image.2 ?_
    refine ⟨V a, ?_, ?_⟩
    · exact Finset.mem_image.2 ⟨a, Finset.mem_univ _, rfl⟩
    · simp [subspaceConcatRight_apply]
  · intro hw
    rcases Finset.mem_image.1 hw with ⟨y, hy, rfl⟩
    rcases Finset.mem_image.1 hy with ⟨a, _ha, rfl⟩
    refine Finset.mem_image.2 ?_
    refine ⟨a, Finset.mem_univ _, ?_⟩
    simp [subspaceConcatRight_apply]

lemma subspaceConcatRight_subset {k n m n' : ℕ} {A : Finset (Word k (n + n'))}
    (x : Word k n) (V : SubspaceW (Fin m) (Fin k) (Fin n'))
    (h : subspaceFinset V ⊆ sliceFinset A x) :
    subspaceFinset (subspaceConcatRight x V) ⊆ A := by
  intro w hw
  have hw' : w ∈ (subspaceFinset V).image (fun y => wordConcat x y) := by
    simpa [subspaceFinset_subspaceConcatRight] using hw
  rcases Finset.mem_image.1 hw' with ⟨y, hy, rfl⟩
  have : y ∈ sliceFinset A x := h hy
  simpa [mem_sliceFinset] using this

def subspaceConcat {k n n' m m' : ℕ}
    (W : SubspaceW (Fin m) (Fin k) (Fin n))
    (V : SubspaceW (Fin m') (Fin k) (Fin n')) :
    SubspaceW (Fin (m + m')) (Fin k) (Fin (n + n')) where
  idxFun i :=
    Fin.addCases
      (fun i => match W.idxFun i with
        | Sum.inl a => Sum.inl a
        | Sum.inr e => Sum.inr (Fin.castAdd m' e))
      (fun i => match V.idxFun i with
        | Sum.inl a => Sum.inl a
        | Sum.inr e => Sum.inr (Fin.natAdd m e))
      i
  proper := by
    intro e
    refine Fin.addCases ?_ ?_ e
    · intro e'
      rcases W.proper e' with ⟨i, hi⟩
      refine ⟨Fin.castAdd n' i, ?_⟩
      simp [hi]
    · intro e'
      rcases V.proper e' with ⟨i, hi⟩
      refine ⟨Fin.natAdd n i, ?_⟩
      simp [hi]

@[simp] lemma subspaceConcat_apply {k n n' m m' : ℕ}
    (W : SubspaceW (Fin m) (Fin k) (Fin n))
    (V : SubspaceW (Fin m') (Fin k) (Fin n'))
    (a : Fin (m + m') → Fin k) :
    subspaceConcat W V a =
      wordConcat
        (W (fun i => a (Fin.castAdd m' i)))
        (V (fun i => a (Fin.natAdd m i))) := by
  funext i
  refine Fin.addCases ?_ ?_ i
  · intro i
    cases h : W.idxFun i with
    | inl a =>
        simp [subspaceConcat, wordConcat, SubspaceW.apply_def, h]
    | inr e =>
        simp [subspaceConcat, wordConcat, SubspaceW.apply_def, h]
  · intro i
    cases h : V.idxFun i with
    | inl a =>
        simp [subspaceConcat, wordConcat, SubspaceW.apply_def, h]
    | inr e =>
        simp [subspaceConcat, wordConcat, SubspaceW.apply_def, h]

lemma subspaceConcat_subset {k n n' m m' : ℕ} {A : Finset (Word k (n + n'))}
    (W : SubspaceW (Fin m) (Fin k) (Fin n))
    (V : SubspaceW (Fin m') (Fin k) (Fin n'))
    (h : ∀ x ∈ subspaceFinset W, subspaceFinset V ⊆ sliceFinset A x) :
    subspaceFinset (subspaceConcat W V) ⊆ A := by
  intro w hw
  rcases Finset.mem_image.1 hw with ⟨a, _ha, rfl⟩
  let aL : Fin m → Fin k := fun i => a (Fin.castAdd m' i)
  let aR : Fin m' → Fin k := fun i => a (Fin.natAdd m i)
  have hx : W aL ∈ subspaceFinset W := by
    refine Finset.mem_image.2 ?_
    exact ⟨aL, Finset.mem_univ _, rfl⟩
  have hy : V aR ∈ subspaceFinset V := by
    refine Finset.mem_image.2 ?_
    exact ⟨aR, Finset.mem_univ _, rfl⟩
  have hslice : V aR ∈ sliceFinset A (W aL) := (h (W aL) hx) hy
  have hmem : wordConcat (W aL) (V aR) ∈ A := by
    exact (mem_sliceFinset A (W aL) (V aR)).1 hslice
  simpa [subspaceConcat_apply, aL, aR] using hmem

noncomputable def density {k n : ℕ} (A : Finset (Word k n)) : ℝ :=
  A.card / (k ^ n : ℝ)

def castWordFinset {k n n' : ℕ} (h : n = n') (A : Finset (Word k n)) :
    Finset (Word k n') := by
  cases h
  exact A

def castWord {k n n' : ℕ} (h : n = n') (w : Word k n) : Word k n' := by
  cases h
  exact w

@[simp] lemma castWord_eq {k n : ℕ} (h : n = n) (w : Word k n) :
    castWord (k := k) h w = w := by
  cases h
  rfl

@[simp] lemma castWord_apply {k n n' : ℕ} (h : n = n') (w : Word k n) (i : Fin n') :
    castWord (k := k) h w i = w (Fin.cast h.symm i) := by
  cases h
  rfl

@[simp] lemma castWord_trans {k n n' n'' : ℕ} (h₁ : n = n') (h₂ : n' = n'')
    (w : Word k n) :
    castWord (k := k) h₂ (castWord (k := k) h₁ w) =
      castWord (k := k) (h₁.trans h₂) w := by
  cases h₁
  cases h₂
  rfl

@[simp] lemma castWord_comp {k n n' : ℕ} (h : n = n') (w : Word k n) :
    castWord (k := k) h w = w ∘ Fin.cast h.symm := by
  funext i
  simp [castWord_apply]

@[simp] lemma wordConcat_empty_left {k n : ℕ} (y : Word k n) :
    wordConcat (emptyWord k) y =
      castWord (k := k) (n := n) (n' := 0 + n) (Nat.zero_add n).symm y := by
  have h : Fin.append (emptyWord k) y = y ∘ Fin.cast (Nat.zero_add n) := by
    change Fin.append (Fin.elim0) y = y ∘ Fin.cast (Nat.zero_add n)
    exact Fin.elim0_append (v := y)
  funext i
  have h' := congrArg (fun f => f i) h
  simpa [wordConcat, castWord_apply] using h'

@[simp] lemma mem_castWordFinset {k n n' : ℕ} (h : n = n') (A : Finset (Word k n))
    (w : Word k n') :
    w ∈ castWordFinset (k := k) h A ↔ castWord (k := k) h.symm w ∈ A := by
  cases h
  rfl

@[simp] lemma sliceFinset_empty {k n : ℕ} (A : Finset (Word k n)) :
    sliceFinset (k := k) (n := 0) (m := n)
        (castWordFinset (k := k) (n := n) (n' := 0 + n) (Nat.zero_add n).symm A)
        (emptyWord k) = A := by
  ext y
  simp [mem_sliceFinset, wordConcat_empty_left, mem_castWordFinset, castWord_trans, castWord_eq,
    -castWord_comp]

@[simp] lemma density_castWordFinset {k n n' : ℕ} (h : n = n') (A : Finset (Word k n)) :
    density (castWordFinset (k := k) h A) = density A := by
  cases h
  rfl

@[simp] lemma castWordFinset_trans {k n n' n'' : ℕ} (h₁ : n = n') (h₂ : n' = n'')
    (A : Finset (Word k n)) :
    castWordFinset (k := k) h₂ (castWordFinset (k := k) h₁ A) =
      castWordFinset (k := k) (h₁.trans h₂) A := by
  cases h₁
  cases h₂
  rfl

@[simp] lemma castWordFinset_eq {k n : ℕ} (h : n = n) (A : Finset (Word k n)) :
    castWordFinset (k := k) h A = A := by
  cases h
  rfl

lemma sliceFinset_slice {k n m r : ℕ} (A : Finset (Word k ((n + m) + r)))
    (x : Word k n) (y : Word k m) :
    sliceFinset
        (sliceFinset
          (castWordFinset (k := k) (n := (n + m) + r) (n' := n + (m + r))
            (Nat.add_assoc n m r) A) x) y =
      sliceFinset A (wordConcat x y) := by
  classical
  ext z
  simp [mem_sliceFinset, wordConcat_assoc]

def castSubspace {k m n n' : ℕ} (h : n = n')
    (V : SubspaceW (Fin m) (Fin k) (Fin n)) :
    SubspaceW (Fin m) (Fin k) (Fin n') := by
  cases h
  exact V

@[simp] lemma subspaceFinset_castSubspace {k m n n' : ℕ} (h : n = n')
    (V : SubspaceW (Fin m) (Fin k) (Fin n)) :
    subspaceFinset (castSubspace (k := k) (m := m) h V) =
      castWordFinset (k := k) h (subspaceFinset V) := by
  cases h
  rfl

lemma density_le_one {k n : ℕ} (hk : 0 < k) (A : Finset (Word k n)) :
    density A ≤ 1 := by
  have hcard_nat : A.card ≤ k ^ n := by
    have hcard_univ : Fintype.card (Word k n) = k ^ n := by
      simp [Word]
    have hcard : A.card ≤ Fintype.card (Word k n) := Finset.card_le_univ A
    simpa [hcard_univ] using hcard
  have hcard : (A.card : ℝ) ≤ (k ^ n : ℝ) := by
    exact_mod_cast hcard_nat
  have hpos : 0 < (k ^ n : ℝ) := by
    have hk' : 0 < (k : ℝ) := by exact_mod_cast hk
    simpa [Nat.cast_pow] using (pow_pos hk' n)
  have hdiv : (A.card : ℝ) / (k ^ n : ℝ) ≤ 1 := by
    have hmul : (A.card : ℝ) ≤ 1 * (k ^ n : ℝ) := by
      simpa using hcard
    exact (div_le_iff₀ hpos).2 (by simpa using hmul)
  simpa [density] using hdiv

noncomputable def densityIn {k n m : ℕ} (A : Finset (Word k n))
    (V : SubspaceW (Fin m) (Fin k) (Fin n)) : ℝ :=
  (A ∩ subspaceFinset V).card / (subspaceFinset V).card

lemma sum_density_slice_eq_density {k n m : ℕ} (hk : 0 < k)
    (A : Finset (Word k (n + m))) :
    Finset.sum (Finset.univ : Finset (Word k n)) (fun x => density (sliceFinset A x)) =
      (k ^ n : ℝ) * density A := by
  classical
  have hsum_nat :
      Finset.sum (Finset.univ : Finset (Word k n)) (fun x => (sliceFinset A x).card) = A.card :=
    sum_card_slice_eq_card (k := k) (n := n) (m := m) A
  have hsum :
      (Finset.sum (Finset.univ : Finset (Word k n))
          (fun x => (sliceFinset A x).card) : ℝ) = (A.card : ℝ) := by
    exact_mod_cast hsum_nat
  have hk' : (k : ℝ) ≠ 0 := by
    exact_mod_cast (ne_of_gt hk)
  have hkpow : (k ^ n : ℝ) ≠ 0 := by
    exact pow_ne_zero _ hk'
  calc
    Finset.sum (Finset.univ : Finset (Word k n)) (fun x => density (sliceFinset A x))
        = Finset.sum (Finset.univ : Finset (Word k n))
            (fun x => ((sliceFinset A x).card : ℝ) / (k ^ m : ℝ)) := by
              simp [density]
    _ = (Finset.sum (Finset.univ : Finset (Word k n))
            (fun x => ((sliceFinset A x).card : ℝ))) / (k ^ m : ℝ) := by
              simpa using
                (Finset.sum_div (s := (Finset.univ : Finset (Word k n)))
                  (f := fun x => ((sliceFinset A x).card : ℝ)) (a := (k ^ m : ℝ))).symm
    _ = (A.card : ℝ) / (k ^ m : ℝ) := by simp [hsum]
    _ = (k ^ n : ℝ) * density A := by
      calc
        (A.card : ℝ) / (k ^ m : ℝ)
            = ((k ^ n : ℝ) * (A.card : ℝ)) / ((k ^ n : ℝ) * (k ^ m : ℝ)) := by
                symm
                exact mul_div_mul_left (A.card : ℝ) (k ^ m : ℝ) hkpow
        _ = ((k ^ n : ℝ) * (A.card : ℝ)) / (k ^ (n + m) : ℝ) := by
              simp [pow_add]
        _ = (k ^ n : ℝ) * ((A.card : ℝ) / (k ^ (n + m) : ℝ)) := by
              simp [mul_div_assoc]
        _ = (k ^ n : ℝ) * density A := by
              simp [density]

noncomputable def denseSliceSet {k n m : ℕ} (A : Finset (Word k (n + m))) (δ : ℝ) :
    Finset (Word k n) :=
  Finset.filter (fun x => δ ≤ density (sliceFinset A x)) Finset.univ

@[simp] lemma mem_denseSliceSet {k n m : ℕ} (A : Finset (Word k (n + m))) (δ : ℝ)
    (x : Word k n) :
    x ∈ denseSliceSet A δ ↔ δ ≤ density (sliceFinset A x) := by
  simp [denseSliceSet]

lemma density_denseSliceSet {k n m : ℕ} (hk : 0 < k) {δ : ℝ} (hδ : 0 ≤ δ)
    (A : Finset (Word k (n + m))) (hA : density A ≥ δ) :
    density (denseSliceSet A (δ / 2)) ≥ δ / 2 := by
  classical
  set B := denseSliceSet A (δ / 2) with hB
  let f : Word k n → ℝ := fun x => density (sliceFinset A x)
  let p : Word k n → Prop := fun x => δ / 2 ≤ f x
  have hsum_eq :
      Finset.sum (Finset.univ : Finset (Word k n)) f = (k ^ n : ℝ) * density A :=
    sum_density_slice_eq_density (k := k) (n := n) (m := m) hk A
  have hk0 : 0 ≤ (k ^ n : ℝ) := by
    exact pow_nonneg (by exact_mod_cast (Nat.zero_le k)) n
  have hkpos : 0 < (k ^ n : ℝ) := by
    have hk' : 0 < (k : ℝ) := by exact_mod_cast hk
    exact pow_pos hk' n
  have hsum_ge : (k ^ n : ℝ) * δ ≤ Finset.sum (Finset.univ : Finset (Word k n)) f := by
    calc
      (k ^ n : ℝ) * δ ≤ (k ^ n : ℝ) * density A := mul_le_mul_of_nonneg_left hA hk0
      _ = Finset.sum (Finset.univ : Finset (Word k n)) f := by
        symm
        exact hsum_eq
  have hsplit :
      Finset.sum (Finset.univ : Finset (Word k n)) f =
        Finset.sum (Finset.univ.filter p) f +
        Finset.sum (Finset.univ.filter fun x => f x < δ / 2) f := by
    simpa [p] using
      (Finset.sum_filter_add_sum_filter_not (s := (Finset.univ : Finset (Word k n)))
        (p := p) (f := f)).symm
  have hsum_B :
      Finset.sum (Finset.univ.filter p) f ≤ (Finset.card (Finset.univ.filter p) : ℝ) := by
    have hsum_B' :
        Finset.sum (Finset.univ.filter p) f ≤
          Finset.sum (Finset.univ.filter p) (fun _ => (1 : ℝ)) := by
      refine Finset.sum_le_sum (s := Finset.univ.filter p) ?_
      intro x hx
      have : f x ≤ 1 := by
        simpa [f] using (density_le_one (k := k) (n := m) hk (sliceFinset A x))
      simpa using this
    simpa using hsum_B'
  have hsum_notB :
      Finset.sum (Finset.univ.filter (fun x => f x < δ / 2)) f ≤
        (k ^ n : ℝ) * (δ / 2) := by
    have hsum_le :
        Finset.sum (Finset.univ.filter (fun x => f x < δ / 2)) f ≤
          (Finset.card (Finset.univ.filter (fun x => f x < δ / 2)) : ℝ) * (δ / 2) := by
      have hsum_le' :
          Finset.sum (Finset.univ.filter (fun x => f x < δ / 2)) f ≤
            Finset.sum (Finset.univ.filter (fun x => f x < δ / 2)) (fun _ => (δ / 2)) := by
        refine Finset.sum_le_sum (s := Finset.univ.filter (fun x => f x < δ / 2)) ?_
        intro x hx
        have hxlt : f x < δ / 2 := (Finset.mem_filter.1 hx).2
        exact le_of_lt hxlt
      simpa using hsum_le'
    have hcard_le :
        (Finset.card (Finset.univ.filter (fun x => f x < δ / 2)) : ℝ) ≤ (k ^ n : ℝ) := by
      have hcard_le_nat :
          (Finset.univ.filter (fun x => f x < δ / 2)).card ≤ Fintype.card (Word k n) :=
        Finset.card_le_univ _
      have hcard_le_nat' : (Finset.univ.filter (fun x => f x < δ / 2)).card ≤ k ^ n := by
        simpa [Word] using hcard_le_nat
      exact_mod_cast hcard_le_nat'
    have hδ' : 0 ≤ δ / 2 := by linarith
    exact le_trans hsum_le (mul_le_mul_of_nonneg_right hcard_le hδ')
  have hsum_le_total :
      Finset.sum (Finset.univ : Finset (Word k n)) f ≤
        (B.card : ℝ) + (k ^ n : ℝ) * (δ / 2) := by
    have hsum_le' :
        Finset.sum (Finset.univ : Finset (Word k n)) f ≤
          (Finset.card (Finset.univ.filter p) : ℝ) +
            (k ^ n : ℝ) * (δ / 2) := by
      calc
        Finset.sum (Finset.univ : Finset (Word k n)) f
            = Finset.sum (Finset.univ.filter p) f +
                Finset.sum (Finset.univ.filter fun x => f x < δ / 2) f := hsplit
        _ ≤ (Finset.card (Finset.univ.filter p) : ℝ) +
              (k ^ n : ℝ) * (δ / 2) := by
                exact add_le_add hsum_B hsum_notB
    simpa [B, denseSliceSet, p, f] using hsum_le'
  have hb : (k ^ n : ℝ) * (δ / 2) ≤ (B.card : ℝ) := by
    linarith [hsum_ge, hsum_le_total]
  have hBdens : δ / 2 ≤ (B.card : ℝ) / (k ^ n : ℝ) := by
    refine (le_div_iff₀ hkpos).2 ?_
    simpa [mul_comm] using hb
  simpa [density, B] using hBdens

lemma denseSliceSet_spec {k n m : ℕ} (hk : 0 < k) {δ : ℝ} (hδ : 0 ≤ δ)
    (A : Finset (Word k (n + m))) (hA : density A ≥ δ) :
    density (denseSliceSet A (δ / 2)) ≥ δ / 2 ∧
      ∀ x ∈ denseSliceSet A (δ / 2), δ / 2 ≤ density (sliceFinset A x) := by
  refine ⟨density_denseSliceSet hk hδ A hA, ?_⟩
  intro x hx
  exact (mem_denseSliceSet A (δ / 2) x).1 hx

def containsLine {k n : ℕ} (A : Finset (Word k n)) : Type :=
  {l : LineW (Fin k) (Fin n) // lineFinset l ⊆ A}

def containsSubspace {k n m : ℕ} (A : Finset (Word k n)) : Type :=
  {V : SubspaceW (Fin m) (Fin k) (Fin n) // subspaceFinset V ⊆ A}

def containsSubspace_castWordFinset {k m n n' : ℕ} (h : n = n') {A : Finset (Word k n)} :
    containsSubspace (k := k) (n := n) (m := m) A →
      containsSubspace (k := k) (n := n') (m := m) (castWordFinset (k := k) h A) := by
  cases h
  intro hA
  simpa using hA

def containsLine_of_slice {k n m : ℕ} (x : Word k n) {A : Finset (Word k (n + m))} :
    containsLine (sliceFinset A x) → containsLine A := by
  rintro ⟨l, hl⟩
  refine ⟨lineConcatRight x l, ?_⟩
  exact lineConcatRight_subset (A := A) x l hl

def containsSubspace_of_slice {k n m m' : ℕ} (x : Word k n) {A : Finset (Word k (n + m'))} :
    containsSubspace (k := k) (n := m') (m := m) (sliceFinset A x) →
      containsSubspace (k := k) (n := n + m') (m := m) A := by
  rintro ⟨V, hV⟩
  refine ⟨subspaceConcatRight x V, ?_⟩
  exact subspaceConcatRight_subset (A := A) x V hV

lemma card_line_le (k n : ℕ) :
    Fintype.card (LineW (Fin k) (Fin n)) ≤ (n + 1) * (k + 1) ^ n := by
  classical
  have hinj := lineW_injective k n
  have hcard :
      Fintype.card (Fin n × (Fin n → Option (Fin k))) = n * (k + 1) ^ n := by
    simp
  have hle :
      Fintype.card (LineW (Fin k) (Fin n)) ≤ n * (k + 1) ^ n := by
    simpa [hcard] using
      (Fintype.card_le_of_injective
        (f := fun l : LineW (Fin k) (Fin n) => (l.proper.1, l.idxFun)) hinj)
  have hle' : n * (k + 1) ^ n ≤ (n + 1) * (k + 1) ^ n := by
    exact Nat.mul_le_mul_right _ (Nat.le_succ n)
  exact le_trans hle hle'

abbrev hasLine {k n : ℕ} (A : Finset (Word k n)) : Prop :=
  Nonempty (containsLine A)

abbrev hasSubspace {k n m : ℕ} (A : Finset (Word k n)) : Prop :=
  Nonempty (containsSubspace (k := k) (n := n) (m := m) A)

/-
`containsLine A` is a subtype that *records an actual line* inside `A`.
We use `hasLine A` only for classical reasoning; extracting a witness
uses `Classical.choice` and is therefore noncomputable.
-/

def containsLine_of_subset {k n : ℕ} {A B : Finset (Word k n)} (hAB : A ⊆ B) :
    containsLine A → containsLine B := by
  rintro ⟨l, hline⟩
  refine ⟨l, ?_⟩
  intro w hw
  exact hAB (hline hw)

def containsSubspace_of_subset {k n m : ℕ} {A B : Finset (Word k n)} (hAB : A ⊆ B) :
    containsSubspace (k := k) (n := n) (m := m) A →
      containsSubspace (k := k) (n := n) (m := m) B := by
  rintro ⟨V, hV⟩
  refine ⟨V, ?_⟩
  intro w hw
  exact hAB (hV hw)

def hasLine_of_subset {k n : ℕ} {A B : Finset (Word k n)} (hAB : A ⊆ B) :
    hasLine A → hasLine B := by
  rintro ⟨h⟩
  exact ⟨containsLine_of_subset hAB h⟩

def hasSubspace_of_subset {k n m : ℕ} {A B : Finset (Word k n)} (hAB : A ⊆ B) :
    hasSubspace (k := k) (n := n) (m := m) A →
      hasSubspace (k := k) (n := n) (m := m) B := by
  rintro ⟨h⟩
  exact ⟨containsSubspace_of_subset hAB h⟩

def lineToSubspace {k n : ℕ} (l : LineW (Fin k) (Fin n)) :
    SubspaceW (Fin 1) (Fin k) (Fin n) where
  idxFun i := match l.idxFun i with
    | none => Sum.inr ⟨0, by decide⟩
    | some a => Sum.inl a
  proper := by
    intro e
    refine ⟨l.proper.1, ?_⟩
    have he : e = ⟨0, by decide⟩ := Subsingleton.elim _ _
    simp [l.proper.2, he]

@[simp] lemma lineToSubspace_apply {k n : ℕ} (l : LineW (Fin k) (Fin n))
    (a : Fin 1 → Fin k) (i : Fin n) :
    lineToSubspace l a i = l (a ⟨0, by decide⟩) i := by
  cases h : l.idxFun i with
  | none =>
      simp [lineToSubspace, SubspaceW.apply_def, h]
  | some b =>
      simp [lineToSubspace, SubspaceW.apply_def, h]

lemma subspaceFinset_lineToSubspace {k n : ℕ} (l : LineW (Fin k) (Fin n)) :
    subspaceFinset (lineToSubspace l) = lineFinset l := by
  classical
  ext w
  constructor
  · intro hw
    rcases Finset.mem_image.1 hw with ⟨a, _ha, rfl⟩
    refine Finset.mem_image.2 ?_
    refine ⟨a ⟨0, by decide⟩, Finset.mem_univ _, ?_⟩
    funext i
    simpa using (lineToSubspace_apply (l := l) (a := a) (i := i)).symm
  · intro hw
    rcases Finset.mem_image.1 hw with ⟨b, _hb, rfl⟩
    let a : Fin 1 → Fin k := fun _ => b
    refine Finset.mem_image.2 ?_
    refine ⟨a, Finset.mem_univ _, ?_⟩
    funext i
    simpa [a] using (lineToSubspace_apply (l := l) (a := a) (i := i))

def containsSubspace_of_containsLine {k n : ℕ} {A : Finset (Word k n)} :
    containsLine A → containsSubspace (k := k) (n := n) (m := 1) A := by
  rintro ⟨l, hl⟩
  refine ⟨lineToSubspace l, ?_⟩
  intro w hw
  have : w ∈ lineFinset l := by
    simpa [subspaceFinset_lineToSubspace] using hw
  exact hl this

def hasSubspace_of_hasLine {k n : ℕ} {A : Finset (Word k n)} :
    hasLine A → hasSubspace (k := k) (n := n) (m := 1) A := by
  rintro ⟨h⟩
  exact ⟨containsSubspace_of_containsLine h⟩

end Polymath.DHJ

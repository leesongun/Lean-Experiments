import Mathlib.Data.Multiset.Basic
import Mathlib.Data.Fintype.Basic

namespace Polymath.DHJ

structure LineW (α ι : Type*) where
  idxFun : ι → Option α
  proper : {i // idxFun i = none}

instance instDecidableEqLineW {α ι : Type*} [DecidableEq α] [DecidableEq ι] [Fintype ι] :
    DecidableEq (LineW α ι) := by
  intro l₁ l₂
  cases l₁ with
  | mk idx₁ prop₁ =>
      cases l₂ with
      | mk idx₂ prop₂ =>
          by_cases hidx : idx₁ = idx₂
          · subst hidx
            by_cases hprop : prop₁ = prop₂
            · subst hprop
              exact isTrue rfl
            ·
              refine isFalse ?_
              intro h
              cases h
              exact hprop rfl
          ·
            refine isFalse ?_
            intro h
            cases h
            exact hidx rfl

def LineW.apply {α ι : Type*} (l : LineW α ι) (x : α) : ι → α :=
  fun i => (l.idxFun i).getD x

instance {α ι : Type*} : CoeFun (LineW α ι) (fun _ => α → ι → α) :=
  ⟨LineW.apply⟩

@[simp] lemma LineW.apply_def {α ι : Type*} (l : LineW α ι) (x : α) (i : ι) :
    l x i = (l.idxFun i).getD x := rfl

@[simp] lemma LineW.apply_none {α ι : Type*} (l : LineW α ι) (x : α) (i : ι)
    (h : l.idxFun i = none) : l x i = x := by
  simp [LineW.apply_def, h]

@[simp] lemma LineW.apply_some {α ι : Type*} (l : LineW α ι) (x : α) (i : ι) (a : α)
    (h : l.idxFun i = some a) : l x i = a := by
  simp [LineW.apply_def, h]

def LineW.IsMono {α ι κ : Type*} (l : LineW α ι) (C : (ι → α) → κ) : Prop :=
  ∃ c, ∀ x, C (l x) = c

def LineW.map {α α' ι : Type*} (f : α → α') (l : LineW α ι) : LineW α' ι :=
  { idxFun := fun i => (l.idxFun i).map f
    proper := ⟨l.proper.1, by simp [l.proper.2]⟩ }

@[simp] lemma LineW.map_apply {α α' ι : Type*} (f : α → α') (l : LineW α ι) (x : α) :
    l.map f (f x) = f ∘ l x := by
  funext i
  cases h : l.idxFun i with
  | none => simp [LineW.apply_def, LineW.map, h]
  | some a => simp [LineW.apply_def, LineW.map, h]

def LineW.vertical {α ι ι' : Type*} (v : ι → α) (l : LineW α ι') : LineW α (ι ⊕ ι') :=
  { idxFun := Sum.elim (some ∘ v) l.idxFun
    proper := ⟨Sum.inr l.proper.1, by simp [l.proper.2]⟩ }

def LineW.horizontal {α ι ι' : Type*} (l : LineW α ι) (v : ι' → α) : LineW α (ι ⊕ ι') :=
  { idxFun := Sum.elim l.idxFun (some ∘ v)
    proper := ⟨Sum.inl l.proper.1, by simp [l.proper.2]⟩ }

def LineW.prod {α ι ι' : Type*} (l : LineW α ι) (l' : LineW α ι') : LineW α (ι ⊕ ι') :=
  { idxFun := Sum.elim l.idxFun l'.idxFun
    proper := ⟨Sum.inl l.proper.1, by simp [l.proper.2]⟩ }

@[simp] lemma LineW.vertical_apply {α ι ι' : Type*} (v : ι → α) (l : LineW α ι') (x : α) :
    l.vertical v x = Sum.elim v (l x) := by
  funext i
  cases i <;> rfl

@[simp] lemma LineW.horizontal_apply {α ι ι' : Type*} (l : LineW α ι) (v : ι' → α) (x : α) :
    l.horizontal v x = Sum.elim (l x) v := by
  funext i
  cases i <;> rfl

@[simp] lemma LineW.prod_apply {α ι ι' : Type*} (l : LineW α ι) (l' : LineW α ι') (x : α) :
    l.prod l' x = Sum.elim (l x) (l' x) := by
  funext i
  cases i <;> rfl

def LineW.reindex {α ι ι' : Type*} (l : LineW α ι) (e : ι ≃ ι') : LineW α ι' :=
  { idxFun := fun i => l.idxFun (e.symm i)
    proper := by
      refine ⟨e l.proper.1, ?_⟩
      simp [l.proper.2] }

@[simp] lemma LineW.reindex_apply {α ι ι' : Type*} (l : LineW α ι) (e : ι ≃ ι') (x : α) :
    l.reindex e x = l x ∘ e.symm := by
  funext i
  rfl

structure SubspaceW (η α ι : Type*) where
  idxFun : ι → α ⊕ η
  proper : ∀ e, {i // idxFun i = Sum.inr e}

def SubspaceW.apply {η α ι : Type*} (l : SubspaceW η α ι) (x : η → α) (i : ι) : α :=
  (l.idxFun i).elim id x

instance {η α ι : Type*} : CoeFun (SubspaceW η α ι) (fun _ => (η → α) → ι → α) :=
  ⟨SubspaceW.apply⟩

@[simp] lemma SubspaceW.apply_def {η α ι : Type*} (l : SubspaceW η α ι) (x : η → α) (i : ι) :
    l x i = (l.idxFun i).elim id x := rfl

def SubspaceW.IsMono {η α ι κ : Type*} (l : SubspaceW η α ι) (C : (ι → α) → κ) : Prop :=
  ∃ c, ∀ x, C (l x) = c

def SubspaceW.reindex {η α ι η' α' ι' : Type*} (l : SubspaceW η α ι)
    (eη : η ≃ η') (eα : α ≃ α') (eι : ι ≃ ι') : SubspaceW η' α' ι' :=
  { idxFun := fun i => (l.idxFun (eι.symm i)).map eα eη
    proper := by
      intro e
      rcases l.proper (eη.symm e) with ⟨i, hi⟩
      refine ⟨eι i, ?_⟩
      simp [hi] }

@[simp] lemma SubspaceW.reindex_apply {η α ι η' α' ι' : Type*} (l : SubspaceW η α ι)
    (eη : η ≃ η') (eα : α ≃ α') (eι : ι ≃ ι') (x : η' → α') (i : ι') :
    l.reindex eη eα eι x i = eα (l (eα.symm ∘ x ∘ eη) (eι.symm i)) := by
  cases h : l.idxFun (eι.symm i) <;> simp [SubspaceW.reindex, SubspaceW.apply_def, h]

@[simp] lemma SubspaceW.reindex_isMono {η α ι η' α' ι' κ : Type*}
    {l : SubspaceW η α ι} {eη : η ≃ η'} {eα : α ≃ α'} {eι : ι ≃ ι'}
    {C : (ι' → α') → κ} :
    (l.reindex eη eα eι).IsMono C ↔
      l.IsMono fun x => C (eα ∘ x ∘ eι.symm) := by
  constructor
  · rintro ⟨c, hc⟩
    refine ⟨c, ?_⟩
    intro x
    have hfun :
        (l.reindex eη eα eι) (eα ∘ x ∘ eη.symm) = eα ∘ l x ∘ eι.symm := by
      funext i
      cases h : l.idxFun (eι.symm i) with
      | inl a =>
          simp [SubspaceW.reindex, SubspaceW.apply_def, h]
      | inr e =>
          simp [SubspaceW.reindex, SubspaceW.apply_def, h]
    simpa [hfun] using hc (eα ∘ x ∘ eη.symm)
  · rintro ⟨c, hc⟩
    refine ⟨c, ?_⟩
    intro x
    have hfun :
        (l.reindex eη eα eι) x =
          eα ∘ l (eα.symm ∘ x ∘ eη) ∘ eι.symm := by
      funext i
      cases h : l.idxFun (eι.symm i) with
      | inl a =>
          simp [SubspaceW.reindex, SubspaceW.apply_def, h]
      | inr e =>
          simp [SubspaceW.reindex, SubspaceW.apply_def, h]
    simpa [hfun] using hc (eα.symm ∘ x ∘ eη)

def LineW.toSubspace {η α ι : Type*} (l : LineW (η → α) ι) : SubspaceW η α (ι × η) :=
  { idxFun := fun ie =>
      (l.idxFun ie.1).elim (Sum.inr ie.2) (fun f => Sum.inl (f ie.2))
    proper := by
      intro e
      refine ⟨(l.proper.1, e), ?_⟩
      simp [l.proper.2] }

@[simp] lemma LineW.toSubspace_apply {η α ι : Type*} (l : LineW (η → α) ι) (a) (ie) :
    l.toSubspace a ie = l a ie.1 ie.2 := by
  cases h : l.idxFun ie.1 <;> simp [LineW.toSubspace, SubspaceW.apply_def, h]

@[simp] lemma LineW.toSubspace_isMono {η α ι κ : Type*} {l : LineW (η → α) ι}
    {C : (ι × η → α) → κ} :
    l.toSubspace.IsMono C ↔ l.IsMono fun x => C (fun (i, e) => x i e) := by
  constructor
  · rintro ⟨c, hc⟩
    refine ⟨c, ?_⟩
    intro x
    have hfun : l.toSubspace x = fun (i, e) => l x i e := by
      funext ie
      cases h : l.idxFun ie.1 <;>
        simp [LineW.toSubspace, SubspaceW.apply_def, LineW.apply_def, h]
    simpa [hfun] using hc x
  · rintro ⟨c, hc⟩
    refine ⟨c, ?_⟩
    intro x
    have hfun : l.toSubspace x = fun (i, e) => l x i e := by
      funext ie
      cases h : l.idxFun ie.1 <;>
        simp [LineW.toSubspace, SubspaceW.apply_def, LineW.apply_def, h]
    simpa [hfun] using hc x

structure AlmostMonoW {α ι κ : Type*} (C : (ι → Option α) → κ) where
  line : LineW (Option α) ι
  color : κ
  has_color : ∀ x : α, C (line (some x)) = color

structure ColorFocusedW {α ι κ : Type*} (C : (ι → Option α) → κ) where
  lines : Multiset (AlmostMonoW C)
  focus : ι → Option α
  is_focused : ∀ p ∈ lines, p.line none = focus
  distinct_colors : (lines.map AlmostMonoW.color).Nodup

instance {α ι κ : Type*} (C : (ι → Option α) → κ) : Inhabited (ColorFocusedW C) := by
  refine ⟨⟨0, fun _ => none, ?_, Multiset.nodup_zero⟩⟩
  intro p hp
  simp at hp

def findNoneFin {α : Type*} [DecidableEq α] {n : ℕ} (w : Fin n → Option α) :
    Option {i : Fin n // w i = none} :=
  match n with
  | 0 => none
  | n + 1 =>
      if h : w ⟨0, Nat.succ_pos n⟩ = none then
        some ⟨⟨0, Nat.succ_pos n⟩, h⟩
      else
        match findNoneFin (n := n) (fun i : Fin n => w i.succ) with
        | none => none
        | some h' =>
            some ⟨h'.1.succ, by simpa using h'.2⟩

lemma findNoneFin_some_iff {α : Type*} [DecidableEq α] {n : ℕ} (w : Fin n → Option α) :
    (∃ i, w i = none) ↔ ∃ h, findNoneFin (n := n) w = some h := by
  induction n with
  | zero =>
      constructor
      · rintro ⟨i, _⟩
        exact (Fin.elim0 i)
      · rintro ⟨h, _⟩
        exact (Fin.elim0 h.1)
  | succ n ih =>
      constructor
      · rintro ⟨i, hi⟩
        by_cases h0 : w ⟨0, Nat.succ_pos n⟩ = none
        · have h0' : w 0 = none := by simpa using h0
          refine ⟨⟨⟨0, Nat.succ_pos n⟩, h0⟩, ?_⟩
          simp [findNoneFin, h0']
        ·
          cases i using Fin.cases with
          | zero =>
              exact (h0 (by simpa using hi)).elim
          | succ j =>
              have : ∃ i, (fun t : Fin n => w t.succ) i = none := by
                refine ⟨j, ?_⟩
                simpa using hi
              rcases (ih _).1 this with ⟨h, hh⟩
              refine ⟨⟨h.1.succ, by simpa using h.2⟩, ?_⟩
              have h0' : w 0 ≠ none := by simpa using h0
              simp [findNoneFin, h0', hh]
      · rintro ⟨h, _hh⟩
        exact ⟨h.1, h.2⟩

lemma findNoneFin_isSome {α : Type*} [DecidableEq α] {n : ℕ}
    (w : Fin n → Option α) (h : ∃ i, w i = none) :
    (findNoneFin (n := n) w).isSome := by
  rcases (findNoneFin_some_iff (w := w)).1 h with ⟨h', hh⟩
  simp [hh]

def LineW.IsCanonical {α : Type*} [DecidableEq α] {n : ℕ} (l : LineW α (Fin n)) : Prop :=
  findNoneFin (n := n) l.idxFun = some l.proper

def LineW.fromIdxFun {α : Type*} [DecidableEq α] {n : ℕ}
    (w : Fin n → Option α) (h : ∃ i, w i = none) : LineW α (Fin n) := by
  exact { idxFun := w, proper := Option.get _ (findNoneFin_isSome (w := w) h) }

@[simp] lemma LineW.fromIdxFun_idxFun {α : Type*} [DecidableEq α] {n : ℕ}
    (w : Fin n → Option α) (h : ∃ i, w i = none) :
    (LineW.fromIdxFun w h).idxFun = w := rfl

@[simp] lemma LineW.isCanonical_fromIdxFun {α : Type*} [DecidableEq α] {n : ℕ}
    (w : Fin n → Option α) (h : ∃ i, w i = none) :
    LineW.IsCanonical (LineW.fromIdxFun w h) := by
  have hsome := findNoneFin_isSome (w := w) h
  have hget := (Option.coe_get (o := findNoneFin (n := n) w) hsome)
  dsimp [LineW.IsCanonical, LineW.fromIdxFun]
  exact hget.symm


lemma LineW.ext_of_canonical {α : Type*} [DecidableEq α] {n : ℕ}
    {l₁ l₂ : LineW α (Fin n)} (h₁ : LineW.IsCanonical l₁) (h₂ : LineW.IsCanonical l₂)
    (hidx : l₁.idxFun = l₂.idxFun) : l₁ = l₂ := by
  cases l₁ with
  | mk idx₁ prop₁ =>
      cases l₂ with
      | mk idx₂ prop₂ =>
          cases hidx
          have hproper : prop₁ = prop₂ := by
            apply Option.some.inj
            calc
              some prop₁ = findNoneFin (n := n) idx₁ := by symm; exact h₁
              _ = some prop₂ := h₂
          cases hproper
          rfl


end Polymath.DHJ

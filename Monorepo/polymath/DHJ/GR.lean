import Monorepo.polymath.DHJ.Definitions
import Monorepo.polymath.DHJ.HJConstructive
import Mathlib.Data.Bool.Basic

namespace Polymath.DHJ

instance {α : Type*} (L : Set α) [DecidablePred L] (x : α) : Decidable (x ∈ L) := by
  change Decidable (L x)
  infer_instance

def linesInSubspace {k n m : ℕ}
    (V : SubspaceW (Fin m) (Fin k) (Fin n)) :
    Set (LineW (Fin k) (Fin n)) :=
  {l | LineW.IsCanonical l ∧ lineFinset l ⊆ subspaceFinset V}

def linesMonochromatic {k n m : ℕ}
    (V : SubspaceW (Fin m) (Fin k) (Fin n))
    (L : Set (LineW (Fin k) (Fin n))) : Prop :=
  (∀ l, l ∈ linesInSubspace V → l ∈ L) ∨ (∀ l, l ∈ linesInSubspace V → l ∉ L)

lemma line_idxFun_eq_of_apply_eq {α ι : Type*} [Nontrivial α]
    {l : LineW α ι} {i j : ι} (h : ∀ a, l a i = l a j) :
    l.idxFun i = l.idxFun j := by
  classical
  cases hi : l.idxFun i with
  | none =>
      cases hj : l.idxFun j with
      | none => rfl
      | some b =>
          obtain ⟨y, hy⟩ := exists_ne b
          have hy' := h y
          simp [hi, hj] at hy'
          exact (hy (by simpa [eq_comm] using hy')).elim
  | some a =>
      cases hj : l.idxFun j with
      | none =>
          obtain ⟨y, hy⟩ := exists_ne a
          have hy' := h y
          simp [hi, hj] at hy'
          exact (hy (by simpa [eq_comm] using hy')).elim
      | some b =>
          have hab : a = b := by
            have h' := h a
            simpa [hi, hj] using h'
          simp [hab]

lemma line_idxFun_eq_some_of_apply_const {α ι : Type*} [Nontrivial α]
    {l : LineW α ι} {i : ι} {a : α} (h : ∀ x, l x i = a) :
    l.idxFun i = some a := by
  classical
  cases hi : l.idxFun i with
  | none =>
      obtain ⟨y, hy⟩ := exists_ne a
      have hy' := h y
      simp [hi] at hy'
      exact (hy hy').elim
  | some b =>
      have hab : b = a := by
        have h' := h a
        simpa [hi] using h'
      simp [hab]

def lineInSubspace {k n m : ℕ}
    (V : SubspaceW (Fin m) (Fin k) (Fin n))
    (l : LineW (Fin k) (Fin m)) :
    LineW (Fin k) (Fin n) := by
  let w : Fin n → Option (Fin k) :=
    fun i => match V.idxFun i with
      | Sum.inl a => some a
      | Sum.inr e => l.idxFun e
  have hw : ∃ i, w i = none := by
    refine ⟨(V.proper l.proper.1).1, ?_⟩
    have hi : V.idxFun (V.proper l.proper.1).1 = Sum.inr l.proper.1 :=
      (V.proper l.proper.1).2
    simp [w, hi, l.proper.2]
  exact LineW.fromIdxFun w hw

@[simp] lemma lineInSubspace_apply {k n m : ℕ}
    (V : SubspaceW (Fin m) (Fin k) (Fin n))
    (l : LineW (Fin k) (Fin m)) (a : Fin k) :
    lineInSubspace V l a = V (l a) := by
  funext i
  cases hV : V.idxFun i with
  | inl a' =>
      simp [lineInSubspace, LineW.fromIdxFun_idxFun, SubspaceW.apply_def, LineW.apply_def, hV]
  | inr e =>
      simp [lineInSubspace, LineW.fromIdxFun_idxFun, SubspaceW.apply_def, LineW.apply_def, hV]

lemma lineInSubspace_subset {k n m : ℕ}
    (V : SubspaceW (Fin m) (Fin k) (Fin n))
    (l : LineW (Fin k) (Fin m)) :
    lineFinset (lineInSubspace V l) ⊆ subspaceFinset V := by
  intro w hw
  rcases Finset.mem_image.1 hw with ⟨a, _ha, rfl⟩
  refine Finset.mem_image.2 ?_
  refine ⟨l a, Finset.mem_univ _, ?_⟩
  simp [lineInSubspace_apply]

lemma lineInSubspace_mem_linesInSubspace {k n m : ℕ}
    (V : SubspaceW (Fin m) (Fin k) (Fin n))
    (l : LineW (Fin k) (Fin m)) :
    lineInSubspace V l ∈ linesInSubspace V := by
  refine ⟨?_, lineInSubspace_subset V l⟩
  simp [lineInSubspace, LineW.isCanonical_fromIdxFun]

def lineSubspace {k n m : ℕ}
    (V : SubspaceW (Fin m) (Fin k) (Fin n)) :
    SubspaceW (Fin m) (Option (Fin k)) (Fin n) where
  idxFun i := match V.idxFun i with
    | Sum.inl a => Sum.inl (some a)
    | Sum.inr e => Sum.inr e
  proper := by
    intro e
    rcases V.proper e with ⟨i, hi⟩
    refine ⟨i, ?_⟩
    simp [hi]

def subspaceComp {α η η' ι : Type*}
    (S : SubspaceW η α ι)
    (T : SubspaceW η' α η) :
    SubspaceW η' α ι where
  idxFun i := match S.idxFun i with
    | Sum.inl a => Sum.inl a
    | Sum.inr e => T.idxFun e
  proper := by
    intro e'
    rcases T.proper e' with ⟨j, hj⟩
    rcases S.proper j with ⟨i, hi⟩
    refine ⟨i, ?_⟩
    simp [hi, hj]

@[simp] lemma subspaceComp_apply {α η η' ι : Type*}
    (S : SubspaceW η α ι)
    (T : SubspaceW η' α η)
    (x : η' → α) (i : ι) :
    subspaceComp S T x i = S (T x) i := by
  cases hS : S.idxFun i with
  | inl a =>
      simp [subspaceComp, SubspaceW.apply_def, hS]
  | inr e =>
      simp [subspaceComp, SubspaceW.apply_def, hS]

lemma subspaceComp_isMono {α η η' ι κ : Type*}
    {S : SubspaceW η α ι}
    {T : SubspaceW η' α η}
    {C : (ι → α) → κ} (hmono : S.IsMono C) :
    (subspaceComp S T).IsMono C := by
  rcases hmono with ⟨c, hc⟩
  refine ⟨c, ?_⟩
  intro x
  have hx : (subspaceComp S T) x = S (T x) := by
    funext i
    simpa using (subspaceComp_apply (S := S) (T := T) (x := x) (i := i))
  simpa [hx] using hc (T x)

@[simp] lemma lineSubspace_apply {k n m : ℕ}
    (V : SubspaceW (Fin m) (Fin k) (Fin n))
    (x : Fin m → Option (Fin k)) (i : Fin n) :
    lineSubspace V x i = (match V.idxFun i with
      | Sum.inl a => some a
      | Sum.inr e => x e) := by
  cases hV : V.idxFun i with
  | inl a =>
      simp [lineSubspace, SubspaceW.apply_def, hV]
  | inr e =>
      simp [lineSubspace, SubspaceW.apply_def, hV]

lemma lineSubspace_idxFun {k n m : ℕ}
    (V : SubspaceW (Fin m) (Fin k) (Fin n))
    (l : LineW (Fin k) (Fin m)) :
    lineSubspace V l.idxFun = (lineInSubspace V l).idxFun := by
  funext i
  cases hV : V.idxFun i with
  | inl a =>
      simp [lineSubspace, lineInSubspace, LineW.fromIdxFun_idxFun, SubspaceW.apply_def, hV]
  | inr e =>
      simp [lineSubspace, lineInSubspace, LineW.fromIdxFun_idxFun, SubspaceW.apply_def, hV]

def subspaceOfOption {k n m : ℕ} (hk : 0 < k)
    (S : SubspaceW (Fin m) (Option (Fin k)) (Fin n)) :
    SubspaceW (Fin m) (Fin k) (Fin n) where
  idxFun i := match S.idxFun i with
    | Sum.inl a => Sum.inl (a.getD ⟨0, hk⟩)
    | Sum.inr e => Sum.inr e
  proper := by
    intro e
    rcases S.proper e with ⟨i, hi⟩
    refine ⟨i, ?_⟩
    simp [hi]

def exists_no_none_of_noConstNone {k n m : ℕ} (hk : 0 < k)
    (S : SubspaceW (Fin m) (Option (Fin k)) (Fin n))
    (hS : ∀ i, S.idxFun i ≠ Sum.inl none) :
    {x : Fin m → Option (Fin k) // ∀ i, S x i ≠ none} := by
  refine ⟨fun _ => some ⟨0, hk⟩, ?_⟩
  intro i
  cases hS' : S.idxFun i with
  | inl a =>
      cases a with
      | some a =>
          simp [SubspaceW.apply_def, hS']
      | none =>
          exact (hS i hS').elim
  | inr e =>
      simp [SubspaceW.apply_def, hS']

lemma noConstNone_of_exists_no_none {k n m : ℕ}
    (S : SubspaceW (Fin m) (Option (Fin k)) (Fin n))
    (x : Fin m → Option (Fin k)) (hx : ∀ i, S x i ≠ none) :
    ∀ i, S.idxFun i ≠ Sum.inl none := by
  intro i hS
  have : S x i = none := by
    simp [SubspaceW.apply_def, hS]
  exact (hx i) this

lemma lineSubspace_subspaceOfOption_apply {k n m : ℕ} (hk : 0 < k)
    (S : SubspaceW (Fin m) (Option (Fin k)) (Fin n))
    (h : ∀ i, S.idxFun i ≠ Sum.inl none) (x : Fin m → Option (Fin k)) (i : Fin n) :
    lineSubspace (subspaceOfOption hk S) x i = S x i := by
  cases hS : S.idxFun i with
  | inl a =>
      cases a with
      | some a =>
          have hV : (subspaceOfOption hk S).idxFun i = Sum.inl a := by
            simp [subspaceOfOption, hS]
          simp [lineSubspace, SubspaceW.apply_def, hV, hS]
      | none =>
          exact (h i hS).elim
  | inr e =>
      have hV : (subspaceOfOption hk S).idxFun i = Sum.inr e := by
        simp [subspaceOfOption, hS]
      simp [lineSubspace, SubspaceW.apply_def, hV, hS]
def lineColor {k n : ℕ}
    (L : Set (LineW (Fin k) (Fin n)))
    (decL : DecidablePred L)
    (w : Fin n → Option (Fin k)) : Bool :=
  match findNoneFin (n := n) w with
  | none => false
  | some h => @decide (L (⟨w, h⟩ : LineW (Fin k) (Fin n))) (decL _)

def lineOfLineSubspace {k n m : ℕ}
    (S : SubspaceW (Fin m) (Option (Fin k)) (Fin n))
    (l : LineW (Fin k) (Fin m)) :
    LineW (Fin k) (Fin n) := by
  let w : Fin n → Option (Fin k) := S l.idxFun
  have hw : ∃ i, w i = none := by
    refine ⟨(S.proper l.proper.1).1, ?_⟩
    have hi : S.idxFun (S.proper l.proper.1).1 = Sum.inr l.proper.1 :=
      (S.proper l.proper.1).2
    simp [w, SubspaceW.apply_def, hi, l.proper.2]
  exact LineW.fromIdxFun w hw

lemma lineOfLineSubspace_lineSubspace {k n m : ℕ}
    (V : SubspaceW (Fin m) (Fin k) (Fin n))
    (l : LineW (Fin k) (Fin m)) :
    lineOfLineSubspace (lineSubspace V) l = lineInSubspace V l := by
  apply LineW.ext_of_canonical
  · simp [lineOfLineSubspace, LineW.isCanonical_fromIdxFun]
  · simp [lineInSubspace, LineW.isCanonical_fromIdxFun]
  · funext i
    cases hV : V.idxFun i with
    | inl a =>
        simp [lineOfLineSubspace, lineInSubspace, lineSubspace, hV,
          LineW.fromIdxFun_idxFun, SubspaceW.apply_def]
    | inr e =>
        simp [lineOfLineSubspace, lineInSubspace, lineSubspace, hV,
          LineW.fromIdxFun_idxFun, SubspaceW.apply_def]

lemma lineColor_lineOfLineSubspace {k n m : ℕ}
    (L : Set (LineW (Fin k) (Fin n)))
    (decL : DecidablePred L)
    (S : SubspaceW (Fin m) (Option (Fin k)) (Fin n))
    (l : LineW (Fin k) (Fin m)) :
    lineColor L decL (S l.idxFun) =
      @decide (L (lineOfLineSubspace S l)) (decL _) := by
  classical
  let w : Fin n → Option (Fin k) := S l.idxFun
  have hw : ∃ i, w i = none := by
    refine ⟨(S.proper l.proper.1).1, ?_⟩
    have hi : S.idxFun (S.proper l.proper.1).1 = Sum.inr l.proper.1 :=
      (S.proper l.proper.1).2
    simp [w, SubspaceW.apply_def, hi, l.proper.2]
  cases hfind : findNoneFin (n := n) w with
  | none =>
      have hsome : ∃ h, findNoneFin (n := n) w = some h :=
        (findNoneFin_some_iff (w := w)).1 hw
      rcases hsome with ⟨h, hh⟩
      have hcontr : (none : Option { i // w i = none }) = some h := by
        exact (hfind ▸ hh)
      cases hcontr
  | some h =>
      simp [lineColor, lineOfLineSubspace, LineW.fromIdxFun, w, hfind]

lemma linesMonochromatic_of_isMono {k n m : ℕ}
    (L : Set (LineW (Fin k) (Fin n)))
    (decL : DecidablePred L)
    (S : SubspaceW (Fin m) (Option (Fin k)) (Fin n))
    (hmono : S.IsMono (lineColor L decL)) :
    (∀ l, lineOfLineSubspace S l ∈ L) ∨ (∀ l, lineOfLineSubspace S l ∉ L) := by
  have _ : DecidablePred L := decL
  rcases hmono with ⟨c, hc⟩
  cases c with
  | false =>
      right
      intro l
      have hcolor : lineColor L decL (S l.idxFun) = false := by simpa using hc l.idxFun
      have hdec : decide (L (lineOfLineSubspace S l)) = false := by
        simpa [lineColor_lineOfLineSubspace] using hcolor
      exact (Bool.decide_false_iff _).1 hdec
  | true =>
      left
      intro l
      have hcolor : lineColor L decL (S l.idxFun) = true := by simpa using hc l.idxFun
      have hdec : decide (L (lineOfLineSubspace S l)) = true := by
        simpa [lineColor_lineOfLineSubspace] using hcolor
      exact (Bool.decide_iff _).1 hdec

noncomputable def linesMonochromatic_option {k m : ℕ} :
    Σ n, ∀ L : Set (LineW (Fin k) (Fin n)),
      DecidablePred L →
        {S : SubspaceW (Fin m) (Option (Fin k)) (Fin n) //
          (∀ l, lineOfLineSubspace S l ∈ L) ∨ (∀ l, lineOfLineSubspace S l ∉ L)} := by
  obtain ⟨n, hS⟩ := Polymath.DHJ.hales_jewett_subspace (k := k) (m := m) (κ := Bool)
  refine ⟨n, ?_⟩
  intro L decL
  obtain ⟨S, hmono⟩ := hS (lineColor L decL)
  refine ⟨S, ?_⟩
  exact linesMonochromatic_of_isMono (L := L) decL (S := S) hmono

lemma line_idxFun_eq_of_same_variable {k n m : ℕ} [Nontrivial (Fin k)]
    (V : SubspaceW (Fin m) (Fin k) (Fin n))
    {L : LineW (Fin k) (Fin n)}
    (hL : lineFinset L ⊆ subspaceFinset V)
    {i j : Fin n} {e : Fin m}
    (hi : V.idxFun i = Sum.inr e) (hj : V.idxFun j = Sum.inr e) :
    L.idxFun i = L.idxFun j := by
  classical
  have happly : ∀ a, L a i = L a j := by
    intro a
    have hmem : L a ∈ subspaceFinset V := by
      apply hL
      refine Finset.mem_image.2 ?_
      refine ⟨a, Finset.mem_univ _, rfl⟩
    rcases Finset.mem_image.1 hmem with ⟨b, _hb, hb⟩
    have hb' : L a = V b := hb.symm
    calc
      L a i = V b i := by rw [hb']
      _ = b e := by simp [SubspaceW.apply_def, hi]
      _ = V b j := by simp [SubspaceW.apply_def, hj]
      _ = L a j := by rw [hb']
  exact line_idxFun_eq_of_apply_eq happly

noncomputable def lineOfSubspace {k n m : ℕ} (hk : 2 ≤ k)
    (V : SubspaceW (Fin m) (Fin k) (Fin n))
    {L : LineW (Fin k) (Fin n)}
    (hL : lineFinset L ⊆ subspaceFinset V) :
    LineW (Fin k) (Fin m) := by
  classical
  let w : Fin m → Option (Fin k) := fun e => L.idxFun (V.proper e).1
  have hw : ∃ e, w e = none := by
    haveI : Nontrivial (Fin k) := (Fin.nontrivial_iff_two_le).2 hk
    obtain ⟨i0, hi0⟩ := L.proper
    cases hV : V.idxFun i0 with
    | inl a =>
        have hconst : ∀ x, L x i0 = a := by
          intro x
          have hmem : L x ∈ subspaceFinset V := by
            apply hL
            refine Finset.mem_image.2 ?_
            refine ⟨x, Finset.mem_univ _, rfl⟩
          rcases Finset.mem_image.1 hmem with ⟨b, _hb, hb⟩
          have hb' : L x = V b := hb.symm
          calc
            L x i0 = V b i0 := by rw [hb']
            _ = a := by simp [SubspaceW.apply_def, hV]
        have hforall : ∀ x, x = a := by
          intro x
          have hx := hconst x
          simpa [LineW.apply_def, hi0] using hx
        obtain ⟨y, hy⟩ := exists_ne a
        exact (hy (hforall y)).elim
    | inr e =>
        refine ⟨e, ?_⟩
        have hchoose : V.idxFun (V.proper e).1 = Sum.inr e := (V.proper e).2
        have hidx : L.idxFun (V.proper e).1 = L.idxFun i0 :=
          line_idxFun_eq_of_same_variable V hL hchoose hV
        simp [w, hidx, hi0]
  exact LineW.fromIdxFun w hw

lemma lineInSubspace_lineOfSubspace {k n m : ℕ} (hk : 2 ≤ k)
    (V : SubspaceW (Fin m) (Fin k) (Fin n))
    {L : LineW (Fin k) (Fin n)}
    (hL : lineFinset L ⊆ subspaceFinset V)
    (hcanon : LineW.IsCanonical L) :
    lineInSubspace V (lineOfSubspace hk V hL) = L := by
  classical
  haveI : Nontrivial (Fin k) := (Fin.nontrivial_iff_two_le).2 hk
  apply LineW.ext_of_canonical
  · simp [lineInSubspace, LineW.isCanonical_fromIdxFun]
  · exact hcanon
  · funext i
    cases hV : V.idxFun i with
    | inl a =>
        have hconst : ∀ x, L x i = a := by
          intro x
          have hmem : L x ∈ subspaceFinset V := by
            apply hL
            refine Finset.mem_image.2 ?_
            refine ⟨x, Finset.mem_univ _, rfl⟩
          rcases Finset.mem_image.1 hmem with ⟨b, _hb, hb⟩
          have hb' : L x = V b := hb.symm
          calc
            L x i = V b i := by rw [hb']
            _ = a := by simp [SubspaceW.apply_def, hV]
        have hidx : L.idxFun i = some a := line_idxFun_eq_some_of_apply_const hconst
        simp [lineInSubspace, hV, hidx, LineW.fromIdxFun_idxFun]
    | inr e =>
        have hchoose : V.idxFun (V.proper e).1 = Sum.inr e := (V.proper e).2
        have hidx :
            L.idxFun i = L.idxFun (V.proper e).1 := by
          exact line_idxFun_eq_of_same_variable V hL hV hchoose
        simp [lineInSubspace, hV, lineOfSubspace, hidx, LineW.fromIdxFun_idxFun]

lemma lineOfSubspace_lineInSubspace {k n m : ℕ} (hk : 2 ≤ k)
    (V : SubspaceW (Fin m) (Fin k) (Fin n))
    (l : LineW (Fin k) (Fin m)) (hcanon : LineW.IsCanonical l) :
    lineOfSubspace hk V (lineInSubspace_subset V l) = l := by
  classical
  apply LineW.ext_of_canonical
  · simp [lineOfSubspace, LineW.isCanonical_fromIdxFun]
  · exact hcanon
  · funext e
    have hchoose : V.idxFun (V.proper e).1 = Sum.inr e := (V.proper e).2
    simp [lineOfSubspace, lineInSubspace, hchoose, LineW.fromIdxFun_idxFun]

lemma linesInSubspace_eq_image {k n m : ℕ} (hk : 2 ≤ k)
    (V : SubspaceW (Fin m) (Fin k) (Fin n)) :
    linesInSubspace V = Set.image (lineInSubspace V) Set.univ := by
  ext L
  constructor
  · intro hL
    rcases hL with ⟨hcanon, hsub⟩
    refine ⟨lineOfSubspace hk V hsub, Set.mem_univ _, ?_⟩
    exact lineInSubspace_lineOfSubspace hk V hsub hcanon
  · rintro ⟨l, _hl, rfl⟩
    exact lineInSubspace_mem_linesInSubspace V l

lemma linesMonochromatic_of_isMono_lineSubspace {k n m : ℕ} (hk : 2 ≤ k)
    (L : Set (LineW (Fin k) (Fin n)))
    (decL : DecidablePred L)
    (V : SubspaceW (Fin m) (Fin k) (Fin n))
    (hmono : (lineSubspace V).IsMono (lineColor L decL)) :
    linesMonochromatic V L := by
  rcases linesMonochromatic_of_isMono (L := L) decL (S := lineSubspace V) hmono with h | h
  · left
    intro l hl
    have hl' : l ∈ Set.image (lineInSubspace V) Set.univ := by
      simpa [linesInSubspace_eq_image hk V] using hl
    rcases hl' with ⟨l', _hl', rfl⟩
    simpa [lineOfLineSubspace_lineSubspace] using h l'
  · right
    intro l hl
    have hl' : l ∈ Set.image (lineInSubspace V) Set.univ := by
      simpa [linesInSubspace_eq_image hk V] using hl
    rcases hl' with ⟨l', _hl', rfl⟩
    simpa [lineOfLineSubspace_lineSubspace] using h l'

lemma linesMonochromatic_of_isMono_option {k n m : ℕ} (hk : 2 ≤ k)
    (L : Set (LineW (Fin k) (Fin n)))
    (decL : DecidablePred L)
    (S : SubspaceW (Fin m) (Option (Fin k)) (Fin n))
    (hS : ∀ i, S.idxFun i ≠ Sum.inl none)
    (hmono : S.IsMono (lineColor L decL)) :
    linesMonochromatic (subspaceOfOption (Nat.lt_of_lt_of_le (by decide : 0 < 2) hk) S) L := by
  have hk' : 0 < k := Nat.lt_of_lt_of_le (by decide : 0 < 2) hk
  have hmono' :
      (lineSubspace (subspaceOfOption hk' S)).IsMono (lineColor L decL) := by
    rcases hmono with ⟨c, hc⟩
    refine ⟨c, ?_⟩
    intro x
    have hx : lineSubspace (subspaceOfOption hk' S) x = S x := by
      funext i
      simpa using lineSubspace_subspaceOfOption_apply hk' S hS x i
    simpa [hx] using hc x
  exact linesMonochromatic_of_isMono_lineSubspace hk (L := L) decL
    (V := subspaceOfOption hk' S) hmono'

lemma linesMonochromatic_of_isMono_option_of_exists_no_none {k n m : ℕ} (hk : 2 ≤ k)
    (L : Set (LineW (Fin k) (Fin n)))
    (decL : DecidablePred L)
    (S : SubspaceW (Fin m) (Option (Fin k)) (Fin n))
    (x : Fin m → Option (Fin k)) (hx : ∀ i, S x i ≠ none)
    (hmono : S.IsMono (lineColor L decL)) :
    linesMonochromatic (subspaceOfOption (Nat.lt_of_lt_of_le (by decide : 0 < 2) hk) S) L := by
  have hS : ∀ i, S.idxFun i ≠ Sum.inl none := noConstNone_of_exists_no_none S x hx
  exact linesMonochromatic_of_isMono_option hk (L := L) decL (S := S) hS hmono

end Polymath.DHJ

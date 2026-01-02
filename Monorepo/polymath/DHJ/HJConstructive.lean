import Monorepo.polymath.DHJ.Definitions
import Monorepo.polymath.DHJ.LineW
import Mathlib.Data.Fintype.Prod
import Mathlib.Logic.Equiv.Fin.Basic

namespace Polymath.DHJ

universe u v w

structure LineMono {α : Type u} {ι : Type v} {κ : Type w} (C : (ι → α) → κ) :
    Type (max u v w) where
  line : LineW α ι
  color : κ
  mono : ∀ x, C (line x) = color

lemma LineMono.isMono {α ι κ : Type*} {C : (ι → α) → κ} (m : LineMono C) :
    m.line.IsMono C :=
  ⟨m.color, m.mono⟩

def LineMono.map {α α' ι κ : Type*} (e : α ≃ α') {C : (ι → α') → κ}
    (m : LineMono (fun v => C (e ∘ v))) : LineMono C :=
  { line := m.line.map e
    color := m.color
    mono := by
      intro x'
      obtain ⟨x, rfl⟩ := e.surjective x'
      simpa [LineW.map_apply] using m.mono x }

/-- Reindex a line along an equivalence of coordinates. -/
def lineReindex {α ι ι' : Type*} (l : LineW α ι) (e : ι ≃ ι') : LineW α ι' :=
  l.reindex e

@[simp] lemma lineReindex_apply {α ι ι' : Type*} (l : LineW α ι) (e : ι ≃ ι') (x : α) :
    lineReindex l e x = l x ∘ e.symm := by
  funext i
  rfl

def LineMono.reindex {α ι ι' κ : Type*} (e : ι ≃ ι') {C : (ι' → α) → κ}
    (m : LineMono (fun v => C (v ∘ e.symm))) : LineMono C :=
  { line := lineReindex m.line e
    color := m.color
    mono := by
      intro x
      simpa [lineReindex_apply] using m.mono x }

def AlmostMonoW.reindex {α ι ι' κ : Type*} (e : ι ≃ ι') {C : (ι' → Option α) → κ}
    (m : AlmostMonoW (fun v => C (v ∘ e.symm))) : AlmostMonoW C :=
  { line := lineReindex m.line e
    color := m.color
    has_color := by
      intro x
      simpa [lineReindex_apply] using m.has_color x }

@[simp] lemma AlmostMonoW.reindex_color {α ι ι' κ : Type*} (e : ι ≃ ι')
    {C : (ι' → Option α) → κ} (m : AlmostMonoW (fun v => C (v ∘ e.symm))) :
    (AlmostMonoW.reindex e m).color = m.color := rfl

def ColorFocusedW.reindex {α ι ι' κ : Type*} (e : ι ≃ ι') {C : (ι' → Option α) → κ}
    (s : ColorFocusedW (fun v => C (v ∘ e.symm))) : ColorFocusedW C :=
  { lines := s.lines.map (AlmostMonoW.reindex e)
    focus := s.focus ∘ e.symm
    is_focused := by
      intro p hp
      simp_rw [Multiset.mem_map] at hp
      rcases hp with ⟨q, hq, rfl⟩
      change lineReindex q.line e none = s.focus ∘ e.symm
      simp [lineReindex_apply, s.is_focused q hq]
    distinct_colors := by
      simpa [Multiset.map_map] using s.distinct_colors }

lemma lineReindex_isMono {α ι ι' κ : Type*} {l : LineW α ι} (e : ι ≃ ι')
    {C : (ι' → α) → κ} (hl : l.IsMono fun v => C (v ∘ e.symm)) :
    (lineReindex l e).IsMono C := by
  rcases hl with ⟨c, hc⟩
  refine ⟨c, ?_⟩
  intro x
  simpa [lineReindex_apply] using hc x

lemma lineMap_isMono_equiv {α α' ι κ : Type*} (e : α ≃ α')
    {C : (ι → α') → κ} {l : LineW α ι} (hl : l.IsMono fun v => C (e ∘ v)) :
    (l.map e).IsMono C := by
  rcases hl with ⟨c, hc⟩
  refine ⟨c, ?_⟩
  intro x
  obtain ⟨x', rfl⟩ := e.surjective x
  simpa using hc x'

def optionFinEquiv (k : ℕ) : Option (Fin k) ≃ Fin (Nat.succ k) :=
  (finSuccEquiv k).symm

def optionFinFunEquiv (k m : ℕ) :
    (Fin m → Option (Fin k)) ≃ (Fin m → Fin (Nat.succ k)) :=
  { toFun := fun f i => optionFinEquiv k (f i)
    invFun := fun f i => (optionFinEquiv k).symm (f i)
    left_inv := by
      intro f
      funext i
      simp [optionFinEquiv]
    right_inv := by
      intro f
      funext i
      simp [optionFinEquiv] }

def finFunEquivFinPow (k m : ℕ) :
    (Fin m → Fin (Nat.succ k)) ≃ Fin ((Nat.succ k) ^ m) := by
  induction m with
  | zero =>
      refine
        { toFun := fun _ => 0
          invFun := fun _ => Fin.elim0
          left_inv := by
            intro f
            funext i
            exact (Fin.elim0 i)
          right_inv := by
            intro i
            cases i with
            | mk val hval =>
                cases val with
                | zero => rfl
                | succ val =>
                    exact (Nat.not_lt_zero _ (Nat.lt_of_succ_lt_succ hval)).elim }
  | succ m ih =>
      refine (Fin.consEquiv (fun _ : Fin (Nat.succ m) => Fin (Nat.succ k))).symm.trans ?_
      refine (Equiv.prodCongr (Equiv.refl _) ih).trans ?_
      refine (Equiv.prodComm (Fin (Nat.succ k)) (Fin ((Nat.succ k) ^ m))).trans ?_
      refine (finProdFinEquiv :
        Fin ((Nat.succ k) ^ m) × Fin (Nat.succ k) ≃
          Fin ((Nat.succ k) ^ m * Nat.succ k)).trans ?_
      have hpow :
          (Nat.succ k) ^ m * Nat.succ k = (Nat.succ k) ^ Nat.succ m := by
        simpa using (Nat.pow_succ (Nat.succ k) m).symm
      exact Equiv.cast (congrArg Fin hpow)

def optionFinPowEquiv (k m : ℕ) :
    Fin ((Nat.succ k) ^ m) ≃ (Fin m → Option (Fin k)) :=
  (finFunEquivFinPow k m).symm.trans (optionFinFunEquiv k m).symm

def hj_option {k : ℕ}
    (ih : ∀ {κ : Type u} [Fintype κ] [DecidableEq κ] [Inhabited κ],
      Σ n, ∀ C : Word k n → κ, LineMono C) :
    ∀ {κ : Type u} [Fintype κ] [DecidableEq κ] [Inhabited κ],
      Σ n, ∀ C : (Fin n → Option (Fin k)) → κ, LineMono C := by
  intro κ _instκ _decκ _inhκ
  cases k with
  | zero =>
      refine ⟨1, ?_⟩
      intro C
      let l : LineW (Option (Fin 0)) (Fin 1) :=
        { idxFun := fun _ => none
          proper := ⟨⟨0, by decide⟩, rfl⟩ }
      refine { line := l, color := C (l none), mono := ?_ }
      intro x
      cases x with
      | none => rfl
      | some x => exact (Nat.not_lt_zero _ x.isLt).elim
  | succ k =>
      have a0 : Fin (Nat.succ k) := ⟨0, Nat.succ_pos k⟩
      have key :
          ∀ r : ℕ,
            Σ n : ℕ,
              (∀ C : (Fin n → Option (Fin (Nat.succ k))) → κ,
                {s : ColorFocusedW C // Multiset.card s.lines = r} ⊕
                  LineMono C) := by
        intro r
        induction r with
        | zero =>
            refine ⟨0, ?_⟩
            intro C
            exact Sum.inl ⟨default, by rfl⟩
        | succ r ihr =>
            rcases ihr with ⟨n, hι⟩
            haveI : Fintype (Option (Fin (Nat.succ k))) := inferInstance
            haveI : Fintype (Fin n → Option (Fin (Nat.succ k))) := inferInstance
            haveI : Fintype ((Fin n → Option (Fin (Nat.succ k))) → κ) := inferInstance
            have ih' := ih (κ := (Fin n → Option (Fin (Nat.succ k))) → κ)
            rcases ih' with ⟨n', hι'⟩
            refine ⟨n + n', ?_⟩
            intro C
            let eSum : Fin n ⊕ Fin n' ≃ Fin (n + n') := finSumFinEquiv
            let Csum :
                (Fin n ⊕ Fin n' → Option (Fin (Nat.succ k))) → κ :=
              fun v => C (v ∘ eSum.symm)
            let C' :
                (Fin n' → Fin (Nat.succ k)) → (Fin n → Option (Fin (Nat.succ k))) → κ :=
              fun v' v => Csum (Sum.elim v (some ∘ v'))
            have hl' := hι' C'
            let l' := hl'.line
            let Cfocus := hl'.color
            have hCfocus : ∀ x, C' (l' x) = Cfocus := hl'.mono
            have hCfocus_apply (x : Fin (Nat.succ k))
                (v : Fin n → Option (Fin (Nat.succ k))) :
                Cfocus v = Csum (Sum.elim v (some ∘ l' x)) := by
              have h' := congrArg (fun f => f v) (hCfocus x)
              simpa [C'] using h'.symm
            have mono_of_mono :
                LineMono Cfocus → LineMono Csum := by
              intro m
              refine
                { line := m.line.horizontal (some ∘ l' a0)
                  color := m.color
                  mono := ?_ }
              intro x
              have hCfocus' :
                  Cfocus (m.line x) = Csum (Sum.elim (m.line x) (some ∘ l' a0)) :=
                hCfocus_apply a0 (m.line x)
              have hc' := m.mono x
              have : Csum (Sum.elim (m.line x) (some ∘ l' a0)) = m.color := by
                simpa [hCfocus'] using hc'
              simpa [LineW.horizontal_apply] using this
            have hsum :
                {s : ColorFocusedW Csum // Multiset.card s.lines = Nat.succ r} ⊕
                  LineMono Csum := by
              have hιC := hι Cfocus
              cases hιC with
              | inr hmono =>
                  exact Sum.inr (mono_of_mono hmono)
              | inl hlines =>
                  rcases hlines with ⟨s, sr⟩
                  by_cases hcolor : Cfocus s.focus ∈ s.lines.map AlmostMonoW.color
                  ·
                    have huniq : ∃! p, p ∈ s.lines ∧ p.color = Cfocus s.focus := by
                      rcases (Multiset.mem_map.1 hcolor) with ⟨p, hp_mem, hp_color⟩
                      refine ⟨p, ⟨hp_mem, hp_color⟩, ?_⟩
                      intro q hq
                      have hq_mem : q ∈ s.lines := hq.1
                      have hq_color : q.color = Cfocus s.focus := hq.2
                      have hinj := Multiset.inj_on_of_nodup_map (s := s.lines)
                        (f := AlmostMonoW.color) s.distinct_colors
                      have hcolor_eq : p.color = q.color := by
                        simpa [hp_color] using hq_color.symm
                      exact (hinj _ hp_mem _ hq_mem hcolor_eq).symm
                    let p := Multiset.choose (p := fun q => q.color = Cfocus s.focus)
                      (l := s.lines) huniq
                    have hp_mem : p ∈ s.lines :=
                      (Multiset.choose_spec (p := fun q => q.color = Cfocus s.focus)
                        (l := s.lines) huniq).1
                    have hp_color : p.color = Cfocus s.focus :=
                      (Multiset.choose_spec (p := fun q => q.color = Cfocus s.focus)
                        (l := s.lines) huniq).2
                    refine Sum.inr (mono_of_mono
                      { line := p.line, color := p.color, mono := ?_ })
                    rintro (_ | _)
                    · rw [hp_color, s.is_focused p hp_mem]
                    · exact p.has_color _
                  ·
                    let mapLine : AlmostMonoW Cfocus → AlmostMonoW Csum := fun p =>
                      { line := p.line.prod (l'.map some)
                        color := p.color
                        has_color := by
                          intro x
                          have hfocus := hCfocus_apply x (p.line (some x))
                          have hcolor : Cfocus (p.line (some x)) = p.color := p.has_color x
                          have : Csum (Sum.elim (p.line (some x)) (l'.map some (some x))) =
                              p.color := by
                            have hmap : l'.map some (some x) = some ∘ l' x := by
                              simp [LineW.map_apply]
                            have :
                                Csum (Sum.elim (p.line (some x)) (some ∘ l' x)) = p.color := by
                              simpa [hfocus] using hcolor
                            simpa [hmap] using this
                          simpa [LineW.prod_apply] using this }
                    let vline : AlmostMonoW Csum :=
                      { line := (l'.map some).vertical s.focus
                        color := Cfocus s.focus
                        has_color := by
                          intro x
                          have hfocus := hCfocus_apply x s.focus
                          have hmap : l'.map some (some x) = some ∘ l' x := by
                            simp [LineW.map_apply]
                          have : Csum (Sum.elim s.focus (l'.map some (some x))) =
                              Cfocus s.focus := by
                            simpa [hmap] using hfocus.symm
                          simpa [LineW.vertical_apply] using this }
                    refine Sum.inl ?_
                    refine ⟨
                      { lines := (s.lines.map mapLine).cons vline
                        focus := Sum.elim s.focus (l'.map some none)
                        is_focused := ?_
                        distinct_colors := ?_ }, ?_⟩
                    · intro p hp
                      simp_rw [Multiset.mem_cons, Multiset.mem_map] at hp
                      rcases hp with rfl | ⟨q, hq, rfl⟩
                      · simp [vline, LineW.vertical_apply]
                      · simp [mapLine, LineW.prod_apply, s.is_focused q hq]
                    ·
                      have hcolor' :
                          Cfocus s.focus ∉ s.lines.map (fun p => (mapLine p).color) := by
                        simpa [mapLine] using hcolor
                      rw [Multiset.map_cons, Multiset.map_map, Multiset.nodup_cons]
                      exact ⟨by simpa [vline] using hcolor', s.distinct_colors⟩
                    ·
                      rw [Multiset.card_cons, Multiset.card_map, sr]
            cases hsum with
            | inl hlines =>
                rcases hlines with ⟨s, sr⟩
                refine Sum.inl ?_
                refine ⟨ColorFocusedW.reindex eSum s, ?_⟩
                simpa [ColorFocusedW.reindex, Multiset.card_map] using sr
            | inr hmono =>
                exact Sum.inr (LineMono.reindex eSum hmono)
      obtain ⟨n, hι⟩ := key (Fintype.card κ + 1)
      refine ⟨n, ?_⟩
      intro C
      have hιC := hι C
      cases hιC with
      | inl hlines =>
          rcases hlines with ⟨s, sr⟩
          have hcard : Fintype.card κ + 1 ≤ Fintype.card κ := by
            have hle : Multiset.card (s.lines.map AlmostMonoW.color) ≤ Fintype.card κ := by
              simpa [Finset.card_mk] using (Finset.card_le_univ ⟨_, s.distinct_colors⟩)
            have hcard' : Multiset.card (s.lines.map AlmostMonoW.color) = Fintype.card κ + 1 := by
              simp [sr, Multiset.card_map]
            exact (hcard' ▸ hle)
          exact (False.elim (Nat.not_succ_le_self _ hcard))
      | inr hmono =>
          exact hmono

/-- Constructive Hales--Jewett for `Fin k`. -/
def hales_jewett_fin :
    ∀ k : ℕ, ∀ {κ : Type u} [Fintype κ] [DecidableEq κ] [Inhabited κ],
      Σ n, ∀ C : Word k n → κ, LineMono C := by
  intro k
  induction k with
  | zero =>
      intro κ _instκ _decκ _inhκ
      refine ⟨1, ?_⟩
      intro C
      let l : LineW (Fin 0) (Fin 1) :=
        { idxFun := fun _ => none
          proper := ⟨⟨0, by decide⟩, rfl⟩ }
      refine { line := l, color := default, mono := ?_ }
      intro x
      exact (Fin.elim0 x)
  | succ k ih =>
      intro κ _instκ _decκ _inhκ
      have hopt := hj_option (k := k) (ih := ih) (κ := κ)
      rcases hopt with ⟨n, hline⟩
      refine ⟨n, ?_⟩
      intro C
      let e : Option (Fin k) ≃ Fin (Nat.succ k) := optionFinEquiv k
      let C' : (Fin n → Option (Fin k)) → κ := fun v => C (e ∘ v)
      have hl := hline C'
      exact LineMono.map e hl

/-- Multidimensional Hales--Jewett, derived from the constructive `hales_jewett_fin`. -/
def hales_jewett_subspace {k m : ℕ} {κ : Type u}
    [Fintype κ] [DecidableEq κ] [Inhabited κ] :
    Σ n, ∀ C : (Fin n → Option (Fin k)) → κ,
      {S : SubspaceW (Fin m) (Option (Fin k)) (Fin n) // S.IsMono C} := by
  -- Apply HJ to the finite alphabet of length-`m` words.
  have h := hales_jewett_fin (k := (Nat.succ k) ^ m) (κ := κ)
  rcases h with ⟨n, hline⟩
  -- Use the line to build a subspace on `Fin n × Fin m`, then reindex to `Fin (n * m)`.
  refine ⟨n * m, ?_⟩
  intro C
  let eWord : Fin ((Nat.succ k) ^ m) ≃ (Fin m → Option (Fin k)) :=
    optionFinPowEquiv k m
  let eProd : (Fin n × Fin m) ≃ Fin (n * m) := finProdFinEquiv
  let C' : (Fin n → Fin m → Option (Fin k)) → κ := fun x =>
    C (fun i => x (eProd.symm i).1 (eProd.symm i).2)
  let Cword : (Fin n → Fin ((Nat.succ k) ^ m)) → κ := fun v => C' (eWord ∘ v)
  have hl := hline Cword
  have hl' : LineMono C' := LineMono.map eWord hl
  let Csub : (Fin n × Fin m → Option (Fin k)) → κ :=
    fun y => C (fun i => y (eProd.symm i))
  have hmono : hl'.line.toSubspace.IsMono Csub := by
    simpa [Csub, C'] using (LineW.toSubspace_isMono (l := hl'.line) (C := Csub)).2
      (hl'.isMono)
  refine ⟨(hl'.line.toSubspace.reindex (Equiv.refl _) (Equiv.refl _) eProd), ?_⟩
  -- transport monochromaticity along reindexing
  simpa [SubspaceW.reindex_isMono, Function.comp] using hmono

end Polymath.DHJ

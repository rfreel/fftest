import Game.Spec

namespace Reachability

abbrev Labels (n : Nat) := Fin n → Option Nat

def Eligible {n} (g : Game n) (a : Labels n) (s : Fin n) : Prop :=
  g.goal s = true ∨
    (if g.agent s then ∃ t, g.edge s t = true ∧ (a t).isSome = true
     else ∀ t, g.edge s t = true → (a t).isSome = true)

instance {n} (g : Game n) (a : Labels n) (s : Fin n) : Decidable (Eligible g a s) :=
  inferInstanceAs (Decidable (_ ∨ _))

def ValidLabels {n} (g : Game n) (a : Labels n) : Prop :=
  ∀ s r, a s = some r →
    (g.goal s = true ∧ r = 0) ∨
    (g.goal s = false ∧
      if g.agent s then
        ∃ t q, g.edge s t = true ∧ a t = some q ∧ q < r
      else ∀ t, g.edge s t = true → ∃ q, a t = some q ∧ q < r)

structure Invariant {n} (g : Game n) (remaining : List (Fin n)) (a : Labels n) : Prop where
  nodup : remaining.Nodup
  size : remaining.length ≤ n
  missing : ∀ s, a s = none ↔ s ∈ remaining
  bounded : ∀ s r, a s = some r → r ≤ n - remaining.length
  valid : ValidLabels g a

structure FinalTable {n} (g : Game n) where
  labels : Labels n
  bounded : ∀ s r, labels s = some r → r ≤ n
  valid : ValidLabels g labels
  closed : ∀ s, labels s = none → ¬ Eligible g labels s

/-- Selecting a finite witness is executable; the existence proof is erased. -/
def first {n} (p : Fin n → Prop) [DecidablePred p] (h : ∃ s, p s) : {s // p s} :=
  match hf : (List.finRange n).find? (fun s => decide (p s)) with
  | some s => ⟨s, by simpa using List.find?_some hf⟩
  | none => False.elim (by
      obtain ⟨s, hs⟩ := h
      have hn := List.find?_eq_none.mp hf s (List.mem_finRange s)
      exact hn (by simpa using hs))

def extend {n} (a : Labels n) (s : Fin n) (r : Nat) : Labels n :=
  fun t => if t = s then some r else a t

theorem extend_old {n} (a : Labels n) (s t : Fin n) (r q : Nat)
    (hs : a s = none) (ht : a t = some q) : extend a s r t = some q := by
  have hne : t ≠ s := by intro h; subst t; simp [hs] at ht
  simp [extend, hne, ht]

theorem extend_valid {n} (g : Game n) (remaining : List (Fin n)) (a : Labels n)
    (inv : Invariant g remaining a) (s : Fin n) (hs : s ∈ remaining)
    (he : Eligible g a s) :
    Invariant g (remaining.erase s)
      (extend a s (if g.goal s then 0 else n - remaining.length + 1)) := by
  let r := if g.goal s then 0 else n - remaining.length + 1
  have hnone : a s = none := (inv.missing s).mpr hs
  have hlen : 0 < remaining.length := List.length_pos_of_mem hs
  have herase := List.length_erase_of_mem hs
  have hsize := inv.size
  constructor
  · exact inv.nodup.erase s
  · omega
  · intro t
    by_cases h : t = s
    · subst t
      simp [extend, inv.nodup.not_mem_erase]
    · simp [extend, h, List.mem_erase_of_ne h, inv.missing]
  · intro t q ht
    by_cases h : t = s
    · subst t
      have hq : r = q := by simpa [extend, r] using ht
      subst q
      dsimp [r]
      split <;> omega
    · have old : a t = some q := by simpa [extend, h] using ht
      have hb := inv.bounded t q old
      omega
  · intro t q ht
    by_cases h : t = s
    · subst t
      have hq : r = q := by simpa [extend, r] using ht
      subst q
      by_cases hg : g.goal s = true
      · exact Or.inl ⟨hg, by simp [r, hg]⟩
      · have hgf : g.goal s = false := Bool.eq_false_iff.mpr hg
        apply Or.inr
        refine ⟨hgf, ?_⟩
        have he' := he.resolve_left hg
        by_cases ho : g.agent s = true
        · simp only [ho, ↓reduceIte] at he' ⊢
          obtain ⟨t, hedge, ht⟩ := he'
          cases hl : a t with
          | none => simp [hl] at ht
          | some v =>
            exact ⟨t, v, hedge, extend_old a s t r v hnone hl, by
              have hb := inv.bounded t v hl
              simp [r, hgf]
              omega⟩
        · have hof : g.agent s = false := Bool.eq_false_iff.mpr ho
          simp only [hof] at he' ⊢
          intro t hedge
          have ht := he' t hedge
          cases hl : a t with
          | none => simp [hl] at ht
          | some v =>
            exact ⟨v, extend_old a s t r v hnone hl, by
              have hb := inv.bounded t v hl
              simp [r, hgf]
              omega⟩
    · have old : a t = some q := by simpa [extend, h] using ht
      rcases inv.valid t q old with goal | ⟨hg, step⟩
      · exact Or.inl goal
      · apply Or.inr
        refine ⟨hg, ?_⟩
        by_cases ho : g.agent t = true
        · simp only [ho, ↓reduceIte] at step ⊢
          obtain ⟨u, v, hedge, hu, hv⟩ := step
          exact ⟨u, v, hedge, extend_old a s u r v hnone hu, hv⟩
        · have hof : g.agent t = false := Bool.eq_false_iff.mpr ho
          simp only [hof] at step ⊢
          intro u hedge
          obtain ⟨v, hu, hv⟩ := step u hedge
          exact ⟨v, extend_old a s u r v hnone hu, hv⟩

def buildTable {n} (g : Game n) (remaining : List (Fin n)) (a : Labels n)
    (inv : Invariant g remaining a) : FinalTable g :=
  match hf : remaining.find? (fun s => decide (Eligible g a s)) with
  | some s =>
    have hs := List.mem_of_find?_eq_some hf
    have he : Eligible g a s := by simpa using List.find?_some hf
    buildTable g (remaining.erase s)
      (extend a s (if g.goal s then 0 else n - remaining.length + 1))
      (extend_valid g remaining a inv s hs he)
  | none => {
      labels := a
      bounded := fun s r h => Nat.le_trans (inv.bounded s r h) (Nat.sub_le n _)
      valid := inv.valid
      closed := by
        intro s hs he
        have hn := List.find?_eq_none.mp hf s ((inv.missing s).mp hs)
        exact hn (by simpa using he)
    }
termination_by remaining.length
decreasing_by
  have hs := List.mem_of_find?_eq_some hf
  have hl := List.length_pos_of_mem hs
  simp only [List.length_erase_of_mem hs]
  omega

def table {n} (g : Game n) : FinalTable g :=
  buildTable g (List.finRange n) (fun _ => none) {
    nodup := List.nodup_finRange n
    size := by simp
    missing := by simp [List.mem_finRange]
    bounded := by simp
    valid := by simp [ValidLabels]
  }

/-- Prefer a successor satisfying p; otherwise choose a legal fallback. -/
def select {n} (g : Game n) (s : Fin n) (p : Fin n → Prop) [DecidablePred p] : Fin n :=
  if h : ∃ t, g.edge s t = true ∧ p t then
    (first (fun t => g.edge s t = true ∧ p t) h).val
  else (first (fun t => g.edge s t = true) (g.total s)).val

theorem select_edge {n} (g : Game n) (s : Fin n) (p : Fin n → Prop) [DecidablePred p] :
    g.edge s (select g s p) = true := by
  unfold select
  split
  next h => exact (first (fun t => g.edge s t = true ∧ p t) h).property.1
  next h => exact (first (fun t => g.edge s t = true) (g.total s)).property

theorem select_property {n} (g : Game n) (s : Fin n) (p : Fin n → Prop) [DecidablePred p]
    (h : ∃ t, g.edge s t = true ∧ p t) : p (select g s p) := by
  simp only [select, dite_eq_left h]
  exact (first (fun t => g.edge s t = true ∧ p t) h).property.2

def resultOfTable {n} (g : Game n) (f : FinalTable g) : Result n where
  winning := fun s => (f.labels s).isSome
  rank := fun s => (f.labels s).getD 0
  agentMove := fun s => select g s (fun t =>
    (f.labels t).isSome = true ∧ (f.labels t).getD 0 < (f.labels s).getD 0)
  environmentMove := fun s => select g s (fun t => f.labels t = none)

def solve : Solver := fun g => resultOfTable g (table g)

theorem table_goal {n} (g : Game n) (f : FinalTable g) (s : Fin n)
    (hg : g.goal s = true) : ∃ r, f.labels s = some r ∧ r = 0 := by
  cases hl : f.labels s with
  | none => exact False.elim (f.closed s hl (Or.inl hg))
  | some r =>
    refine ⟨r, rfl, ?_⟩
    rcases f.valid s r hl with h | h
    · exact h.2
    · simp [hg] at h

theorem table_losing {n} (g : Game n) (f : FinalTable g) (s : Fin n)
    (hs : f.labels s = none) : g.goal s = false ∧
      (if g.agent s then ∀ t, g.edge s t = true → f.labels t = none
       else ∃ t, g.edge s t = true ∧ f.labels t = none) := by
  have hc := f.closed s hs
  have hg : g.goal s = false := Bool.eq_false_iff.mpr (fun h => hc (Or.inl h))
  refine ⟨hg, ?_⟩
  by_cases ho : g.agent s = true
  · simp only [ho, ↓reduceIte]
    intro t hedge
    cases hl : f.labels t with
    | none => rfl
    | some r =>
      exfalso
      apply hc
      right
      simp only [ho, ↓reduceIte]
      exact ⟨t, hedge, by simp [hl]⟩
  · have hof : g.agent s = false := Bool.eq_false_iff.mpr ho
    simp only [hof]
    by_cases h : ∃ t, g.edge s t = true ∧ f.labels t = none
    · exact h
    · exfalso
      apply hc
      right
      simp only [hof]
      intro t hedge
      cases hl : f.labels t with
      | none => exact False.elim (h ⟨t, hedge, hl⟩)
      | some r => simp

theorem result_winning_certificate {n} (g : Game n) (f : FinalTable g) :
    WinningCertificate g (resultOfTable g f) := by
  refine ⟨?_, ?_, ?_⟩
  · intro s hg
    obtain ⟨r, hl, hr⟩ := table_goal g f s hg
    simp [resultOfTable, hl, hr]
  · intro s hw
    cases hl : f.labels s with
    | none => simp [resultOfTable, hl] at hw
    | some r => simpa [resultOfTable, hl] using f.bounded s r hl
  · intro s hw hg
    cases hl : f.labels s with
    | none => simp [resultOfTable, hl] at hw
    | some r =>
      have hv := f.valid s r hl
      rcases hv with h | ⟨_, hv⟩
      · simp [hg] at h
      · by_cases ho : g.agent s = true
        · simp only [ho, ↓reduceIte] at hv ⊢
          obtain ⟨t, q, hedge, ht, hq⟩ := hv
          have hex : ∃ t, g.edge s t = true ∧
              ((f.labels t).isSome = true ∧ (f.labels t).getD 0 < (f.labels s).getD 0) :=
            ⟨t, hedge, by simp [ht, hl, hq]⟩
          have hp := select_property g s _ hex
          exact ⟨select_edge g s _, hp⟩
        · have hof : g.agent s = false := Bool.eq_false_iff.mpr ho
          simp only [hof] at hv ⊢
          intro t hedge
          obtain ⟨q, ht, hq⟩ := hv t hedge
          simp [resultOfTable, ht, hl, hq]

theorem result_losing_certificate {n} (g : Game n) (f : FinalTable g) :
    LosingCertificate g (resultOfTable g f) := by
  intro s hw
  have hl : f.labels s = none := by
    cases h : f.labels s <;> simp_all [resultOfTable]
  obtain ⟨hg, hc⟩ := table_losing g f s hl
  refine ⟨hg, ?_⟩
  by_cases ho : g.agent s = true
  · simp only [ho, ↓reduceIte] at hc ⊢
    intro t hedge
    simp [resultOfTable, hc t hedge]
  · have hof : g.agent s = false := Bool.eq_false_iff.mpr ho
    simp only [hof] at hc ⊢
    have hp := select_property g s (fun t => f.labels t = none) hc
    exact ⟨select_edge g s _, by simp [resultOfTable, hp]⟩

theorem result_agent_legal {n} (g : Game n) (f : FinalTable g) :
    LegalAgent g (liftPosition (resultOfTable g f).agentMove) := by
  intro h s ho
  exact select_edge g s _

theorem result_environment_legal {n} (g : Game n) (f : FinalTable g) :
    LegalEnvironment g (liftPosition (resultOfTable g f).environmentMove) := by
  intro h s ho
  exact select_edge g s _

end Reachability

import Game.Solver
import Game.Contract

namespace Reachability

theorem certificate_wins {n} (g : Game n) (r : Result n)
    (hc : WinningCertificate g r) (hl : LegalAgent g (liftPosition r.agentMove))
    (s : Fin n) (hs : r.winning s = true) :
    StrategyWins g (liftPosition r.agentMove) s := by
  refine ⟨hl, ?_⟩
  intro p hstart hlegal hfollow
  apply Classical.byContradiction
  intro hn
  have nogoal : ∀ k, g.goal (p k) = false := by
    intro k
    apply Bool.eq_false_iff.mpr
    intro hg
    exact hn ⟨k, hg⟩
  have step : ∀ k, r.winning (p k) = true →
      r.winning (p (k + 1)) = true ∧ r.rank (p (k + 1)) < r.rank (p k) := by
    intro k hw
    have hstep := hc.2.2 (p k) hw (nogoal k)
    by_cases ho : g.agent (p k) = true
    · simp only [ho, ↓reduceIte] at hstep
      have hf : p (k + 1) = r.agentMove (p k) := hfollow k ho
      rw [hf]
      exact hstep.2
    · have hof : g.agent (p k) = false := Bool.eq_false_iff.mpr ho
      simp only [hof] at hstep
      exact hstep (p (k + 1)) (hlegal k)
  have bounded : ∀ k, r.winning (p k) = true ∧ r.rank (p k) + k ≤ r.rank s := by
    intro k
    induction k with
    | zero => simpa [hstart] using And.intro hs (Nat.le_refl (r.rank s))
    | succ k ih =>
      have h := step k ih.1
      exact ⟨h.1, by omega⟩
  have h := (bounded (r.rank s + 1)).2
  omega

theorem certificate_avoids {n} (g : Game n) (r : Result n)
    (hc : LosingCertificate g r) (hl : LegalEnvironment g (liftPosition r.environmentMove))
    (s : Fin n) (hs : r.winning s = false) :
    StrategyAvoids g (liftPosition r.environmentMove) s := by
  refine ⟨hl, ?_⟩
  intro p hstart hlegal hfollow
  have stays : ∀ k, r.winning (p k) = false := by
    intro k
    induction k with
    | zero => simpa [hstart] using hs
    | succ k ih =>
      have hstep := (hc (p k) ih).2
      by_cases ho : g.agent (p k) = true
      · simp only [ho, ↓reduceIte] at hstep
        exact hstep (p (k + 1)) (hlegal k)
      · have hof : g.agent (p k) = false := Bool.eq_false_iff.mpr ho
        simp only [hof] at hstep
        have hf : p (k + 1) = r.environmentMove (p k) := hfollow k hof
        rw [hf]
        exact hstep.2
  intro k
  exact (hc (p k) (stays k)).1

/-- Construct an infinite play from the supplied legal strategies. -/
def runState {n} (g : Game n) (σ : HistoryStrategy n) (τ : PositionalStrategy n)
    (s : Fin n) : Nat → List (Fin n) × Fin n
  | 0 => ([], s)
  | k + 1 =>
    let prev := runState g σ τ s k
    (prev.1 ++ [prev.2], if g.agent prev.2 then σ prev.1 prev.2 else τ prev.2)

theorem runState_history {n} (g : Game n) (σ : HistoryStrategy n)
    (τ : PositionalStrategy n) (s : Fin n) (k : Nat) :
    (runState g σ τ s k).1 = history (fun i => (runState g σ τ s i).2) k := by
  induction k with
  | zero => rfl
  | succ k ih => simpa [runState, history, List.range_succ, List.map_append] using ih

theorem winning_not_avoided {n} (g : Game n) (τ : PositionalStrategy n) (s : Fin n)
    (ha : StrategyAvoids g (liftPosition τ) s) : ¬ Winning g s := by
  intro ⟨σ, hσ⟩
  let p : Play n := fun k => (runState g σ τ s k).2
  have hstep : ∀ k, p (k + 1) =
      if g.agent (p k) then σ (history p k) (p k) else τ (p k) := by
    intro k
    change (if g.agent (p k) then σ (runState g σ τ s k).1 (p k) else τ (p k)) = _
    rw [runState_history]
  have hstart : p 0 = s := rfl
  have hlegal : LegalPlay g p := by
    intro k
    rw [hstep]
    by_cases ho : g.agent (p k) = true
    · simp only [ho, ↓reduceIte]
      exact hσ.1 _ _ ho
    · have hof : g.agent (p k) = false := Bool.eq_false_iff.mpr ho
      simp only [hof]
      exact ha.1 (history p k) (p k) hof
  have hfσ : FollowsAgent g σ p := by
    intro k ho
    rw [hstep]
    simp [ho]
  have hfτ : FollowsEnvironment g (liftPosition τ) p := by
    intro k ho
    rw [hstep]
    simp [ho, liftPosition]
  obtain ⟨k, hg⟩ := hσ.2 p hstart hlegal hfσ
  have hn := ha.2 p hstart hlegal hfτ k
  simp [hn] at hg

theorem acceptance : MeetsContract solve where
  winningCertificate := fun g => result_winning_certificate g (table g)
  losingCertificate := fun g => result_losing_certificate g (table g)
  agentLegal := fun g => result_agent_legal g (table g)
  environmentLegal := fun g => result_environment_legal g (table g)
  winningSound := fun g s hs => certificate_wins g (solve g)
    (result_winning_certificate g (table g)) (result_agent_legal g (table g)) s hs
  losingSound := fun g s hs => certificate_avoids g (solve g)
    (result_losing_certificate g (table g)) (result_environment_legal g (table g)) s hs
  complete := by
    intro n g s
    constructor
    · intro hs
      exact ⟨liftPosition (solve g).agentMove,
        certificate_wins g (solve g) (result_winning_certificate g (table g))
          (result_agent_legal g (table g)) s hs⟩
    · intro hw
      cases h : (solve g).winning s with
      | true => rfl
      | false =>
        exact False.elim (winning_not_avoided g (solve g).environmentMove s
          (certificate_avoids g (solve g) (result_losing_certificate g (table g))
            (result_environment_legal g (table g)) s h) hw)

end Reachability

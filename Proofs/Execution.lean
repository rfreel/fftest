import Proofs.Acceptance
import Game.Wire

namespace Reachability.Execution

/-- Finite local checks on an arbitrary candidate, independent of its producer. -/
def LocalCorrect {n} (g : Game n) (r : Result n) : Prop :=
  WinningCertificate g r ∧ LosingCertificate g r ∧
  (∀ s, g.agent s = true → g.edge s (r.agentMove s) = true) ∧
  (∀ s, g.agent s = false → g.edge s (r.environmentMove s) = true)

instance {n} (g : Game n) (r : Result n) : Decidable (LocalCorrect g r) := by
  unfold LocalCorrect WinningCertificate LosingCertificate
  infer_instance

/-- This check does not rerun solve or assume anything about native code. -/
def checkResult {n} (g : Game n) (r : Result n) : Bool := decide (LocalCorrect g r)

structure CertifiedResult {n} (g : Game n) (r : Result n) : Prop where
  winningCertificate : WinningCertificate g r
  losingCertificate : LosingCertificate g r
  agentLegal : LegalAgent g (liftPosition r.agentMove)
  environmentLegal : LegalEnvironment g (liftPosition r.environmentMove)
  wins : ∀ s, r.winning s = true → StrategyWins g (liftPosition r.agentMove) s
  avoids : ∀ s, r.winning s = false → StrategyAvoids g (liftPosition r.environmentMove) s
  complete : ∀ s, r.winning s = true ↔ Winning g s

theorem checkResult_sound {n} (g : Game n) (r : Result n)
    (h : checkResult g r = true) : CertifiedResult g r := by
  have hc : LocalCorrect g r := of_decide_eq_true h
  obtain ⟨hw, hl, ha, he⟩ := hc
  have hal : LegalAgent g (liftPosition r.agentMove) := fun _ s ho => ha s ho
  have hel : LegalEnvironment g (liftPosition r.environmentMove) := fun _ s ho => he s ho
  refine ⟨hw, hl, hal, hel, certificate_wins g r hw hal,
    certificate_avoids g r hl hel, ?_⟩
  intro s
  constructor
  · intro hs
    exact ⟨liftPosition r.agentMove, certificate_wins g r hw hal s hs⟩
  · intro hs
    cases hb : r.winning s with
    | true => rfl
    | false =>
      exact False.elim (winning_not_avoided g r.environmentMove s
        (certificate_avoids g r hl hel s hb) hs)

theorem solver_accepted {n} (g : Game n) : checkResult g (solve g) = true := by
  apply decide_eq_true
  exact ⟨acceptance.winningCertificate g, acceptance.losingCertificate g,
    (fun s ho => acceptance.agentLegal g [] s ho),
    (fun s ho => acceptance.environmentLegal g [] s ho)⟩

/-- The source adapter returns precisely the proved solver's encoding after successful decoding. -/
theorem respond_eq_solver (line : String) (j : Lean.Json) {n} (g : Game n)
    (hs : Wire.strictShape line = true)
    (hp : Lean.Json.parse line = .ok j)
    (hg : Wire.parseGame j = .ok ⟨n, g⟩) :
    Wire.respond line = Wire.encode (solve g) := by
  simp [Wire.respond, hs, hp, hg, Bind.bind, Except.bind, Pure.pure, Except.pure]

end Reachability.Execution

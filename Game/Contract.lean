import Game.Spec

namespace Reachability

/-- Immutable obligations. Implementations must supply a term of this exact type. -/
structure MeetsContract (solve : Solver) : Prop where
  winningCertificate : ∀ {n} (g : Game n), WinningCertificate g (solve g)
  losingCertificate : ∀ {n} (g : Game n), LosingCertificate g (solve g)
  agentLegal : ∀ {n} (g : Game n), LegalAgent g (liftPosition (solve g).agentMove)
  environmentLegal : ∀ {n} (g : Game n), LegalEnvironment g (liftPosition (solve g).environmentMove)
  winningSound : ∀ {n} (g : Game n) s, (solve g).winning s = true →
    StrategyWins g (liftPosition (solve g).agentMove) s
  losingSound : ∀ {n} (g : Game n) s, (solve g).winning s = false →
    StrategyAvoids g (liftPosition (solve g).environmentMove) s
  complete : ∀ {n} (g : Game n) s, (solve g).winning s = true ↔ Winning g s

end Reachability

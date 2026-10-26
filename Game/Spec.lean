import Std

namespace Reachability

/-- A total, finite, turn-based game. true means agent-owned. -/
structure Game (n : Nat) where
  agent : Fin n → Bool
  edge : Fin n → Fin n → Bool
  goal : Fin n → Bool
  total : ∀ s, ∃ t, edge s t = true

abbrev Play (n : Nat) := Nat → Fin n
abbrev HistoryStrategy (n : Nat) := List (Fin n) → Fin n → Fin n
abbrev PositionalStrategy (n : Nat) := Fin n → Fin n

def LegalPlay {n : Nat} (g : Game n) (p : Play n) : Prop :=
  ∀ k, g.edge (p k) (p (k + 1)) = true

/-- The history excludes the current state, which is supplied separately. -/
def history {n : Nat} (p : Play n) (k : Nat) : List (Fin n) :=
  (List.range k).map p

def LegalAgent {n : Nat} (g : Game n) (σ : HistoryStrategy n) : Prop :=
  ∀ h s, g.agent s = true → g.edge s (σ h s) = true

def LegalEnvironment {n : Nat} (g : Game n) (τ : HistoryStrategy n) : Prop :=
  ∀ h s, g.agent s = false → g.edge s (τ h s) = true

def FollowsAgent {n : Nat} (g : Game n) (σ : HistoryStrategy n) (p : Play n) : Prop :=
  ∀ k, g.agent (p k) = true → p (k + 1) = σ (history p k) (p k)

def FollowsEnvironment {n : Nat} (g : Game n) (τ : HistoryStrategy n) (p : Play n) : Prop :=
  ∀ k, g.agent (p k) = false → p (k + 1) = τ (history p k) (p k)

def StrategyWins {n : Nat} (g : Game n) (σ : HistoryStrategy n) (s : Fin n) : Prop :=
  LegalAgent g σ ∧
    ∀ p, p 0 = s → LegalPlay g p → FollowsAgent g σ p → ∃ k, g.goal (p k) = true

def StrategyAvoids {n : Nat} (g : Game n) (τ : HistoryStrategy n) (s : Fin n) : Prop :=
  LegalEnvironment g τ ∧
    ∀ p, p 0 = s → LegalPlay g p → FollowsEnvironment g τ p → ∀ k, g.goal (p k) = false

def Winning {n : Nat} (g : Game n) (s : Fin n) : Prop :=
  ∃ σ : HistoryStrategy n, StrategyWins g σ s

def liftPosition {n : Nat} (σ : PositionalStrategy n) : HistoryStrategy n :=
  fun _ s => σ s

/-- Executable output. Strategies are legal on every state owned by their player. -/
structure Result (n : Nat) where
  winning : Fin n → Bool
  rank : Fin n → Nat
  agentMove : PositionalStrategy n
  environmentMove : PositionalStrategy n

abbrev Solver := {n : Nat} → Game n → Result n

/-- Local, decidable evidence for reaching a goal. -/
def WinningCertificate {n : Nat} (g : Game n) (r : Result n) : Prop :=
  (∀ s, g.goal s = true → r.winning s = true ∧ r.rank s = 0) ∧
  (∀ s, r.winning s = true → r.rank s ≤ n) ∧
  (∀ s, r.winning s = true → g.goal s = false →
    if g.agent s then
      g.edge s (r.agentMove s) = true ∧
        r.winning (r.agentMove s) = true ∧ r.rank (r.agentMove s) < r.rank s
    else
      ∀ t, g.edge s t = true → r.winning t = true ∧ r.rank t < r.rank s)

/-- The complement stays outside goals under the environment's selected moves. -/
def LosingCertificate {n : Nat} (g : Game n) (r : Result n) : Prop :=
  ∀ s, r.winning s = false → g.goal s = false ∧
    (if g.agent s then
      ∀ t, g.edge s t = true → r.winning t = false
    else
      g.edge s (r.environmentMove s) = true ∧ r.winning (r.environmentMove s) = false)

end Reachability

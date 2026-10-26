import Proofs.Execution

set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

namespace NativeWitness
open Reachability

def game0 : Game 0 where
  agent := fun s => ([] : List Bool).getD s.val false
  edge := fun s t => decide ((s.val, t.val) ∈ ([] : List (Nat × Nat)))
  goal := fun s => decide (s.val ∈ ([] : List Nat))
  total := by decide

def response0 : Result 0 where
  winning := fun s => ([] : List Bool).getD s.val false
  rank := fun s => ([] : List Nat).getD s.val 0
  agentMove := fun s => ([] : List (Fin 0)).getD s.val s
  environmentMove := fun s => ([] : List (Fin 0)).getD s.val s

theorem checked0 : Execution.checkResult game0 response0 = true := by decide

theorem certified0 : Execution.CertifiedResult game0 response0 :=
  Execution.checkResult_sound game0 response0 checked0

theorem exact0 : ∀ s : Fin 0,
    response0.winning s = (solve game0).winning s ∧
    response0.rank s = (solve game0).rank s ∧
    response0.agentMove s = (solve game0).agentMove s ∧
    response0.environmentMove s = (solve game0).environmentMove s := by decide +kernel

def game1 : Game 1 where
  agent := fun s => ([true] : List Bool).getD s.val false
  edge := fun s t => decide ((s.val, t.val) ∈ ([(0, 0)] : List (Nat × Nat)))
  goal := fun s => decide (s.val ∈ ([] : List Nat))
  total := by decide

def response1 : Result 1 where
  winning := fun s => ([false] : List Bool).getD s.val false
  rank := fun s => ([0] : List Nat).getD s.val 0
  agentMove := fun s => ([(⟨0, by decide⟩ : Fin 1)] : List (Fin 1)).getD s.val s
  environmentMove := fun s => ([(⟨0, by decide⟩ : Fin 1)] : List (Fin 1)).getD s.val s

theorem checked1 : Execution.checkResult game1 response1 = true := by decide

theorem certified1 : Execution.CertifiedResult game1 response1 :=
  Execution.checkResult_sound game1 response1 checked1

theorem exact1 : ∀ s : Fin 1,
    response1.winning s = (solve game1).winning s ∧
    response1.rank s = (solve game1).rank s ∧
    response1.agentMove s = (solve game1).agentMove s ∧
    response1.environmentMove s = (solve game1).environmentMove s := by decide +kernel

def game2 : Game 1 where
  agent := fun s => ([false] : List Bool).getD s.val false
  edge := fun s t => decide ((s.val, t.val) ∈ ([(0, 0)] : List (Nat × Nat)))
  goal := fun s => decide (s.val ∈ ([0] : List Nat))
  total := by decide

def response2 : Result 1 where
  winning := fun s => ([true] : List Bool).getD s.val false
  rank := fun s => ([0] : List Nat).getD s.val 0
  agentMove := fun s => ([(⟨0, by decide⟩ : Fin 1)] : List (Fin 1)).getD s.val s
  environmentMove := fun s => ([(⟨0, by decide⟩ : Fin 1)] : List (Fin 1)).getD s.val s

theorem checked2 : Execution.checkResult game2 response2 = true := by decide

theorem certified2 : Execution.CertifiedResult game2 response2 :=
  Execution.checkResult_sound game2 response2 checked2

theorem exact2 : ∀ s : Fin 1,
    response2.winning s = (solve game2).winning s ∧
    response2.rank s = (solve game2).rank s ∧
    response2.agentMove s = (solve game2).agentMove s ∧
    response2.environmentMove s = (solve game2).environmentMove s := by decide +kernel

def game3 : Game 2 where
  agent := fun s => ([true, false] : List Bool).getD s.val false
  edge := fun s t => decide ((s.val, t.val) ∈ ([(0, 0), (0, 1), (1, 1)] : List (Nat × Nat)))
  goal := fun s => decide (s.val ∈ ([1] : List Nat))
  total := by decide

def response3 : Result 2 where
  winning := fun s => ([true, true] : List Bool).getD s.val false
  rank := fun s => ([2, 0] : List Nat).getD s.val 0
  agentMove := fun s => ([(⟨1, by decide⟩ : Fin 2), (⟨1, by decide⟩ : Fin 2)] : List (Fin 2)).getD s.val s
  environmentMove := fun s => ([(⟨0, by decide⟩ : Fin 2), (⟨1, by decide⟩ : Fin 2)] : List (Fin 2)).getD s.val s

theorem checked3 : Execution.checkResult game3 response3 = true := by decide

theorem certified3 : Execution.CertifiedResult game3 response3 :=
  Execution.checkResult_sound game3 response3 checked3

theorem exact3 : ∀ s : Fin 2,
    response3.winning s = (solve game3).winning s ∧
    response3.rank s = (solve game3).rank s ∧
    response3.agentMove s = (solve game3).agentMove s ∧
    response3.environmentMove s = (solve game3).environmentMove s := by decide +kernel

def game4 : Game 2 where
  agent := fun s => ([false, true] : List Bool).getD s.val false
  edge := fun s t => decide ((s.val, t.val) ∈ ([(0, 0), (0, 1), (1, 1)] : List (Nat × Nat)))
  goal := fun s => decide (s.val ∈ ([1] : List Nat))
  total := by decide

def response4 : Result 2 where
  winning := fun s => ([false, true] : List Bool).getD s.val false
  rank := fun s => ([0, 0] : List Nat).getD s.val 0
  agentMove := fun s => ([(⟨0, by decide⟩ : Fin 2), (⟨1, by decide⟩ : Fin 2)] : List (Fin 2)).getD s.val s
  environmentMove := fun s => ([(⟨0, by decide⟩ : Fin 2), (⟨1, by decide⟩ : Fin 2)] : List (Fin 2)).getD s.val s

theorem checked4 : Execution.checkResult game4 response4 = true := by decide

theorem certified4 : Execution.CertifiedResult game4 response4 :=
  Execution.checkResult_sound game4 response4 checked4

theorem exact4 : ∀ s : Fin 2,
    response4.winning s = (solve game4).winning s ∧
    response4.rank s = (solve game4).rank s ∧
    response4.agentMove s = (solve game4).agentMove s ∧
    response4.environmentMove s = (solve game4).environmentMove s := by decide +kernel

def game5 : Game 3 where
  agent := fun s => ([true, false, true] : List Bool).getD s.val false
  edge := fun s t => decide ((s.val, t.val) ∈ ([(0, 0), (0, 1), (1, 2), (2, 2)] : List (Nat × Nat)))
  goal := fun s => decide (s.val ∈ ([2] : List Nat))
  total := by decide

def response5 : Result 3 where
  winning := fun s => ([true, true, true] : List Bool).getD s.val false
  rank := fun s => ([3, 2, 0] : List Nat).getD s.val 0
  agentMove := fun s => ([(⟨1, by decide⟩ : Fin 3), (⟨2, by decide⟩ : Fin 3), (⟨2, by decide⟩ : Fin 3)] : List (Fin 3)).getD s.val s
  environmentMove := fun s => ([(⟨0, by decide⟩ : Fin 3), (⟨2, by decide⟩ : Fin 3), (⟨2, by decide⟩ : Fin 3)] : List (Fin 3)).getD s.val s

theorem checked5 : Execution.checkResult game5 response5 = true := by decide

theorem certified5 : Execution.CertifiedResult game5 response5 :=
  Execution.checkResult_sound game5 response5 checked5

theorem exact5 : ∀ s : Fin 3,
    response5.winning s = (solve game5).winning s ∧
    response5.rank s = (solve game5).rank s ∧
    response5.agentMove s = (solve game5).agentMove s ∧
    response5.environmentMove s = (solve game5).environmentMove s := by decide +kernel

def game6 : Game 3 where
  agent := fun s => ([true, false, true] : List Bool).getD s.val false
  edge := fun s t => decide ((s.val, t.val) ∈ ([(0, 1), (1, 0), (1, 2), (2, 2)] : List (Nat × Nat)))
  goal := fun s => decide (s.val ∈ ([2] : List Nat))
  total := by decide

def response6 : Result 3 where
  winning := fun s => ([false, false, true] : List Bool).getD s.val false
  rank := fun s => ([0, 0, 0] : List Nat).getD s.val 0
  agentMove := fun s => ([(⟨1, by decide⟩ : Fin 3), (⟨0, by decide⟩ : Fin 3), (⟨2, by decide⟩ : Fin 3)] : List (Fin 3)).getD s.val s
  environmentMove := fun s => ([(⟨1, by decide⟩ : Fin 3), (⟨0, by decide⟩ : Fin 3), (⟨2, by decide⟩ : Fin 3)] : List (Fin 3)).getD s.val s

theorem checked6 : Execution.checkResult game6 response6 = true := by decide

theorem certified6 : Execution.CertifiedResult game6 response6 :=
  Execution.checkResult_sound game6 response6 checked6

theorem exact6 : ∀ s : Fin 3,
    response6.winning s = (solve game6).winning s ∧
    response6.rank s = (solve game6).rank s ∧
    response6.agentMove s = (solve game6).agentMove s ∧
    response6.environmentMove s = (solve game6).environmentMove s := by decide +kernel

def game7 : Game 3 where
  agent := fun s => ([false, true, false] : List Bool).getD s.val false
  edge := fun s t => decide ((s.val, t.val) ∈ ([(0, 1), (1, 0), (1, 2), (2, 2)] : List (Nat × Nat)))
  goal := fun s => decide (s.val ∈ ([2] : List Nat))
  total := by decide

def response7 : Result 3 where
  winning := fun s => ([true, true, true] : List Bool).getD s.val false
  rank := fun s => ([3, 2, 0] : List Nat).getD s.val 0
  agentMove := fun s => ([(⟨1, by decide⟩ : Fin 3), (⟨2, by decide⟩ : Fin 3), (⟨2, by decide⟩ : Fin 3)] : List (Fin 3)).getD s.val s
  environmentMove := fun s => ([(⟨1, by decide⟩ : Fin 3), (⟨0, by decide⟩ : Fin 3), (⟨2, by decide⟩ : Fin 3)] : List (Fin 3)).getD s.val s

theorem checked7 : Execution.checkResult game7 response7 = true := by decide

theorem certified7 : Execution.CertifiedResult game7 response7 :=
  Execution.checkResult_sound game7 response7 checked7

theorem exact7 : ∀ s : Fin 3,
    response7.winning s = (solve game7).winning s ∧
    response7.rank s = (solve game7).rank s ∧
    response7.agentMove s = (solve game7).agentMove s ∧
    response7.environmentMove s = (solve game7).environmentMove s := by decide +kernel

end NativeWitness
#print axioms NativeWitness.certified0
#print axioms NativeWitness.exact0
#print axioms NativeWitness.certified1
#print axioms NativeWitness.exact1
#print axioms NativeWitness.certified2
#print axioms NativeWitness.exact2
#print axioms NativeWitness.certified3
#print axioms NativeWitness.exact3
#print axioms NativeWitness.certified4
#print axioms NativeWitness.exact4
#print axioms NativeWitness.certified5
#print axioms NativeWitness.exact5
#print axioms NativeWitness.certified6
#print axioms NativeWitness.exact6
#print axioms NativeWitness.certified7
#print axioms NativeWitness.exact7

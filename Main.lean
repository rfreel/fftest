import Game
import Lean.Data.Json

open Lean Reachability

namespace Wire

/-- Count structural colons before Json's map representation can discard duplicate keys.
The accepted schema has exactly four root fields and no nested object values. -/
structure LexState where
  quoted : Bool := false
  escaped : Bool := false
  number : Bool := false
  fractional : Bool := false
  colons : Nat := 0
  depth : Nat := 0
  badNesting : Bool := false

def scanChar (s : LexState) (c : Char) : LexState :=
  if s.quoted then
    if s.escaped then {s with escaped := false}
    else if c == '\\' then {s with escaped := true}
    else if c == '"' then {s with quoted := false}
    else s
  else if c == '"' then {s with quoted := true, number := false}
  else
    let delimiter := c.isWhitespace || c == ',' || c == ']' || c == '}' || c == ':' || c == '[' || c == '{'
    let opens := c == '[' || c == '{'
    let closes := c == ']' || c == '}'
    let depth := if opens then s.depth + 1 else if closes then s.depth - 1 else s.depth
    {s with
      depth := depth
      badNesting := s.badNesting || depth > 3 || (c == '{' && s.depth != 0)
      colons := s.colons + (if c == ':' then 1 else 0)
      fractional := s.fractional || (s.number && (c == '.' || c == 'e' || c == 'E'))
      number := if delimiter then false else s.number || c.isDigit || c == '-'}

def strictShape (line : String) : Bool :=
  let s := line.toList.foldl scanChar {}
  s.colons == 4 && !s.fractional && !s.badNesting

def getNats (j : Json) : Except String (Array Nat) := do
  (← j.getArr?).mapM Json.getNat?

def parseGame (j : Json) : Except String (Σ n, Game n) := do
  let obj ← j.getObj?
  unless obj.toList.length == 4 do throw "invalid_input"
  let n ← (← j.getObjVal? "n").getNat?
  let owners ← (← (← j.getObjVal? "owner").getArr?).mapM Json.getBool?
  let edges ← (← (← j.getObjVal? "edges").getArr?).mapM getNats
  let goals ← getNats (← j.getObjVal? "goals")
  unless owners.size == n && edges.size == n do throw "invalid_input"
  unless goals.all (· < n) && goals.toList.eraseDups.length == goals.size do
    throw "invalid_input"
  for row in edges do
    unless !row.isEmpty && row.all (· < n) && row.toList.eraseDups.length == row.size do
      throw "invalid_input"
  let edge : Fin n → Fin n → Bool := fun s t => (edges[s.val]!).contains t.val
  if ht : ∀ s : Fin n, ∃ t : Fin n, edge s t = true then
    let g : Game n := {
      agent := fun s => owners[s.val]!
      edge := edge
      goal := fun s => goals.contains s.val
      total := ht
    }
    return ⟨n, g⟩
  else throw "invalid_input"

def encode {n} (r : Result n) : Json :=
  let states := List.finRange n
  Json.mkObj [
    ("winning", Json.arr (states.map (fun s => Json.bool (r.winning s))).toArray),
    ("rank", Json.arr (states.map (fun s => toJson (r.rank s))).toArray),
    ("agent_move", Json.arr (states.map (fun s => toJson (r.agentMove s).val)).toArray),
    ("environment_move", Json.arr (states.map (fun s => toJson (r.environmentMove s).val)).toArray)]

def respond (line : String) : Json :=
  let answer : Except String Json := do
    unless strictShape line do throw "invalid_input"
    let j ← Json.parse line
    let ⟨_, g⟩ ← parseGame j
    return encode (Reachability.solve g)
  match answer with
  | .ok j => j
  | .error _ => Json.mkObj [("error", Json.str "invalid_input")]

end Wire

def main : IO UInt32 := do
  let stdin ← IO.getStdin
  let stdout ← IO.getStdout
  repeat
    let line ← stdin.getLine
    if line.isEmpty then break
    stdout.putStrLn (Wire.respond line).compress
    stdout.flush
  return 0

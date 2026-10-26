# Finite reachability games

Status: DRAFT. Human approval is required before implementation.

## Input and meaning

A game has n states numbered 0 through n-1. n may be zero. Each state
has an owner (agent or environment), a set of successor states, and a goal flag.
Every state has at least one successor. Duplicate successors in the wire format
are rejected. Goals count as reached immediately, including at time zero;
play may continue, but a later departure does not undo success.

The agent chooses at agent-owned states; the environment chooses at its states.
A history-dependent strategy receives the entire previous finite history and the
current state. A legal strategy must select an actual successor at every state
owned by its player. The agent wins from s exactly when some legal strategy
reaches a goal in finitely many moves on every compatible infinite legal play.
No uniform bound is assumed in this definition. No probability or fairness
assumption is made about environment moves.

Game/Spec.lean defines these semantics independently of the solver. In
particular Winning quantifies over history-dependent strategies, not just
positional ones. Legal strategy requirements prevent vacuous wins caused by
choosing an illegal move.

## Output and proofs

For every state return a winning flag, a natural-number rank, an agent move and
an environment move. Both move arrays must be legal at all states owned by their
player, including states where that player cannot achieve its objective.

Every goal is winning with rank zero. Every winning rank is at most n. At each
winning non-goal agent state the selected successor is winning with smaller
rank; at each winning non-goal environment state every successor is winning
with smaller rank. No goal lies in the losing region. Every successor of a
losing agent state is losing; the selected successor of a losing environment
state is losing. Ranks outside the winning region are ignored.

Game/Contract.lean additionally requires proofs that the returned agent strategy
actually wins, the returned environment strategy avoids all goals forever from
losing states, and the winning flag is equivalent to the history-dependent
semantic definition. All definitions must be total. No partial/unsafe solver,
additional axioms, proof holes, native_decide, or application FFI is allowed.

The implementation must expose Reachability.solve : Reachability.Solver in
Game/Solver.lean. Proofs/Acceptance.lean must import it and expose
Reachability.acceptance : Reachability.MeetsContract Reachability.solve.
The harness checks this exact type and audits its transitive axioms.

## Executable interface

Build with `lake build game-solver`. The executable reads UTF-8 JSON lines from
stdin and emits one JSON object per line to stdout. It continues after a bad
line. No other stdout output is permitted.

Input: {"n": 2, "owner": [true, false], "edges": [[1], [1]], "goals": [1]}
Output: {"winning": [true, true], "rank": [1, 0],
         "agent_move": [1, 1], "environment_move": [1, 1]}

All four output arrays have length n. Move values are in range even at states
owned by the other player. Winning flags are JSON booleans; rank and move values
are nonnegative JSON integers, excluding booleans. n must be a nonnegative JSON
integer, owner a boolean array of length n, edges a length-n array of nonempty
arrays of distinct in-range integers, goals an array of distinct in-range
integers. Empty n=0 games have empty arrays. Extra or missing keys, wrong types,
duplicate JSON keys, invalid JSON and invalid games produce
{"error":"invalid_input"}. A whitespace-only line is invalid input.

The parser, JSON adapter, printer, compiled code generation and operating system
are outside the mathematical proof boundary and are tested. The adapter must
call Reachability.solve; a separate wire-only solver is not acceptable.

## Acceptance and performance

1. Lean 4.34.0 checks the specification, implementation, exact acceptance term,
   and every checked source file within a 120-second per-file allowance.
2. Acceptance and every public theorem use only propext, Classical.choice and
   Quot.sound as foundational axioms. Imported helpers are included transitively.
3. All 22,100 total games with one through three states, and the empty game,
   match an independent strategy-enumeration/cycle oracle. Both certificates
   are checked independently on every output.
4. Fixed larger regressions and seeded generated games pass. Malformed inputs
   receive the specified error without corrupting following requests.
5. An audit round finds no reachable high-or-critical issue. Reaching the round
   limit is not evidence of convergence.

No speed target is imposed and the performance loop is disabled. The benchmark
records elapsed time, workload hash and toolchain details for a fixed workload;
it does not establish a performance claim or authorize an endless search.

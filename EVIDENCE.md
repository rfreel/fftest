# Verified reachability-game solver

Implementation: `Game/Solver.lean`. Formal acceptance: `Proofs/Acceptance.lean`.
The approved `SPEC.md`, `Game/Spec.lean`, `Game/Contract.lean`, tests, toolchain,
and original acceptance harness are unchanged.

## Formal result

Lean 4.34.0 checks the exact theorem
`Reachability.acceptance : Reachability.MeetsContract Reachability.solve`.
It establishes:

- termination of the executable finite construction, with one state removed
  on each recursive promotion;
- winning certificates with strictly decreasing natural ranks bounded by n;
- legal strategies for both players at every state they own;
- eventual goal reachability under the returned winning strategy;
- permanent goal avoidance under the returned losing-region strategy;
- soundness and completeness against the approved history-dependent strategy
  semantics, using an explicitly constructed infinite play for the reverse direction.

`python3 tools/check_contract.py --complete` passes its exact-type probe and
transitive axiom audit. Only the approved foundational axioms are permitted.
There are no application axioms, proof holes, application FFI, or separate
unproved solver behind the JSON interface.

## Executable checks

- `python3 tools/runtime_tests.py --complete`: **22,180 requests pass**,
  including all **22,101** total games with zero through three states, larger
  regressions, seeded games, malformed requests, and recovery after errors.
- `python3 -m unittest discover -s tests -v`: **five tests pass**. The independent
  strategy-enumeration/cycle oracle agrees with bounded reachability on all
  22,101 small games.
- `ff --config <controller>/factory-live.yaml check`: **seven of seven Lean
  files pass**, followed by the exact contract, harness and executable checks.
- `python3 audit/review.py`: **118 extra protocol requests pass**, including
  58 malformed cases interleaved with valid requests. A 30,000-level invalid
  nesting case and a huge-exponent token are rejected before generic parsing.
- The same review rejects all three deliberate mutations: false winning flags,
  zeroed ranks, and replacing the acceptance theorem with a proof of True.

The independently repeatable review and source hashes are in `audit/review.py`
and `audit/review.json`. These extra checks do not replace the fixed harness.

## Audit round 1

A direct review covered the construction's termination measure, legal fallback
moves, both ownership quantifiers, rank descent, goal-at-time-zero semantics,
empty games, non-vacuous history-dependent strategies, exact proof type,
transitive axioms, duplicate keys, numeric types, nested malformed input and
line recovery. Mutation, crash and regression probes found no reachable high or
critical issue in this reviewed scope. This is a manual audit round, not a claim
that the unavailable autonomous factory audit converged, or that all defects
are excluded.

## Baseline

One local native-process run consumed the 22,101-game workload in **0.444 seconds**.
Workload SHA-256:
`c799430e9e88ec5a50ba6986b7b95f9b7bd8465f63d14555da15b7e48da820c6`.
This is a reproducible baseline observation, not a speed guarantee or comparison.
Run `python3 tools/bench.py` after building `game-solver` to measure another host.

## Reproduce

```sh
lake build
python3 tools/check_contract.py --complete
python3 -m unittest discover -s tests -v
python3 tools/runtime_tests.py --complete
python3 audit/review.py
python3 tools/bench.py
```

The preparation host uses the previously documented executable-path compatibility
shim for Lean. GitHub CI repeats the fixed proof and runtime acceptance on a
normal Linux host without that shim. See `KNOWN_LIMITATIONS.md` for the boundary
between the mathematical proof and the executable environment.

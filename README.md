# fftest

A Lean 4 finite reachability-game solver, built through formal-factory.

**Current state: specification draft. Implementation is blocked on human approval.**

Review [SPEC.md](SPEC.md), [the formal semantics](Game/Spec.lean), and
[the immutable contract](Game/Contract.lean). The contract requires both a
winning strategy with decreasing rank and a losing-region avoidance strategy,
with soundness and completeness against history-dependent play.

## Run the factory

Prerequisites: Python 3.11+, git, elan/Lean, and Codex CLI signed in with
`codex login`. No API key or additional model subscription is required by this
configuration. Existing CLI account usage still applies.

```sh
git clone https://github.com/rfreel/fftest.git
cd fftest
python3 tools/setup_factory.py --start
```

This installs the pinned factory in `../fftest-factory`, makes a separate target
clone, validates the configuration, runs draft checks, and starts a detached
controller with an authenticated localhost-only API. It waits for specification
approval before launching implementation. The factory uses one agent at a time,
no subagents, three attempts per task, three audit rounds, and no performance
loop. Those are work bounds, not a monetary spending cap.

```sh
../fftest-factory/venv/bin/ff --config ../fftest-factory/factory.yaml status
../fftest-factory/venv/bin/ff --config ../fftest-factory/factory.yaml decisions
# After reviewing the concrete specification, replace ID with its decision id:
../fftest-factory/venv/bin/ff --config ../fftest-factory/factory.yaml decide ID approve
```

The controller rechecks decisions periodically. A restart preserves its state.
Stop the controller with its PID from `../fftest-factory/factory.pid`; use
`ff stop RUN_ID` for any agent already running. Stopping the controller alone
does not stop detached agents.

## Check the work

```sh
lake build
python3 -m unittest discover -s tests -v
python3 tools/check_contract.py
# Once implemented, require the full proof and compiled-program tests:
python3 tools/check_contract.py --complete
python3 tools/runtime_tests.py --complete
python3 tools/bench.py
```

A green draft check means the specification and harness compile. It does not
mean a solver exists. Full acceptance requires the exact type
`Reachability.MeetsContract Reachability.solve`, a transitive axiom audit,
22,101 exhaustive games including the empty game, larger regressions, malformed
input tests and audit convergence. The parser/compiler/OS boundary is tested,
not formally verified. See [setup evidence](docs/SETUP.md).

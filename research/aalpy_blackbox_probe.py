#!/usr/bin/env python3
"""Black-box AALpy experiment: recover hidden coupled and independent two-ring Mealy systems.
Only the SUL can be queried by the learner; exact target dynamics are used *after* learning
for independently checking full behavioral equivalence via finite product exploration.
"""
import json
import random
import sys
import time
import traceback
from collections import deque
from importlib.metadata import version
from itertools import combinations
from pathlib import Path

from aalpy.base import SUL
from aalpy.learning_algs import run_KV, run_Lstar
from aalpy.oracles import WMethodEqOracle

ALPHABET = ("A", "B", "P")
HIDDEN_STATES = tuple((a, b) for a in range(3) for b in range(3))
OUTDIR = Path("probe-artifacts")


def hidden_step(state, action, coupled):
    a, b = state
    if action == "A":
        return ((a + 1) % 3, b), "_"
    if action == "B":
        return (a, (b + (a + 1 if coupled else 1)) % 3), "_"
    if action == "P":
        return (a, b), "hit" if (a, b) == (0, 0) else "miss"
    raise ValueError(f"Unknown action: {action}")


class HiddenRingSUL(SUL):
    """The learner sees only reset/step/output, never a transition table."""
    def __init__(self, coupled):
        super().__init__()
        self._coupled = coupled
        self._hidden = None

    def pre(self):
        self._hidden = (0, 0)

    def post(self):
        pass

    def step(self, letter):
        self._hidden, result = hidden_step(self._hidden, letter, self._coupled)
        return result


def reachable_states(coupled):
    todo = deque([(0, 0)])
    seen = {(0, 0)}
    while todo:
        state = todo.popleft()
        for action in ALPHABET:
            next_state, _ = hidden_step(state, action, coupled)
            if next_state not in seen:
                seen.add(next_state)
                todo.append(next_state)
    return seen


def pair_probe(left, right, coupled):
    """BFS for the shortest input word separating two target states."""
    todo = deque([(left, right, ())])
    seen = {(left, right)}
    while todo:
        ls, rs, path = todo.popleft()
        for action in ALPHABET:
            ln, lo = hidden_step(ls, action, coupled)
            rn, ro = hidden_step(rs, action, coupled)
            word = path + (action,)
            if lo != ro:
                return word
            key = (ln, rn)
            if key not in seen:
                seen.add(key)
                todo.append((ln, rn, word))
    return None


def rival_probe():
    """Find a finite intervention distinguishing coupled vs independent dynamics."""
    todo = deque([((0, 0), (0, 0), ())])
    seen = {((0, 0), (0, 0))}
    while todo:
        ls, rs, path = todo.popleft()
        for action in ALPHABET:
            ln, lo = hidden_step(ls, action, True)
            rn, ro = hidden_step(rs, action, False)
            word = path + (action,)
            if lo != ro:
                return word
            key = (ln, rn)
            if key not in seen:
                seen.add(key)
                todo.append((ln, rn, word))
    return None


def full_equivalence(model, coupled):
    """Exact BFS over the hidden-target x learned-hypothesis product automaton.
    A pass proves equal output traces for all finite input words from reset,
    not merely for a bounded test sample.
    """
    start = ((0, 0), model.initial_state, ())
    todo = deque([start])
    seen = {((0, 0), id(model.initial_state))}
    while todo:
        hidden_state, model_state, history = todo.popleft()
        for action in ALPHABET:
            hidden_next, correct_output = hidden_step(hidden_state, action, coupled)
            predicted_output = model_state.output_fun.get(action, "<missing>")
            if correct_output != predicted_output:
                return {
                    "equivalent": False,
                    "counterexample": "".join(history + (action,)),
                    "expected": correct_output,
                    "observed": predicted_output,
                    "product_states_examined": len(seen),
                }
            model_next = model_state.transitions[action]
            key = (hidden_next, id(model_next))
            if key not in seen:
                seen.add(key)
                todo.append((hidden_next, model_next, history + (action,)))
    return {"equivalent": True, "product_states_examined": len(seen)}


def learn_variant(algorithm_name, coupled):
    random.seed(20261029)
    sul = HiddenRingSUL(coupled)
    oracle = WMethodEqOracle(list(ALPHABET), sul, max_number_of_states=9)
    learner = run_KV if algorithm_name == "KV" else run_Lstar
    started = time.monotonic()
    model = learner(
        list(ALPHABET), sul, oracle,
        automaton_type="mealy", print_level=0
    )
    elapsed = round(time.monotonic() - started, 4)
    checked = full_equivalence(model, coupled)
    result = {
        "system": "coupled" if coupled else "independent",
        "algorithm": algorithm_name,
        "inferred_states": len(model.states),
        "membership_queries": sul.num_queries,
        "membership_query_steps": sul.num_steps,
        "equivalence_oracle_steps": oracle.num_steps,
        "duration_seconds": elapsed,
        "full_equivalence": checked,
    }
    if len(model.states) != 9 or not checked["equivalent"]:
        raise AssertionError(json.dumps(result))
    return result


def run():
    OUTDIR.mkdir(exist_ok=True)
    counts = {
        "coupled": len(reachable_states(True)),
        "independent": len(reachable_states(False)),
    }
    pair_probes = {
        mode: [pair_probe(left, right, coupled)
               for left, right in combinations(HIDDEN_STATES, 2)]
        for mode, coupled in (("coupled", True), ("independent", False))
    }
    assert counts == {"coupled": 9, "independent": 9}, counts
    assert all(probe is not None for v in pair_probes.values() for probe in v)
    rival = rival_probe()
    assert rival, "The two rivals should be behaviorally distinguishable"

    record = {
        "aalpy_version": version("aalpy"),
        "fixture": {
            "alphabet": ALPHABET,
            "reachable_hidden_states": counts,
            "separable_hidden_pairs": {k: len(v) for k, v in pair_probes.items()},
            "total_pairs_per_system": 36,
            "max_shortest_probe_length": {k: max(map(len, v)) for k, v in pair_probes.items()},
            "shortest_rival_separating_probe": "".join(rival),
        },
        "experiments": [],
    }
    for name, coupled in (("KV", True), ("Lstar", True), ("KV", False)):
        result = learn_variant(name, coupled)
        record["experiments"].append(result)
        print("CASE_PASS " + json.dumps(result, sort_keys=True), flush=True)

    record["status"] = "PASS"
    (OUTDIR / "aalpy-probe-results.json").write_text(json.dumps(record, indent=2, sort_keys=True))
    print("AALPY_PROBE_JSON=" + json.dumps(record, sort_keys=True), flush=True)


if __name__ == "__main__":
    try:
        run()
    except Exception as exc:
        OUTDIR.mkdir(exist_ok=True)
        error = {
            "status": "FAIL",
            "exception": repr(exc),
            "traceback": traceback.format_exc(),
        }
        (OUTDIR / "aalpy-probe-results.json").write_text(json.dumps(error, indent=2))
        print("AALPY_PROBE_JSON=" + json.dumps(error, sort_keys=True), flush=True)
        sys.exit(1)

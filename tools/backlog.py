from pathlib import Path
root = Path(__file__).resolve().parents[1]
required = ('Game/Solver.lean', 'Proofs/Acceptance.lean')
if any(not (root / f).is_file() for f in required) or 'PENDING:' in (root / 'Main.lean').read_text():
    print('verified-solver\tImplement the approved SPEC.md end to end: total Reachability.solve, '
          'exact MeetsContract proof Reachability.acceptance, Main JSONL adapter calling that solver, '
          'all exhaustive/oracle and malformed-input tests. Keep immutable files unchanged. '
          'Use ff check before submitting. Commit a complete vertical slice; incomplete proofs cannot pass the gate.')

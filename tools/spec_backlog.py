from pathlib import Path
root = Path(__file__).resolve().parents[1]
if any(not (root / p).is_file() for p in ('SPEC.md', 'Game/Spec.lean', 'Game/Contract.lean')):
    print('draft-semantics\tDraft the specified total finite reachability game semantics and contract for human review.')

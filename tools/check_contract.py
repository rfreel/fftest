"""Check the fixed proof boundary, including an exact-typed acceptance probe."""
import argparse
import os
from pathlib import Path
import re
import subprocess
import tempfile

ROOT = Path(__file__).resolve().parents[1]
BANNED = re.compile(r'\b(sorry|admit|axiom|unsafe|partial|native_decide)\b|implemented_by|debug\.skipKernelTC|@\[extern')


def checked(argv, timeout=180):
    p = subprocess.run(argv, cwd=ROOT, capture_output=True, text=True, timeout=timeout)
    if p.returncode or "declaration uses 'sorry'" in p.stdout + p.stderr:
        raise RuntimeError(p.stdout + p.stderr)
    return p.stdout + p.stderr


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--complete', action='store_true')
    args = parser.parse_args()
    for directory in ('Game', 'Proofs'):
        for path in (ROOT / directory).rglob('*.lean'):
            # Conservative scanner; the kernel and transitive axiom probe remain decisive.
            source = re.sub(r'/-.*?-/', '', path.read_text(), flags=re.S)
            source = re.sub(r'--[^\n]*', '', source)
            if BANNED.search(source):
                raise RuntimeError(f'forbidden construct: {path.relative_to(ROOT)}')
    checked(['lake', 'build'])
    if not args.complete and os.environ.get('FF_SPEC_APPROVED') != '1':
        print('PASS: draft specification and contract compile; solver acceptance is pending')
        return
    for path in ('Game/Solver.lean', 'Proofs/Acceptance.lean'):
        if not (ROOT / path).is_file():
            raise RuntimeError(f'missing required implementation: {path}')
    (ROOT / '.lake/build/lib/lean/Proofs').mkdir(parents=True, exist_ok=True)
    checked(['lake', 'env', 'lean', '-o', '.lake/build/lib/lean/Proofs/Acceptance.olean', 'Proofs/Acceptance.lean'])
    probe = ROOT / '.ff_acceptance_probe.lean'
    try:
        probe.write_text('import Proofs.Acceptance\n'
                         'example : Reachability.MeetsContract Reachability.solve := Reachability.acceptance\n'
                         '#print axioms Reachability.acceptance\n')
        output = checked(['lake', 'env', 'lean', str(probe)])
    finally:
        probe.unlink(missing_ok=True)
    if 'unknown' in output.lower() or 'sorryAx' in output:
        raise RuntimeError(output)
    match = re.search(r"'Reachability.acceptance' depends on axioms: \[([^\]]*)\]", output)
    no_axioms = "'Reachability.acceptance' does not depend on any axioms" in output
    if not match and not no_axioms:
        raise RuntimeError('missing axiom audit output: ' + output)
    axioms = {x.strip() for x in match.group(1).split(',') if x.strip()} if match else set()
    if axioms - {'propext', 'Classical.choice', 'Quot.sound'}:
        raise RuntimeError(f'non-foundational axioms: {sorted(axioms)}')
    print('PASS: exact solver contract and transitive axiom audit')


if __name__ == '__main__':
    main()

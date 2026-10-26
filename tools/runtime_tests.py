"""End-to-end tests against the compiled Lean executable, never a Python substitute."""
import argparse
import json
import os
import random
import subprocess
from pathlib import Path
from oracle import check_certificate, games_up_to, oracle

ROOT = Path(__file__).resolve().parents[1]


def regressions():
    yield {'n': 20, 'owner': [True] * 20, 'edges': [[min(i + 1, 19)] for i in range(20)], 'goals': [19]}, [True] * 20
    yield {'n': 20, 'owner': [False] * 20, 'edges': [[i, min(i + 1, 19)] if i < 19 else [19] for i in range(20)], 'goals': [19]}, [False] * 19 + [True]
    yield {'n': 20, 'owner': [True] * 20, 'edges': [[i] for i in range(20)], 'goals': []}, [False] * 20
    rng = random.Random(20261025)
    for _ in range(60):
        n = rng.randint(4, 7)
        g = {'n': n, 'owner': [bool(rng.randrange(2)) for _ in range(n)],
             'edges': [rng.sample(range(n), rng.randint(1, min(n, 2))) for _ in range(n)],
             'goals': [s for s in range(n) if rng.randrange(4) == 0]}
        yield g, oracle(g)


def run_cases(cases, extra_lines=()):
    cases = list(cases)
    lines = [json.dumps(g, separators=(',', ':')) for g, _ in cases] + list(extra_lines)
    proc = subprocess.run([str(ROOT / '.lake/build/bin/game-solver')], input='\n'.join(lines) + '\n',
                          text=True, capture_output=True, timeout=120, cwd=ROOT)
    assert proc.returncode == 0, proc.stderr
    outputs = proc.stdout.splitlines()
    assert len(outputs) == len(lines), ('response count', len(outputs), len(lines), proc.stderr)
    for i, ((g, expected), line) in enumerate(zip(cases, outputs)):
        try:
            r = json.loads(line)
            check_certificate(g, r)
            assert r['winning'] == expected, ('oracle mismatch', g, r, expected)
        except Exception as exc:
            raise AssertionError(f'case {i}: {g!r}: {exc}') from exc
    for line in outputs[len(cases):]:
        assert json.loads(line) == {'error': 'invalid_input'}, line
    return len(lines)


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--complete', action='store_true')
    args = parser.parse_args()
    if not args.complete and os.environ.get('FF_SPEC_APPROVED') != '1':
        print('DRAFT: compiled solver acceptance is pending specification approval')
        return
    subprocess.run(['lake', 'build', 'game-solver'], cwd=ROOT, check=True, timeout=180)
    count = run_cases(((g, oracle(g)) for g in games_up_to(3)))
    malformed = ['null', '[]', '{}', '{', '', ' ',
                 '{"n":0,"n":1,"owner":[],"edges":[],"goals":[]}',
                 '{"n":true,"owner":[],"edges":[],"goals":[]}',
                 '{"n":1,"owner":[true],"edges":[[]],"goals":[]}',
                 '{"n":1,"owner":[true],"edges":[[0,0]],"goals":[]}',
                 '{"n":1,"owner":[1],"edges":[[0]],"goals":[]}',
                 '{"n":1,"owner":[true],"edges":[[1]],"goals":[]}',
                 '{"n":1,"owner":[true],"edges":[[0]],"goals":[0,0]}',
                 '{"n":0,"owner":[],"edges":[],"goals":[],"extra":1}']
    count += run_cases(regressions(), malformed)
    # Error recovery must work within one process, with a valid request after an error.
    valid = '{"n":0,"owner":[],"edges":[],"goals":[]}'
    p = subprocess.run([str(ROOT / '.lake/build/bin/game-solver')],
                       input='bad\n' + valid + '\n', text=True, capture_output=True, timeout=5)
    assert p.returncode == 0 and len(p.stdout.splitlines()) == 2, p
    assert json.loads(p.stdout.splitlines()[0]) == {'error': 'invalid_input'}
    check_certificate({'n': 0, 'owner': [], 'edges': [], 'goals': []}, json.loads(p.stdout.splitlines()[1]))
    print(f'PASS: {count + 2} runtime requests, including 22,101 exhaustive games')


if __name__ == '__main__':
    main()

"""Additional mutation, crash and protocol review, without changing the fixed harness."""
import hashlib
import json
from pathlib import Path
import subprocess
import tempfile
import time

ROOT = Path(__file__).resolve().parents[1]
BINARY = ROOT / '.lake/build/bin/game-solver'


def wire_review():
    valid = {'n': 2, 'owner': [True, False], 'edges': [[0, 1], [1]], 'goals': [1]}
    # Numeric tokens must be integer syntax, and decoded keys must be unique.
    bad = ['null', 'true', 'false', '0', '[]', '', ' ', '{', '{}',
           '{"n":0,"owner":[],"edges":[],"goals":[],"\\u006e":0}',
           '{"n":0,"owner":[],"edges":[],"goals":[],"n":0}',
           '{"n":1e100000,"owner":[],"edges":[],"goals":[]}',
           '{"n":0,"owner":[],"edges":[],"goals":' + '[' * 30000 + ']' * 30000 + '}',
           '{"n":0,"owner":{},"edges":[],"goals":[]}',
           '{"n":0,"owner":[],"edges":[],"goals":[],"extra":{}}']
    for n in ['true', 'false', 'null', '"2"', '-1', '2.0', '2e0', '2E+0', '+2', '02', 'NaN', 'Infinity']:
        bad.append('{"n":' + n + ',"owner":[true,false],"edges":[[0,1],[1]],"goals":[1]}')
    for field, replacements in {
        'owner': [None, {}, [], [True], [True, False, True], [1, 0], ['true', False]],
        'edges': [None, {}, [], [[0]], [[], [1]], [[0, 0], [1]], [[0, 2], [1]], [[True], [1]], [[0.0], [1]], [[-1], [1]], [[[0]], [1]]],
        'goals': [None, {}, [True], ['1'], [2], [-1], [1, 1], [1.0], [[1]]]
    }.items():
        for replacement in replacements:
            bad.append(json.dumps(dict(valid, **{field: replacement})))
    for field in valid:
        bad.append(json.dumps({k: v for k, v in valid.items() if k != field}))
    # Every invalid request is followed by a valid one within the same process.
    good = json.dumps(valid)
    lines = [line for invalid in bad for line in (invalid, good)]
    # Escaped root keys and arbitrary JSON whitespace are valid, not duplicates.
    escaped = '{"\\u006e":2, "owner":[true,false], "edges":[[0,1],[1]], "goals":[1]}'
    lines += [escaped, json.dumps(valid, separators=(' , ', ' : '))]
    proc = subprocess.run([str(BINARY)], input='\n'.join(lines) + '\n', text=True,
                          capture_output=True, timeout=15)
    assert proc.returncode == 0, proc.stderr
    outputs = proc.stdout.splitlines()
    assert len(outputs) == len(lines), (len(outputs), len(lines))
    for i, output in enumerate(outputs):
        answer = json.loads(output)
        if i < len(bad) * 2 and i % 2 == 0:
            assert answer == {'error': 'invalid_input'}, (lines[i][:200], answer)
        else:
            assert answer['winning'] == [True, True], (lines[i], answer)
            assert answer['agent_move'][0] == 1 and answer['rank'][0] > answer['rank'][1], answer
    return {'requests': len(lines), 'invalid_cases': len(bad), 'status': 'pass'}


def mutation_review():
    source = (ROOT / 'Game/Solver.lean').read_text()
    mutants = {
        'all_winning_flags_false': source.replace('winning := fun s => (f.labels s).isSome',
                                                'winning := fun _ => false'),
        'all_ranks_zero': source.replace('rank := fun s => (f.labels s).getD 0',
                                        'rank := fun _ => 0'),
        'weaken_acceptance_to_true': 'import Game.Solver\nimport Game.Contract\n'
                                    'namespace Mutation\n'
                                    'theorem acceptance : True := True.intro\n'
                                    'example : Reachability.MeetsContract Reachability.solve := acceptance\n'
                                    'end Mutation\n'
    }
    results = []
    with tempfile.TemporaryDirectory(prefix='fftest-mutations-') as directory:
        for name, text in mutants.items():
            assert text != source
            path = Path(directory) / (name + '.lean')
            path.write_text(text)
            p = subprocess.run(['lake', 'env', 'lean', str(path)], cwd=ROOT,
                               capture_output=True, text=True, timeout=120)
            assert p.returncode != 0 and 'error' in p.stdout + p.stderr, (name, p.stdout, p.stderr)
            results.append({'mutation': name, 'rejected': True})
    return results


def main():
    start = time.perf_counter()
    result = {
        'protocol_crash_regression_review': wire_review(),
        'proof_mutation_review': mutation_review(),
        'source_sha256': {p: hashlib.sha256((ROOT / p).read_bytes()).hexdigest()
                          for p in ['Game/Solver.lean', 'Proofs/Acceptance.lean', 'Main.lean']},
        'scope': 'One local manual audit round; no claim of exhaustive defect absence or automatic factory audit convergence.'
    }
    result['seconds'] = time.perf_counter() - start
    print(json.dumps(result, indent=2))


if __name__ == '__main__':
    main()

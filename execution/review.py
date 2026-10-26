"""Reject bad native producers, including a valid but non-identical solution."""
import json
from pathlib import Path
import subprocess
import sys
import tempfile

ROOT = Path(__file__).resolve().parents[1]


def main():
    request = (ROOT / 'execution/requests.jsonl').read_text().splitlines()[3] + '\n'
    executable = ROOT / '.lake/build/bin/game-solver'
    response = json.loads(subprocess.check_output([str(executable)], input=request, text=True))
    assert response['rank'] == [2, 0]
    results = []
    with tempfile.TemporaryDirectory(prefix='fftest-native-negative-') as td:
        temporary = Path(td)
        requests = temporary / 'request.jsonl'
        requests.write_text(request)
        for name, ranks in [('invalid_zero_rank', [0, 0]), ('valid_but_not_exact_rank', [1, 0])]:
            mutated = dict(response, rank=ranks)
            literal = json.dumps(json.dumps(mutated) + '\n')
            c = temporary / (name + '.c')
            c.write_text('#include <stdio.h>\nint main(void) { fputs(' + literal + ', stdout); return 0; }\n')
            binary = temporary / name
            subprocess.run(['cc', '-O0', str(c), '-o', str(binary)], check=True)
            output = temporary / ('evidence-' + name)
            p = subprocess.run([sys.executable, str(ROOT / 'execution/certify.py'),
                                '--requests', str(requests), '--binary', str(binary),
                                '--output-dir', str(output)], cwd=ROOT, capture_output=True, text=True)
            report = json.loads((output / 'report.json').read_text())
            assert p.returncode != 0 and report['status'] == 'REJECTED', (name, p.stdout, p.stderr)
            text = (output / 'kernel-check.txt').read_text()
            assert 'error' in text
            if name == 'valid_but_not_exact_rank':
                assert "'NativeWitness.certified0' depends on axioms: [propext, Classical.choice, Quot.sound]" in text
                assert "'NativeWitness.exact0' depends on axioms:" in text and 'sorryAx' in text
            results.append({'producer': name, 'kernel_rejected': True})
    print(json.dumps({'native_mutations': results, 'whole_binary_refinement': 'OPEN'}, indent=2))


if __name__ == '__main__':
    main()

"""Kernel-check captured native responses. This is not whole-binary verification."""
import argparse
import hashlib
import json
from pathlib import Path
import struct
import subprocess
import sys

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / 'tools'))
from oracle import validate_game


def sha(data):
    return hashlib.sha256(data).hexdigest()


def no_duplicate_keys(pairs):
    result = {}
    for key, value in pairs:
        if key in result:
            raise ValueError('duplicate JSON key')
        result[key] = value
    return result


def loads(line):
    return json.loads(line, object_pairs_hook=no_duplicate_keys,
                      parse_constant=lambda value: (_ for _ in ()).throw(ValueError(value)))


def shape(n, r):
    assert type(r) is dict and set(r) == {'winning', 'rank', 'agent_move', 'environment_move'}
    assert all(type(v) is list and len(v) == n for v in r.values())
    assert all(type(v) is bool for v in r['winning'])
    assert all(type(v) is int and v >= 0 for v in r['rank'])
    assert all(type(v) is int and 0 <= v < n for key in ('agent_move', 'environment_move') for v in r[key])
    # No semantic Python oracle here. Lean's kernel checks the actual candidate.


def lean_list(xs):
    return '[' + ', '.join(xs) + ']'


def witness(g, r, i):
    n = g['n']
    owner = lean_list(['true' if x else 'false' for x in g['owner']])
    winning = lean_list(['true' if x else 'false' for x in r['winning']])
    ranks = lean_list([str(x) for x in r['rank']])
    edges = lean_list([f'({s}, {t})' for s, row in enumerate(g['edges']) for t in row])
    goals = lean_list([str(x) for x in g['goals']])
    def moves(key):
        return lean_list([f'(⟨{x}, by decide⟩ : Fin {n})' for x in r[key]])
    return f'''
def game{i} : Game {n} where
  agent := fun s => ({owner} : List Bool).getD s.val false
  edge := fun s t => decide ((s.val, t.val) ∈ ({edges} : List (Nat × Nat)))
  goal := fun s => decide (s.val ∈ ({goals} : List Nat))
  total := by decide

def response{i} : Result {n} where
  winning := fun s => ({winning} : List Bool).getD s.val false
  rank := fun s => ({ranks} : List Nat).getD s.val 0
  agentMove := fun s => ({moves('agent_move')} : List (Fin {n})).getD s.val s
  environmentMove := fun s => ({moves('environment_move')} : List (Fin {n})).getD s.val s

theorem checked{i} : Execution.checkResult game{i} response{i} = true := by decide

theorem certified{i} : Execution.CertifiedResult game{i} response{i} :=
  Execution.checkResult_sound game{i} response{i} checked{i}

theorem exact{i} : ∀ s : Fin {n},
    response{i}.winning s = (solve game{i}).winning s ∧
    response{i}.rank s = (solve game{i}).rank s ∧
    response{i}.agentMove s = (solve game{i}).agentMove s ∧
    response{i}.environmentMove s = (solve game{i}).environmentMove s := by decide +kernel
'''


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--requests', type=Path, required=True)
    parser.add_argument('--output-dir', type=Path, required=True)
    parser.add_argument('--binary', type=Path, default=ROOT / '.lake/build/bin/game-solver')
    args = parser.parse_args()
    binary = args.binary.resolve()
    output = args.output_dir.resolve()
    output.mkdir(parents=True, exist_ok=True)
    raw = args.requests.read_bytes()
    games = [validate_game(loads(line)) for line in raw.decode('utf-8').splitlines()]
    if not games:
        raise ValueError('at least one valid request required')
    image = binary.read_bytes()
    if image[:6] != b'\x7fELF\x02\x01':
        raise ValueError('expected a 64-bit little-endian ELF producer')
    machine = struct.unpack_from('<H', image, 18)[0]
    # A stale success report must never survive a failed rerun.
    report = {'status': 'pending', 'whole_binary_refinement': 'OPEN',
              'binary_sha256': sha(image), 'binary_bytes': len(image), 'elf_machine': machine,
              'requests_sha256': sha(raw), 'request_count': len(games),
              'trusted_binding': 'Python captures bytes and translates JSON to Lean literals; this binding is not kernel-proved.'}
    report_path = output / 'report.json'
    report_path.write_text(json.dumps(report, indent=2) + '\n')
    proc = subprocess.run([str(binary)], input=raw, capture_output=True, timeout=30)
    (output / 'requests.jsonl').write_bytes(raw)
    (output / 'responses.jsonl').write_bytes(proc.stdout)
    (output / 'stderr.txt').write_bytes(proc.stderr)
    if proc.returncode:
        raise RuntimeError('native producer did not exit successfully')
    replies = proc.stdout.decode('utf-8').splitlines()
    if len(replies) != len(games):
        raise ValueError('native response count differs from request count')
    results = [loads(line) for line in replies]
    for g, r in zip(games, results):
        shape(g['n'], r)
    source = ('import Proofs.Execution\n\nset_option maxRecDepth 100000\n'
              'set_option maxHeartbeats 2000000\n\nnamespace NativeWitness\nopen Reachability\n')
    source += ''.join(witness(g, r, i) for i, (g, r) in enumerate(zip(games, results)))
    source += '\nend NativeWitness\n'
    source += ''.join(f'#print axioms NativeWitness.certified{i}\n#print axioms NativeWitness.exact{i}\n'
                      for i in range(len(games)))
    proof = output / 'Witness.lean'
    proof.write_text(source)
    check = subprocess.run(['lake', 'env', 'lean', str(proof)], cwd=ROOT,
                           capture_output=True, text=True, timeout=120)
    (output / 'kernel-check.txt').write_text(check.stdout + check.stderr)
    if check.returncode or "uses 'sorry'" in check.stdout + check.stderr:
        report['status'] = 'REJECTED'
        report_path.write_text(json.dumps(report, indent=2) + '\n')
        raise RuntimeError('kernel rejected captured response; see kernel-check.txt')
    # Record exact dependency output; the factory also audits all public theorem axioms.
    import re
    audits = re.findall(r"'([^']+)' depends on axioms: \[([^\]]*)\]", check.stdout)
    for name, used in audits:
        extra = {x.strip() for x in used.split(',') if x.strip()} - {'propext', 'Classical.choice', 'Quot.sound'}
        if extra:
            raise RuntimeError(f'unapproved axioms: {name}: {extra}')
    audited = {name for name, _ in audits} | set(re.findall(r"'([^']+)' does not depend on any axioms", check.stdout))
    required = {f'NativeWitness.{kind}{i}' for i in range(len(games)) for kind in ('certified', 'exact')}
    if not required <= audited:
        raise RuntimeError('missing axiom audit for a captured response')
    report.update(status='KERNEL_CHECKED_RESPONSES', responses_sha256=sha(proc.stdout),
                  witness_sha256=sha(source.encode()), checked_theorems=len(required),
                  claim='These captured responses satisfy the game contract and exactly equal solve on these decoded inputs. No all-input machine-code theorem is asserted.')
    report_path.write_text(json.dumps(report, indent=2) + '\n')
    print(json.dumps(report, indent=2))


if __name__ == '__main__':
    main()

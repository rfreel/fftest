"""Record a baseline only. No target, ratio or claimed performance guarantee."""
import hashlib
import json
import subprocess
import time
from pathlib import Path
from oracle import games_up_to
root = Path(__file__).resolve().parents[1]
payload = ''.join(json.dumps(g, separators=(',', ':')) + '\n' for g in games_up_to(3))
start = time.perf_counter()
p = subprocess.run([str(root / '.lake/build/bin/game-solver')], input=payload,
                   text=True, capture_output=True, check=True, timeout=120)
elapsed = time.perf_counter() - start
assert len(p.stdout.splitlines()) == 22101
print(json.dumps({'seconds': elapsed, 'cases': 22101,
                  'workload_sha256': hashlib.sha256(payload.encode()).hexdigest(),
                  'lean': subprocess.check_output(['lean', '--version'], text=True).strip()}))

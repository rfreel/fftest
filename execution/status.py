"""The machine-code target cannot be marked complete by response tests."""
import argparse
import json
from pathlib import Path
parser = argparse.ArgumentParser()
parser.add_argument('--require-whole-binary', action='store_true')
args = parser.parse_args()
report = json.loads((Path(__file__).parent / 'checked/report.json').read_text())
state = {'source_solver': 'PROVED', 'source_response_checker': 'PROVED',
         'captured_native_responses': report['status'],
         'captured_response_count': report['request_count'],
         'whole_binary_refinement': 'OPEN',
         'reason': 'No machine-code proof for the pinned x86-64 ELF, its dynamic libraries, loader, and input/output environment.'}
print(json.dumps(state, indent=2))
raise SystemExit(1 if args.require_whole_binary else 0)

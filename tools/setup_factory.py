#!/usr/bin/env python3
"""Install the pinned factory into a controller directory outside the target repo."""
import argparse
import json
import os
from pathlib import Path
import secrets
import shutil
import subprocess
import sys
import time
import urllib.error
import urllib.request

ROOT = Path(__file__).resolve().parents[1]


def run(argv, **kwargs):
    subprocess.run([str(x) for x in argv], check=True, **kwargs)


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--directory', type=Path, default=ROOT.parent / 'fftest-factory')
    parser.add_argument('--start', action='store_true', help='start at the human specification approval gate')
    parser.add_argument('--factory-source', type=Path, help='reuse a local clone at the pinned commit')
    args = parser.parse_args()
    controller = args.directory.resolve()
    if controller == ROOT or ROOT in controller.parents:
        raise SystemExit('Controller directory must be outside the target repository')
    controller.mkdir(parents=True, exist_ok=True)
    lock = json.loads((ROOT / 'ff.lock.json').read_text())
    source = args.factory_source.resolve() if args.factory_source else controller / 'formal-factory'
    if not source.exists():
        run(['git', 'clone', lock['repository'], source])
        run(['git', 'checkout', '--detach', lock['commit']], cwd=source)
    commit = subprocess.check_output(['git', 'rev-parse', 'HEAD'], cwd=source, text=True).strip()
    if commit != lock['commit']:
        raise SystemExit(f'Factory checkout is not pinned: {commit}')
    if subprocess.check_output(['git', 'status', '--porcelain'], cwd=source, text=True).strip():
        raise SystemExit('Factory source must be clean')
    venv = controller / 'venv'
    if not venv.exists():
        run([sys.executable, '-m', 'venv', venv])
    python = venv / 'bin/python'
    run([python, '-m', 'pip', 'install', '-e', source])
    for tool in ('git', 'lean', 'lake', 'codex'):
        if not shutil.which(tool):
            raise SystemExit(f'{tool} is missing from PATH; install it and rerun setup')
    run(['lean', '--version'])
    run(['codex', 'login', 'status'])
    target = controller / 'target'
    if not target.exists():
        run(['git', 'clone', 'https://github.com/rfreel/fftest.git', target])
    if subprocess.check_output(['git', 'status', '--porcelain'], cwd=target, text=True).strip():
        raise SystemExit('Factory target clone is dirty; inspect it before continuing')
    run(['git', 'fetch', 'origin', 'main'], cwd=target)
    run(['git', 'merge', '--ff-only', 'origin/main'], cwd=target)
    env = dict(os.environ, FF_TARGET_REPO=str(target), FF_STATE_DIR=str(controller / 'state'),
               FF_CODEX_BINARY=shutil.which('codex'))
    template = (ROOT / 'factory.template.yaml').read_text()
    for key in ('FF_TARGET_REPO', 'FF_STATE_DIR', 'FF_CODEX_BINARY'):
        template = template.replace('${' + key + '}', json.dumps(env[key]))
        template = template.replace('${' + key + ':-codex}', json.dumps(env[key]))
    config = controller / 'factory.yaml'
    config.write_text(template)
    ff = venv / 'bin/ff'
    run([ff, '--config', config, 'validate'], env=env)
    # Preflight all draft checks before launching agents or requesting approval.
    run([ff, '--config', config, 'check'], env=env, cwd=target)
    print(f'Prepared {config}', flush=True)
    if not args.start:
        print(f'Start: {ff} --config {config} run --api 127.0.0.1:8787')
        return
    pidfile = controller / 'factory.pid'
    if pidfile.exists():
        try:
            pid = int(pidfile.read_text())
            cmdline = Path(f'/proc/{pid}/cmdline').read_bytes()
            if b'ff' in cmdline and str(config).encode() in cmdline:
                print('Factory is already running')
                return
        except (OSError, ValueError):
            pass
    # A live API prevents accidentally starting a second controller on this port.
    try:
        urllib.request.urlopen('http://127.0.0.1:8787/status', timeout=1)
    except urllib.error.HTTPError:
        raise SystemExit('Port 8787 already has an API; inspect before starting another factory')
    except OSError:
        pass
    else:
        raise SystemExit('Port 8787 is already in use')
    tokenfile = controller / 'api-token'
    if not tokenfile.exists():
        with tokenfile.open('x', opener=lambda path, flags: os.open(path, flags, 0o600)) as f:
            f.write(secrets.token_hex(32))
    env['FF_API_TOKEN'] = tokenfile.read_text().strip()
    with (controller / 'factory.log').open('a') as log:
        proc = subprocess.Popen([str(ff), '--config', str(config), 'run', '--api', '127.0.0.1:8787'],
                                cwd=controller, env=env, stdin=subprocess.DEVNULL,
                                stdout=log, stderr=subprocess.STDOUT, start_new_session=True)
    pidfile.write_text(str(proc.pid))
    for _ in range(20):
        time.sleep(.25)
        if proc.poll() is not None:
            raise SystemExit(f'Factory exited; inspect {controller / "factory.log"}')
        try:
            req = urllib.request.Request('http://127.0.0.1:8787/status',
                                         headers={'Authorization': 'Bearer ' + env['FF_API_TOKEN']})
            with urllib.request.urlopen(req, timeout=1) as response:
                state = json.load(response)
            print('Factory API is running on localhost; specification approval is required.')
            return
        except OSError:
            pass
    raise SystemExit('Factory did not become ready; inspect factory.log')


if __name__ == '__main__':
    main()

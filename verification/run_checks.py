#!/usr/bin/env python3
"""Audit the recorded targets; optionally replay their complete proof exports."""
from pathlib import Path
from datetime import datetime, timezone
import argparse
import hashlib
import json
import os
import re
import subprocess

parser = argparse.ArgumentParser(description=__doc__)
parser.add_argument('--kernels', action='store_true', help='run Lean, NanoDa and con-ron on exported proofs')
args = parser.parse_args()
root = Path(__file__).resolve().parents[1]
stamp = datetime.now(timezone.utc).strftime('%Y%m%dT%H%M%S%fZ')
out = root / '.lake' / 'verification' / stamp
out.mkdir(parents=True)
groups = json.loads((root / 'verification' / 'targets.json').read_text())
targets = groups['headline'] + groups['components']
allowed = {'propext', 'Classical.choice', 'Quot.sound'}
report = {'checked_at_utc': datetime.now(timezone.utc).isoformat(), 'targets': targets,
          'kernel_checks_requested': args.kernels, 'status': 'running', 'stages': {},
          'scope': 'Local statement and axiom audit, with optional standalone kernels; not protected Palomar verification.'}
env = os.environ.copy()

def save():
    (out / 'RESULTS.json').write_text(json.dumps(report, indent=2) + '\n')

def run(name, command, destination=None):
    stdout, stderr = destination or out / f'{name}.log', out / f'{name}-stderr.log'
    report['current_stage'] = name
    save()
    print(f'Starting {name}', flush=True)
    with stdout.open('w') as output, stderr.open('w') as errors:
        result = subprocess.run(command, cwd=root, env=env, stdout=output, stderr=errors)
    report['stages'][name] = {'command': command, 'exit_code': result.returncode,
                            'stdout': str(stdout.relative_to(root)), 'stderr': str(stderr.relative_to(root))}
    save()
    if result.returncode:
        print(stdout.read_text(errors='replace')[-6000:])
        print(stderr.read_text(errors='replace')[-6000:])
        raise RuntimeError(f'{name} failed with exit {result.returncode}')
    print(f'{name}: passed', flush=True)

try:
    config = json.loads((root / 'comparator.json').read_text())
    if config['theorem_names'] != groups['headline']:
        raise RuntimeError('Comparator targets do not match verification/targets.json')
    if not set(config['permitted_axioms']) <= allowed:
        raise RuntimeError('Comparator configuration permits nonstandard axioms')
    if len(targets) != len(set(targets)):
        raise RuntimeError('Duplicate audit target')
    run('axioms', ['lake', 'env', 'lean', 'verification/Audit.lean'])
    text = (out / 'axioms.log').read_text()
    axioms = {}
    for target in targets:
        match = re.search(re.escape("'" + target + "' depends on axioms: [") + r'(.*?)\]', text, re.S)
        if match:
            names = {part.strip() for part in match[1].split(',') if part.strip()}
        elif "'" + target + "' does not depend on any axioms" in text:
            names = set()
        else:
            raise RuntimeError(f'Missing axiom report for {target}')
        if not names <= allowed:
            raise RuntimeError(f'Unpermitted axioms for {target}: {sorted(names - allowed)}')
        axioms[target] = sorted(names)
    report['axioms'] = axioms
    save()
    if args.kernels:
        prefix = Path(subprocess.check_output(['lake', 'env', 'lean', '--print-prefix'],
                                             cwd=root, env=env, text=True).strip())
        env['PATH'] = str(prefix / 'bin') + os.pathsep + env.get('PATH', '')
        for name in ('leanexport', 'leanchecker', 'nanoda_bin', 'con-ron'):
            if not (prefix / 'bin' / name).is_file():
                raise RuntimeError(f'The pinned toolchain does not provide {name}')
        export = out / 'proofs.ndjson'
        run('export', ['lake', 'env', 'leanexport', 'Solution', '--', *targets], export)
        if 'PANIC' in (out / 'export-stderr.log').read_text():
            raise RuntimeError('Proof export contains PANIC')
        digest = hashlib.sha256()
        with export.open('rb') as source:
            for chunk in iter(lambda: source.read(1024 * 1024), b''):
                digest.update(chunk)
        report['export'] = {'sha256': digest.hexdigest(), 'bytes': export.stat().st_size,
                            'path': str(export.relative_to(root))}
        save()
        run('lean', [str(prefix / 'bin' / 'leanchecker'), '--silent', '--from-export', str(export)])
        nano_config = out / 'nanoda.json'
        nano_config.write_text(json.dumps({'export_file_path': str(export), 'use_stdin': False,
            'permitted_axioms': sorted(allowed), 'unpermitted_axiom_hard_error': True,
            'num_threads': 4, 'nat_extension': True, 'string_extension': True,
            'print_success_message': True}, indent=2) + '\n')
        run('nanoda', [str(prefix / 'bin' / 'nanoda_bin'), str(nano_config)])
        run('con-ron', [str(prefix / 'bin' / 'con-ron'), '--verified', '--jobs=4', str(export)])
    report['status'] = 'pass'
except Exception as error:
    report['status'] = 'fail'
    report['error'] = str(error)
    print(str(error), flush=True)
finally:
    save()
    print(f'Report: {out.relative_to(root) / "RESULTS.json"}', flush=True)
raise SystemExit(0 if report['status'] == 'pass' else 1)

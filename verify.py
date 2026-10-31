"""Compile the paper's Lean sources and check their paper correspondence."""
import argparse
import json
import os
from pathlib import Path
import shutil
import subprocess
import sys

ROOT = Path(__file__).resolve().parent


def run(command, env, log=None):
    print('+ ' + ' '.join(map(str, command)), flush=True)
    if log is None:
        subprocess.run(command, cwd=ROOT, env=env, check=True)
    else:
        with log.open('w', encoding='utf-8') as output:
            result = subprocess.run(command, cwd=ROOT, env=env, stdout=output,
                                    stderr=subprocess.STDOUT)
        if result.returncode:
            print(log.read_text(encoding='utf-8', errors='replace')[-12000:], file=sys.stderr)
            raise subprocess.CalledProcessError(result.returncode, command)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--jobs', type=int, choices=range(1, 10), default=2,
                        metavar='1..9', help='Concurrent compiler processes (default: 2; 6 GiB each)')
    parser.add_argument('--resume', action='store_true',
                        help='Reuse this checkout\'s source- and object-hash-validated results')
    parser.add_argument('--skip-cache', action='store_true',
                        help='Skip Mathlib cache download when dependencies are already installed')
    parser.add_argument('--recorded-only', action='store_true',
                        help='Check archived evidence only; does NOT run Lean')
    args = parser.parse_args()
    if sys.version_info < (3, 10):
        parser.error('Python 3.10 or later is required')
    if not __debug__:
        parser.error('Run without python -O: verification requires assertions')
    env = dict(os.environ, PYTHONOPTIMIZE='0', PYTHONUTF8='1')
    checker = [sys.executable, 'verification/check_correspondence.py']
    if args.recorded_only:
        if args.resume or args.skip_cache:
            parser.error('--recorded-only cannot be combined with build options')
        run(checker, env)
        print('PASS: archived evidence and source correspondence; Lean was NOT run.')
        return
    if not shutil.which('lake') or not shutil.which('git'):
        parser.error('Install Git and Lean via Elan, then reopen your terminal; see README.md')
    evidence = ROOT / '.lake/verification'
    evidence.mkdir(parents=True, exist_ok=True)
    status = evidence / 'verification-result.json'
    status.write_text(json.dumps({'status': 'RUNNING'}), encoding='utf-8')
    try:
        if not args.skip_cache:
            run(['lake', 'exe', 'cache', 'get'], env)
        # Do not print this environment: it may contain user credentials.
        result = subprocess.run(['lake', 'env', sys.executable, '-c',
                                 'import json,os; print(json.dumps(dict(os.environ)))'],
                                cwd=ROOT, env=env, capture_output=True, text=True, check=True)
        lean_env = json.loads(result.stdout)
        version = subprocess.run(['lean', '--version'], cwd=ROOT, env=lean_env,
                                 capture_output=True, text=True, check=True).stdout.strip()
        expected = (ROOT / 'lean-toolchain').read_text().strip().split(':v')[-1]
        if not version.startswith('Lean (version ' + expected + ','):
            raise RuntimeError('Unexpected Lean toolchain: ' + version)
        print(version, flush=True)
        rebuild = [sys.executable, 'verification/rebuild.py', '--jobs', str(args.jobs),
                   '--output-dir', str(evidence)]
        if args.resume:
            rebuild.append('--resume')
        run(rebuild, lean_env)
        objects = ROOT / '.lake/audit-build/lib/lean'
        old_build = (ROOT / '.lake/build/lib/lean').resolve()
        paths = [p for p in lean_env.get('LEAN_PATH', '').split(os.pathsep)
                 if p and Path(p).resolve() != old_build]
        lean_env['LEAN_PATH'] = os.pathsep.join([str(objects), *paths])
        lean_env['LEAN_NUM_THREADS'] = '3'
        adapter = objects / 'verification/Proposition2Planar.olean'
        adapter.parent.mkdir(parents=True, exist_ok=True)
        for source, target, log in [
            ('verification/Proposition2Planar.lean', adapter, 'proposition2-planar-axioms.txt'),
            ('verification/DIntegrationAudit.lean', None, 'd-integration-axioms.log'),
            ('PaperIndex.lean', None, 'paper-index.log'),
        ]:
            command = ['lean', '-M6144', '-DrelaxedAutoImplicit=false', source]
            if target:
                command.extend(['-o', str(target)])
            run(command, lean_env, evidence / log)
        run([*checker, '--evidence-dir', str(evidence)], env,
            evidence / 'correspondence-check.json')
        status.write_text(json.dumps({'status': 'PASS', 'lean': version,
            'mode': 'hash_validated_resume' if args.resume else 'fresh_project_compilation',
            'library_modules': 1612, 'named_statements': 81,
            'supplementary_adapter_and_index': 'PASS'}, indent=2) + '\n', encoding='utf-8')
    except BaseException as error:
        status.write_text(json.dumps({'status': 'FAIL', 'error': str(error)}, indent=2) + '\n',
                          encoding='utf-8')
        raise
    print('PASS: Lean compilation, axiom audits and correspondence for 81 named statements.')
    print('Fresh reports: .lake/verification/ (archived reports were not overwritten).')


if __name__ == '__main__':
    try:
        main()
    except (subprocess.CalledProcessError, RuntimeError) as error:
        print('FAIL: ' + str(error), file=sys.stderr)
        sys.exit(1)

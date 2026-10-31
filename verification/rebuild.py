"""Fresh dependency-ordered compilation with bounded parallelism and axiom audit.

Run: lake env python verification/rebuild.py --jobs 18
Use --compile-only to prepare the dependency cache during proof development.
That mode records COMPILED, never PASS; both audits remain required for release.
Only pinned external package oleans are reused. Project oleans are built in a
separate directory. CPU affinity limits this process and its compiler children
to at most eighteen logical processors. Each compiler has three Lean threads; combined
compiler memory limits stay below 56 GiB.
"""
from concurrent.futures import ThreadPoolExecutor, wait, FIRST_COMPLETED
from pathlib import Path
import argparse
import hashlib
import json
import os
import re
import subprocess
import sys
import time

ROOT = Path(__file__).resolve().parents[1]


def limit_cpus(maximum=18):
    if os.name == 'nt':
        import ctypes
        from ctypes import wintypes
        kernel = ctypes.WinDLL('kernel32', use_last_error=True)
        kernel.GetCurrentProcess.restype = wintypes.HANDLE
        kernel.GetProcessAffinityMask.argtypes = [wintypes.HANDLE,
            ctypes.POINTER(ctypes.c_size_t), ctypes.POINTER(ctypes.c_size_t)]
        kernel.SetProcessAffinityMask.argtypes = [wintypes.HANDLE, ctypes.c_size_t]
        handle = kernel.GetCurrentProcess()
        available, system = ctypes.c_size_t(), ctypes.c_size_t()
        if not kernel.GetProcessAffinityMask(handle, ctypes.byref(available), ctypes.byref(system)):
            raise ctypes.WinError(ctypes.get_last_error())
        cpus = [i for i in range(available.value.bit_length()) if available.value & (1 << i)][:maximum]
        mask = sum(1 << i for i in cpus)
        if not cpus or not kernel.SetProcessAffinityMask(handle, mask):
            raise ctypes.WinError(ctypes.get_last_error())
        return cpus
    if hasattr(os, 'sched_getaffinity'):
        cpus = sorted(os.sched_getaffinity(0))[:maximum]
        os.sched_setaffinity(0, cpus)
        return cpus
    # macOS has no process CPU-affinity API. When the whole machine already
    # has at most the requested bound, every worker necessarily respects it.
    count = os.cpu_count()
    if sys.platform == 'darwin' and count is not None and count <= maximum:
        return list(range(count))
    raise RuntimeError('Cannot enforce the requested logical-CPU limit on this platform')


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--jobs', type=int, default=18, choices=range(1, 19))
    parser.add_argument('--resume', action='store_true')
    parser.add_argument('--output-dir', type=Path,
                        help='Write new build evidence here instead of replacing the archived reports')
    parser.add_argument('--compile-only', action='store_true',
                        help='Prepare module cache without audits; result is COMPILED, not PASS')
    args = parser.parse_args()
    memory_mib = min(6144, 57344 // args.jobs)
    cpu_ids = limit_cpus()
    started = time.time()
    out = ROOT/'.lake/audit-build/lib/lean'
    evidence = args.output_dir.resolve() if args.output_dir else ROOT/'verification'
    evidence.mkdir(parents=True, exist_ok=True)
    logs = evidence/'compiler-logs'
    out.mkdir(parents=True, exist_ok=True)
    (out.parent.parent/'scheduler.json').write_text(json.dumps({'pid': os.getpid(),
        'cwd': str(ROOT), 'cpu_ids': cpu_ids, 'jobs': args.jobs}), encoding='utf-8')
    print(f'CPU upper bound: {cpu_ids}; jobs: {args.jobs}; memory per compiler: {memory_mib} MiB', flush=True)
    logs.mkdir(parents=True, exist_ok=True)
    env = dict(os.environ, LEAN_NUM_THREADS='3')
    paths = env.get('LEAN_PATH', '').split(os.pathsep)
    paths = [p for p in paths if p and Path(p).resolve() != (ROOT/'.lake/build/lib/lean').resolve()]
    env['LEAN_PATH'] = os.pathsep.join([str(out), *paths])
    files = {'.'.join(p.relative_to(ROOT).with_suffix('').parts): p
             for base in ('Paper', 'GraphTheory') for p in (ROOT/base).rglob('*.lean')}
    files['Paper'] = ROOT/'Paper.lean'
    deps = {m: set(re.findall(r'^import\s+([\w.]+)', p.read_text(encoding='utf-8'), re.M)) & files.keys()
            for m, p in files.items()}
    priority = set()
    def prioritize(m):
        if m in priority or m not in files:
            return
        priority.add(m)
        for dep in deps[m]:
            prioritize(dep)
    for m in ('Paper.Endpoints.Rounding.Slack', 'Paper.Endpoints.Rounding.CurrentBudget',
              'Paper.Certificates.Counting.SubgraphCertificates', 'Paper.Optimality.Examples.SplitGraphGap',
              'Paper.Initialization.Pruning.SimpleD0', 'Paper.Endpoints.Rounding.CurrentRounding',
              'Paper.Endpoints.Bounds.SeparateDensities'):
        prioritize(m)
    result_path = evidence/'build-result.json'
    results = json.loads(result_path.read_text()).get('modules', {}) if args.resume and result_path.exists() else {}
    done = set()
    # A resumed result is reusable only when its input and all local imports match.
    changed = True
    while changed:
        changed = False
        for m, p in files.items():
            r = results.get(m, {})
            obj = out/(m.replace('.', '/')+'.olean')
            if m not in done and deps[m] <= done and r.get('status') == 'PASS' and r.get('sha256') == sha(p) and obj.exists() and r.get('olean_sha256') == sha(obj):
                done.add(m)
                changed = True
    results = {m: results[m] for m in done}
    failed = set()
    pending = set(files)-done
    active = {}

    def compile_one(m):
        p = files[m]
        obj = out/(m.replace('.', '/')+'.olean')
        obj.parent.mkdir(parents=True, exist_ok=True)
        before = sha(p)
        t = time.time()
        cmd = ['lean', f'-M{memory_mib}', '-DrelaxedAutoImplicit=false', '-DmaxSynthPendingDepth=3',
               '-Dpp.unicode.fun=true', '-Dweak.linter.mathlibStandardSet=true',
               str(p.relative_to(ROOT)), '-o', str(obj)]
        with (logs/(m+'.log')).open('w', encoding='utf-8') as log:
            proc = subprocess.run(cmd, cwd=ROOT, env=env, stdout=log, stderr=subprocess.STDOUT)
        status = 'PASS' if proc.returncode == 0 and before == sha(p) else 'FAIL'
        return {'status': status, 'seconds': round(time.time()-t, 3), 'sha256': before,
                'exit_code': proc.returncode, 'olean_sha256': sha(obj) if status == 'PASS' else None}

    audit_results = {}

    def save(status):
        result_path.write_text(json.dumps({'status': status, 'elapsed_seconds': round(time.time()-started, 3),
            'jobs': args.jobs, 'cpu_ids': cpu_ids, 'lean_threads': 3, 'memory_limit_mib_per_process': memory_mib,
            'project_modules': len(files), 'modules': results, 'audits': audit_results}, indent=2)+'\n', encoding='utf-8')

    with ThreadPoolExecutor(max_workers=args.jobs) as pool:
        while pending or active:
            ready = sorted((m for m in pending if deps[m] <= done), key=lambda m: (m not in priority, m))
            for m in ready[:args.jobs-len(active)]:
                pending.remove(m)
                active[pool.submit(compile_one, m)] = m
            if not active:
                break
            completed, _ = wait(active, return_when=FIRST_COMPLETED)
            for future in completed:
                m = active.pop(future)
                r = future.result()
                results[m] = r
                (done if r['status'] == 'PASS' else failed).add(m)
                print(f"{r['status']} {len(done)}/{len(files)} {m} ({r['seconds']}s)", flush=True)
            save('RUNNING')
    for m in pending:
        results[m] = {'status': 'BLOCKED', 'imports_not_built': sorted(deps[m]-done)}
    if failed or pending:
        save('FAIL')
        raise SystemExit(1)
    if args.compile_only:
        save('COMPILED')
        print('MODULE_COMPILATION_ONLY: both axiom audits are still required', flush=True)
        return
    # A fully cached resume must invalidate the old PASS before replacing logs.
    save('RUNNING')
    # Both read the completed, frozen object cache and write separate logs.
    # Two audit workers share the same CPU affinity and three-thread limit.
    def run_audit(source, log_name):
        t = time.monotonic()
        with (evidence/log_name).open('w', encoding='utf-8') as log:
            proc = subprocess.run(['lean', f'-M{memory_mib}', 'verification/'+source],
                                  cwd=ROOT, env=env, stdout=log, stderr=subprocess.STDOUT)
        return {'exit_code': proc.returncode, 'seconds': round(time.monotonic()-t, 3)}

    with ThreadPoolExecutor(max_workers=min(2, args.jobs)) as pool:
        jobs = [(name, pool.submit(run_audit, source, log_name)) for name, source, log_name in
                [('selected_roots', 'Audit.lean', 'axioms.log'),
                 ('full_library', 'FullAudit.lean', 'full-axioms.log')]]
        audit_results.update((name, future.result()) for name, future in jobs)
    audit_code = audit_results['selected_roots']['exit_code']
    full_code = audit_results['full_library']['exit_code']
    save('PASS' if audit_code == 0 and full_code == 0 else 'AXIOM_AUDIT_FAIL')
    print('AXIOM_AUDIT', audit_code, flush=True)
    print('FULL_AXIOM_AUDIT', full_code, flush=True)
    raise SystemExit(audit_code or full_code)


if __name__ == '__main__':
    main()

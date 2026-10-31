"""Check source closure, current build hashes, audit evidence and source manifest."""
from pathlib import Path
import argparse
import hashlib
import json
import re
from external_policy import external_entries, external_dependencies
from lean_source import check_source

BASE = Path(__file__).resolve().parents[1]


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--update-manifest', action='store_true')
    ap.add_argument('--no-report', action='store_true')
    ap.add_argument('--evidence-dir', type=Path,
                    help='Read a new build and axiom audit instead of the archived reports')
    args = ap.parse_args()
    evidence = args.evidence_dir.resolve() if args.evidence_dir else BASE/'verification'
    files = {'.'.join(p.relative_to(BASE).with_suffix('').parts): p
             for d in ('Paper', 'GraphTheory') for p in (BASE/d).rglob('*.lean')}
    files['Paper'] = BASE/'Paper.lean'
    seen = set()
    def visit(name):
        if name in seen:
            return
        seen.add(name)
        text = files[name].read_text(encoding='utf-8-sig')
        assert not re.search(r'^import\s+(?:Scratch|MdsLean)\.', text, re.M), name
        for dep in re.findall(r'^import\s+([\w.]+)', text, re.M):
            if dep.startswith(('Paper', 'GraphTheory', 'Scratch.', 'MdsLean.')):
                assert dep in files, (name, dep)
                visit(dep)
    visit('Paper')
    assert seen == set(files), ('unreachable sources', sorted(set(files)-seen))
    build = json.loads((evidence/'build-result.json').read_text())
    assert build['status'] == 'PASS', build['status']
    assert set(build['modules']) == set(files), 'Build source set differs'
    comment_edits = json.loads((BASE/'verification/comment-edits.json').read_text())['files']
    for name, path in files.items():
        record = build['modules'][name]
        check_source(record, path, comment_edits.get(path.relative_to(BASE).as_posix()),
                     archived=not args.evidence_dir)
    roots = set(json.loads((BASE/'verification/roots.json').read_text()))
    audit = [json.loads(line.removeprefix('AUDIT '))
             for line in (evidence/'axioms.log').read_text().splitlines()
             if line.startswith('AUDIT ')]
    assert {r['name'] for r in audit} == roots, 'Endpoint audit differs from roots'
    external_entries()
    external_roots = {r['name']: external_dependencies(r) for r in audit
                      if external_dependencies(r)}
    full = [json.loads(line.removeprefix('FULL_AUDIT '))
            for line in (evidence/'full-axioms.log').read_text().splitlines()
            if line.startswith('FULL_AUDIT ')]
    assert len(full) == 1 and 'sorryAx' not in full[0]['transitive_axioms']
    sources = [*files.values(), BASE/'verification/Audit.lean', BASE/'verification/FullAudit.lean']
    # Preserve case-sensitive component ordering on Windows as well as POSIX.
    sources = sorted(set(sources + [BASE/'verification/external-results.json',
                                  BASE/'verification/external_policy.py', BASE/'verification/roots.json',
                                  BASE/'verification/lean_source.py', BASE/'verification/comment-edits.json']),
                     key=lambda path: path.relative_to(BASE).parts)
    manifest = ''.join(sha(p)+'  '+p.relative_to(BASE).as_posix()+'\n' for p in sources)
    target = BASE/'MANIFEST_SHA256.txt'
    if args.update_manifest:
        target.write_text(manifest, encoding='utf-8', newline='\n')
    assert target.read_text(encoding='utf-8') == manifest, 'Source manifest mismatch'
    report = {'status': 'PASS', 'compiled_modules': len(files), 'endpoint_roots': len(roots),
              'all_declaration_audit': full[0], 'source_manifest_sha256': sha(target),
              'external_roots': external_roots,
              'core_only_roots': len(roots) - len(external_roots)}
    if not args.no_report:
        (evidence/'package-check.json').write_text(json.dumps(report, indent=2)+'\n', encoding='utf-8')
    print(json.dumps(report))


if __name__ == '__main__':
    main()

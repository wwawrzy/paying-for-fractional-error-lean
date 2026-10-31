"""Check the paper result index against Lean sources and axiom evidence."""
import hashlib
import argparse
import json
from pathlib import Path
import re
import subprocess
import sys

BASE = Path(__file__).resolve().parents[1]
CORE = {'propext', 'Classical.choice', 'Quot.sound'}


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def require(condition, message):
    if not condition:
        raise ValueError(message)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--evidence-dir', type=Path,
                        help='Check new compilation/axiom evidence instead of the archived reports')
    args = parser.parse_args()
    evidence = args.evidence_dir.resolve() if args.evidence_dir else BASE/'verification'
    data = json.loads((BASE / 'verification/statement-map.json').read_text(encoding='utf8'))
    rows = data['items']
    require(len(rows) == data['total_statements'] == 81, 'Statement count differs')
    require(len({r['inventory_id'] for r in rows}) == 81, 'Duplicate result labels')
    index = (BASE / 'PaperIndex.lean').read_text(encoding='utf8')
    for row in rows:
        require('Paper label: ' + row['inventory_id'] + ';' in index, 'Missing result in index')
        for ref in row['lean']:
            require('#check ' + ref['declaration'] in index, 'Missing declaration in index')
    audit = {r['name']: r['axioms'] for line in (evidence / 'axioms.log').read_text().splitlines()
             if line.startswith('AUDIT ') for r in [json.loads(line[6:])]}
    supplemental = data['supplemental']
    require(sha(BASE / supplemental['file']) == supplemental['source_sha256'], 'Adapter source changed')
    require(sha(BASE / supplemental['axiom_log']) == supplemental['axiom_log_sha256'], 'Adapter axiom evidence changed')
    require(hashlib.sha256((BASE / supplemental['file']).read_text(encoding='utf8').encode()).hexdigest() == supplemental['audited_lean_body_sha256'], 'Adapter proof body changed')
    adapter_log = (evidence / 'proposition2-planar-axioms.txt').read_text()
    additional = 0
    for row in rows:
        external = set()
        require(bool(row['lean']), 'Missing formal declarations')
        for ref in row['lean']:
            require(sha(BASE / ref['file']) == ref['source_sha256'], 'Formal source changed: ' + ref['file'])
            name = ref['declaration']
            if ref['file'] == supplemental['file']:
                match = re.search(re.escape(name) + r"' depends on axioms: \[([^]]*)\]", adapter_log)
                require(match is not None, 'Missing adapter audit: ' + name)
                axioms = {s.strip() for s in match[1].split(',') if s.strip()}
                require(axioms <= CORE, 'Unexpected adapter axiom')
            else:
                require(name in audit, 'Missing audited declaration: ' + name)
                axioms = set(audit[name])
            external.update(axioms - CORE)
        require(external == set(row['external_axioms']), 'Axiom dependencies differ: ' + row['inventory_id'])
        additional += bool(external)
    require(additional == data['external_dependent_statements'] == 8, 'External statement count differs')
    require(len(rows) - additional == data['core_only_statements'] == 73, 'Core statement count differs')
    command = [sys.executable, str(BASE / 'verification/check_package.py'), '--no-report']
    if args.evidence_dir:
        command.extend(['--evidence-dir', str(evidence)])
    result = subprocess.run(command, capture_output=True, text=True)
    require(result.returncode == 0, result.stdout + result.stderr)
    package = json.loads(result.stdout)
    print(json.dumps({'status': 'PASS', 'statements': len(rows), 'core_only': 73,
                      'external_dependent': additional, 'compiled_library_modules': package['compiled_modules'],
                      'evidence': str(evidence.relative_to(BASE)) if evidence.is_relative_to(BASE) else str(evidence),
                      'mode': 'new_build_evidence' if args.evidence_dir else 'archived_evidence'}, indent=2))


if __name__ == '__main__':
    main()

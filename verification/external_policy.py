"""Exact external mathematical assumptions and their permitted roots."""
import hashlib
import json
from pathlib import Path

BASE = Path(__file__).resolve().parents[1]
CORE = {'propext', 'Classical.choice', 'Quot.sound'}


def external_entries():
    entries = json.loads((BASE/'verification/external-results.json').read_text())['entries']
    assert len({e['name'] for e in entries}) == len(entries)
    for entry in entries:
        for field in ('source',):
            path = BASE/entry[field]
            assert hashlib.sha256(path.read_bytes()).hexdigest() == entry[field+'_sha256'], (
                'External result source changed', entry['name'], field)
        for definition in entry.get('definition_sources', []):
            assert hashlib.sha256((BASE/definition['file']).read_bytes()).hexdigest() == definition['sha256'], (
                'External result definitions changed', definition['file'])
    return entries


def external_dependencies(record):
    """Reject undeclared assumptions and use outside the declared root scope."""
    external = set(record['axioms']) - CORE
    allowed = {e['name'] for e in external_entries() if record['name'] in e['allowed_roots']}
    assert external <= allowed, ('Unaccepted endpoint axiom', record['name'], external - allowed)
    return sorted(external)

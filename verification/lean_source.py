"""Fingerprint Lean source while ignoring comments, preserving all other text."""
import hashlib
import re


def comment_spans(text):
    """Locate nested block comments and line comments outside string/char literals."""
    i = 0
    while i < len(text):
        if text.startswith('--', i):
            end = text.find('\n', i)
            end = len(text) if end < 0 else end
            yield i, end
            i = end
        elif text.startswith('/-', i):
            start, depth = i, 1
            i += 2
            while depth and i < len(text):
                if text.startswith('/-', i):
                    depth += 1
                    i += 2
                elif text.startswith('-/', i):
                    depth -= 1
                    i += 2
                else:
                    i += 1
            if depth:
                raise ValueError('Unclosed Lean comment')
            yield start, i
        elif text[i] == '"':
            i += 1
            while i < len(text):
                if text[i] == '\\':
                    i += 2
                elif text[i] == '"':
                    i += 1
                    break
                else:
                    i += 1
        elif text[i] == "'" and (match := re.match(r"'(?:\\.|[^'\\\n])'", text[i:])):
            i += len(match[0])
        else:
            i += 1


def code_sha256(text):
    parts, end = [], 0
    for start, stop in comment_spans(text):
        parts.append(text[end:start])
        end = stop
    parts.append(text[end:])
    return hashlib.sha256(''.join(parts).encode('utf-8')).hexdigest()


def check_source(record, path, edit=None, *, archived=False):
    """Require exact build inputs, or recorded comment-only edits for old evidence."""
    current = hashlib.sha256(path.read_bytes()).hexdigest()
    assert record['status'] == 'PASS', path
    if record['sha256'] == current:
        return
    assert archived and edit is not None, ('Build source differs', path)
    assert record['sha256'] == edit['compiled_source_sha256'], path
    assert current == edit['current_source_sha256'], path
    assert code_sha256(path.read_text(encoding='utf-8')) == edit['code_sha256'], path

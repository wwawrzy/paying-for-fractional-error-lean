"""Comment cleanup must not conceal changes to executable Lean source."""
import hashlib
from pathlib import Path
import sys
import tempfile
import unittest

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / 'verification'))
from lean_source import code_sha256, check_source


def sha(text):
    return hashlib.sha256(text.encode()).hexdigest()


class SourceIntegrityTests(unittest.TestCase):
    def test_nested_comments_and_literals(self):
        before = 'def s := "-- /- literal -/" /- outer /- inner -/ -/\n-- old\ndef c := \'"\'\n'
        after = 'def s := "-- /- literal -/" /- replacement -/\n-- new\ndef c := \'"\'\n'
        self.assertEqual(code_sha256(before), code_sha256(after))
        self.assertNotEqual(code_sha256(before), code_sha256(after.replace('literal', 'changed')))

    def test_unterminated_comment_rejected(self):
        with self.assertRaises(ValueError):
            code_sha256('def n := 1 /- unfinished')

    def test_archive_exception_cannot_accept_code_edit_or_new_build(self):
        before = '-- old\ndef n := 1\n'
        after = '-- new\ndef n := 1\n'
        record = {'status': 'PASS', 'sha256': sha(before)}
        edit = {'compiled_source_sha256': sha(before),
                'current_source_sha256': sha(after), 'code_sha256': code_sha256(before)}
        with tempfile.TemporaryDirectory() as directory:
            path = Path(directory) / 'Example.lean'
            path.write_bytes(after.encode())
            check_source(record, path, edit, archived=True)
            with self.assertRaises(AssertionError):
                check_source(record, path, edit, archived=False)
            tampered = after.replace(':= 1', ':= 2')
            path.write_bytes(tampered.encode())
            edit['current_source_sha256'] = sha(tampered)
            with self.assertRaises(AssertionError):
                check_source(record, path, edit, archived=True)


if __name__ == '__main__':
    unittest.main()

"""Check that verification failures cannot be reported as successful builds."""
import contextlib
import io
import os
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest
from unittest.mock import patch

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
import verify


class VerificationTests(unittest.TestCase):
    def test_failed_logged_command_propagates(self):
        with tempfile.TemporaryDirectory() as directory:
            log = Path(directory) / 'failure.log'
            with contextlib.redirect_stdout(io.StringIO()), contextlib.redirect_stderr(io.StringIO()):
                with self.assertRaises(subprocess.CalledProcessError) as error:
                    verify.run([sys.executable, '-c', 'print("bad proof"); raise SystemExit(7)'],
                               os.environ.copy(), log)
            self.assertEqual(error.exception.returncode, 7)
            self.assertIn('bad proof', log.read_text())

    def test_archive_mode_is_explicit_and_does_not_start_build(self):
        output = io.StringIO()
        with patch.object(sys, 'argv', ['verify.py', '--recorded-only']), \
             patch.object(verify, 'run') as run, contextlib.redirect_stdout(output):
            verify.main()
        self.assertEqual(run.call_count, 1)
        self.assertIn('check_correspondence.py', run.call_args.args[0][1])
        self.assertIn('Lean was NOT run', output.getvalue())

    def test_failed_build_invalidates_previous_pass(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            status = root / '.lake/verification/verification-result.json'
            status.parent.mkdir(parents=True)
            status.write_text('{"status":"PASS"}')
            with patch.object(verify, 'ROOT', root), \
                 patch.object(sys, 'argv', ['verify.py']), \
                 patch.object(verify.shutil, 'which', return_value='tool'), \
                 patch.object(verify, 'run', side_effect=subprocess.CalledProcessError(1, ['lake'])):
                with self.assertRaises(subprocess.CalledProcessError):
                    verify.main()
            self.assertEqual(verify.json.loads(status.read_text())['status'], 'FAIL')


if __name__ == '__main__':
    unittest.main()

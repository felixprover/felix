#!/usr/bin/env python3
"""Exercise live diagnostic events and owned child settlement with real processes."""

import json
import os
from pathlib import Path
import select
import subprocess
import sys
import tempfile
import unittest
from unittest.mock import patch

import diagnose_memory


FIXTURE = '''
from pathlib import Path
import signal, subprocess, sys, time
root = Path(sys.argv[1])
child = None
def expired(*_):
    raise TimeoutError('fixture watchdog expired')
signal.signal(signal.SIGALRM, expired)
signal.alarm(10)
try:
    child = subprocess.Popen([sys.executable, '-c', 'import sys; sys.stdin.read()'], stdin=subprocess.PIPE)
    print(child.pid, flush=True)
    if sys.argv[2] == 'normal':
        samples = root / 'memory.samples.jsonl'
        while not samples.exists() or not samples.stat().st_size:
            time.sleep(0.005)
    else:
        sys.stdin.read()
except KeyboardInterrupt:
    (root / 'interrupted').write_text('yes')
finally:
    if child is not None:
        child.terminate()
        child.wait()
    (root / 'settled').write_text('yes')
'''


class MemoryTests(unittest.TestCase):
    def exercise(self, normal=False, bad_sampler=False):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            fixture = root / 'fixture.py'
            fixture.write_text(FIXTURE)
            fake = root / 'bad-sampler.py'
            fake.write_text("print('invalid notification', flush=True)\n")
            with (root / 'fixture.stderr').open('w') as errors:
                verifier = subprocess.Popen(
                    [sys.executable, '-B', str(fixture), str(root), 'normal' if normal else 'wait'],
                    stdin=subprocess.PIPE, stdout=subprocess.PIPE, stderr=errors,
                    text=True, start_new_session=True)
                try:
                    self.assertTrue(select.select([verifier.stdout], [], [], 5)[0], 'fixture never became ready')
                    child = int(verifier.stdout.readline())
                    sampler = fake if bad_sampler else diagnose_memory.SAMPLER
                    with patch.object(diagnose_memory, 'SAMPLER', sampler):
                        result = diagnose_memory.observe(
                            verifier, root, 4 * 1024 * 1024 if normal else 1, 0.01)
                    self.assertTrue((root / 'settled').exists())
                    self.assertIsNotNone(verifier.poll())
                    with self.assertRaises(ProcessLookupError):
                        os.kill(child, 0)
                    if bad_sampler:
                        self.assertFalse(result['successful'])
                        self.assertIsNotNone(result['monitor_error'])
                        self.assertTrue((root / 'interrupted').exists())
                    else:
                        memory = json.loads((root / 'memory.json').read_text())
                        live = [json.loads(line) for line in (root / 'memory.samples.jsonl').read_text().splitlines()]
                        self.assertEqual(memory['samples'], live)
                        self.assertIn(str(child), live[0]['rss_kib_by_pid'])
                        self.assertEqual(not normal, result['limit_exceeded'])
                        self.assertEqual(normal, result['successful'])
                        self.assertEqual(not normal, (root / 'interrupted').exists())
                finally:
                    diagnose_memory.cancel_and_wait(verifier)
                    verifier.stdin.close()
                    verifier.stdout.close()

    def test_threshold_notification_cancels_and_settles_owned_children(self):
        self.exercise()

    def test_normal_completion_retains_live_samples_without_cancellation(self):
        self.exercise(normal=True)

    def test_monitor_failure_cancels_and_settles_the_verifier(self):
        self.exercise(bad_sampler=True)


if __name__ == '__main__':
    unittest.main()

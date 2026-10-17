#!/usr/bin/env python3
"""Exercise trial retention and store isolation with a controlled verifier."""

import hashlib
import json
import os
from pathlib import Path
import sqlite3
import subprocess
import tempfile
import unittest


ROOT = Path(__file__).resolve().parents[2]
FAKE = '''#!/usr/bin/env python3
from pathlib import Path
import sqlite3
import sys
args = sys.argv[1:]
store = args[args.index('--store') + 1]
n = next(a for a in args if a.startswith('-N'))[2:]
rts = next(a for a in args if a.startswith('-s') and not a.startswith('--'))[2:]
with sqlite3.connect(store) as db:
    db.execute('create table if not exists counter (value integer)')
    row = db.execute('select value from counter').fetchone()
    print('initial counter:', row[0] if row else 'absent')
    db.execute('delete from counter')
    db.execute('insert into counter values (99)')
Path(rts).write_text('TASKS: 1 (using -N' + n + ')\\n')
print('Direct source authorization summary: 0 source axioms, 0 explicit proof gaps.')
print('completed runs: ' + ('1' if n == '3' else '0'))
print('render hints: ' + str('--check-render-hints' in args))
sys.exit(7 if n == '1' else 0)
'''


class SweepTest(unittest.TestCase):
    def setUp(self):
        self.temporary = tempfile.TemporaryDirectory()
        self.addCleanup(self.temporary.cleanup)
        self.root = Path(self.temporary.name)
        self.binary = self.root / 'verifier'
        self.binary.write_text(FAKE)
        self.binary.chmod(0o755)
        self.source = self.root / 'source.json'
        self.source.write_text(json.dumps({'binary_sha256': hashlib.sha256(self.binary.read_bytes()).hexdigest()}))
        self.inputs = self.root / 'inputs.json'
        self.inputs.write_text('{}\n')
        self.environment = self.root / 'environment.json'
        self.environment.write_text('{}\n')
        self.snapshot = self.root / 'snapshot.sqlite'
        db = sqlite3.connect(self.snapshot)
        db.execute('create table counter (value integer)')
        db.execute('insert into counter values (42)')
        db.commit()
        db.close()

    def run_sweep(self, *extra):
        return subprocess.run(
            ['python3', 'benchmark/concurrency/run.py', '--binary', str(self.binary),
             '--source-manifest', str(self.source), '--input-manifest', str(self.inputs),
             '--environment-manifest', str(self.environment),
             '--store', str(self.root / 'trial.sqlite'), '--output', str(self.root / 'results'),
             *extra], cwd=ROOT, capture_output=True, text=True,
            env={**os.environ, 'FELIX_TIME_STYLE': 'portable'})

    def records(self):
        return [json.loads(p.read_text()) for p in sorted((self.root / 'results').glob('*.json'))]

    def test_failed_trial_is_retained_and_later_trial_runs(self):
        result = self.run_sweep('--configuration', '1:2:2', '--configuration', '2:2:2')
        self.assertEqual(1, result.returncode, result.stderr)
        records = self.records()
        self.assertEqual([7, 0], [r['exit_status'] for r in records])
        self.assertEqual([False, True], [r['valid_trial'] for r in records])
        self.assertEqual([1, 2], [r['effective_capabilities'] for r in records])
        self.assertTrue(all(r['command'][1] == 'library/everything.tex' for r in records))
        self.assertTrue(all(not r['check_render_hints'] for r in records))

    def test_render_hint_validation_reaches_the_verifier_and_is_recorded(self):
        result = self.run_sweep('--check-render-hints', '--configuration', '2:2:2')
        self.assertEqual(0, result.returncode, result.stderr)
        record, = self.records()
        self.assertTrue(record['check_render_hints'])
        self.assertIn('--check-render-hints', record['command'])
        log, = (self.root / 'results').glob('*.run.txt')
        self.assertIn('render hints: True', log.read_text())

    def test_incremental_trials_restore_snapshot_even_after_failure(self):
        before = self.snapshot.read_bytes()
        result = self.run_sweep('--mode', 'incremental', '--store-snapshot', str(self.snapshot),
                                '--configuration', '1:2:2', '--configuration', '2:2:2')
        self.assertEqual(1, result.returncode, result.stderr)
        logs = sorted((self.root / 'results').glob('*.run.txt'))
        self.assertEqual(2, len(logs))
        for log in logs:
            self.assertIn('initial counter: 42', log.read_text())
        self.assertEqual(before, self.snapshot.read_bytes())
        self.assertTrue(all('--refresh' not in r['command'] for r in self.records()))

    def test_warm_atp_work_invalidates_an_otherwise_successful_trial(self):
        result = self.run_sweep('--mode', 'warm', '--store-snapshot', str(self.snapshot),
                                '--configuration', '3:2:2')
        self.assertEqual(1, result.returncode, result.stderr)
        record, = self.records()
        self.assertEqual(0, record['exit_status'])
        self.assertFalse(record['valid_trial'])
        self.assertIn('unchanged warm trial executed ATP work', record['problems'])


if __name__ == '__main__':
    unittest.main()

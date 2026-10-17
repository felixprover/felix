"""Failure retention, output boundary, and fixed repetition protocol checks."""
import copy
import gzip
import json
from pathlib import Path
import sys
import tempfile
import time
import unittest

import cli


class CliTests(unittest.TestCase):
    def setUp(self):
        self.workload = {'name': 'cold', 'kind': 'primary', 'command': ['--parseonly', 'root.tex'],
                         'stdout': '', 'stderr_pattern': ''}
        self.exe = {'path': '/pinned/felix', 'sha256': 'fixed'}
        self.spec = {'mode': 'calibration', 'workloads': [self.workload],
                     'executables': {label: self.exe for label in cli.LABELS}}
        self.record = {'workload': 'cold', 'pair': 0, 'label': 'reference', 'executable': self.exe,
                       'command': self.workload['command'], 'status': 'ok', 'returncode': 0,
                       'stdout': '', 'stderr': '', 'process_elapsed_ns': 1000000000,
                       'time_text': '  400 maximum resident set size\n',
                       'rts_text': 'program arguments\n [("bytes allocated", "1000"),'
                                   '("max_bytes_used", "300"),("mut_wall_seconds", ".6"),'
                                   '("GC_wall_seconds", ".3")]\n'}

    def records(self, pairs):
        records = [dict(self.record, pair=pair, label=label) for pair in range(pairs)
                   for label in (cli.LABELS if pair % 2 == 0 else cli.LABELS[::-1])]
        return records

    def test_cli_boundary(self):
        self.assertEqual(cli.metrics(self.record, self.workload)['elapsed_seconds'], 1)
        record = dict(self.record, stdout='corpus\t0\t123\t456\n')
        with self.assertRaises(ValueError):
            cli.metrics(record, self.workload)

    def test_archived_samples_replay(self):
        with tempfile.TemporaryDirectory() as directory:
            output = Path(directory)
            raw = '\n'.join(json.dumps(r) for r in self.records(7)) + '\n'
            (output / 'samples.jsonl').write_text(raw)
            self.assertEqual(cli.read_records(output), self.records(7))
            (output / 'samples.jsonl').unlink()
            (output / 'samples.jsonl.gz').write_bytes(gzip.compress(raw.encode()))
            self.assertEqual(cli.read_records(output), self.records(7))

    def test_timeout_stops_descendants(self):
        with tempfile.TemporaryDirectory() as directory:
            marker = Path(directory) / 'child-finished'
            child = 'import time; from pathlib import Path; time.sleep(.5); Path(' + repr(str(marker)) + ').touch()'
            parent = 'import subprocess,sys,time; subprocess.Popen([sys.executable,"-c",' + repr(child) + ']); print("started",flush=True); time.sleep(3)'
            result = cli.execute(sys.executable, ['-c', parent], timeout=.2)
            self.assertEqual(result['status'], 'timeout')
            self.assertEqual(result['stdout'], 'started\n')
            time.sleep(.6)
            self.assertFalse(marker.exists())

    def test_failure_and_missing_metrics(self):
        for change in [dict(status='timeout'), dict(returncode=1), dict(stderr='Parsing failed'),
                       dict(time_text=''), dict(rts_text=''), dict(process_elapsed_ns=0)]:
            with self.subTest(change=change), self.assertRaises(ValueError):
                cli.metrics(dict(self.record, **change), self.workload)

    def test_pairs_are_complete_and_ordered(self):
        records = self.records(7)
        self.assertEqual(cli.summarize(self.spec, records, 7)['decision'], 'pass')
        for malformed in [records[:-1], records + [records[0]], records[::-1]]:
            with self.assertRaises(ValueError):
                cli.summarize(self.spec, malformed, 7)
        with self.assertRaises(ValueError):
            cli.summarize(self.spec, self.records(6), 6)

    def test_changed_command_and_binary(self):
        for field, value in [('command', []), ('executable', {'sha256': 'different'})]:
            records = copy.deepcopy(self.records(7))
            records[0][field] = value
            with self.assertRaises(ValueError):
                cli.summarize(self.spec, records, 7)

    def test_source_workspace_is_measured_and_checked(self):
        with tempfile.TemporaryDirectory() as directory:
            result = cli.execute(sys.executable, ['-c', 'from pathlib import Path; print(Path.cwd())'],
                                 cwd=directory)
            self.assertEqual(Path(result['stdout'].strip()), Path(directory).resolve())
        directories = dict(reference='/pinned/original', candidate='/pinned/migrated')
        self.workload['working_directories'] = directories
        records = [dict(r, cwd=directories[r['label']]) for r in self.records(7)]
        self.assertEqual(cli.summarize(self.spec, records, 7)['decision'], 'pass')
        records[0]['cwd'] = directories['candidate']
        with self.assertRaises(ValueError):
            cli.summarize(self.spec, records, 7)
        self.workload['working_directories'] = dict(reference='relative')
        with self.assertRaises(ValueError):
            cli.working_directory(self.workload, 'reference')

    def test_gate_boundaries(self):
        decide = cli.timing_decision
        self.assertEqual(decide([.90, 1.10], .90, 1.10), 'pass')
        self.assertEqual(decide([.89, 1.01], .90, 1.10), 'inconclusive')
        self.assertEqual(decide([1.11, 1.12], .90, 1.10), 'fail')
        self.assertEqual(decide([.89, .90], None, .90), 'pass')
        self.assertEqual(decide([.99, 1.00], None, 1., strict=True), 'inconclusive')
        self.assertEqual(decide([1.00, 1.01], None, 1., strict=True), 'fail')

    def test_warm_requires_zero_fresh_work(self):
        workload = dict(self.workload, kind='warm', installations=474, stderr_pattern=r'(?s).*Verification successful\.\n')
        report = ('module installations 474 0 0\nlive Vampire runs started: 0\n'
                  'verification completions: 0\nVerification successful.\n')
        cli.check_output(dict(self.record, stderr=report), workload)
        for old, new in [('474 0 0', '473 1 0'), ('started: 0', 'started: 1'), ('completions: 0', 'completions: 1')]:
            with self.assertRaises(ValueError):
                cli.check_output(dict(self.record, stderr=report.replace(old, new)), workload)

    def test_readability_nonregression_preserves_primary_boundary(self):
        spec = dict(self.spec, mode='nonregression')
        records = copy.deepcopy(self.records(7))
        self.assertEqual(cli.summarize(spec, records, 7)['decision'], 'pass')
        for row in records:
            if row['label'] == 'candidate':
                row['process_elapsed_ns'] = 1110000000
        self.assertEqual(cli.summarize(spec, records, 7)['decision'], 'fail')
        for row in records:
            row['process_elapsed_ns'] = 1000000000
            if row['label'] == 'candidate':
                row['rts_text'] = row['rts_text'].replace('"1000"', '"1101"')
        result = cli.summarize(spec, records, 7)
        self.assertEqual(result['decision'], 'fail')
        self.assertFalse(result['extension_allowed'])

    def test_extension_cannot_hide_non_time_failure(self):
        spec = dict(self.spec, mode='incremental')
        records = self.records(7)
        # Exact ratio 1 touches the strict incremental time bound: failure,
        # never an invitation to collect more favorable observations.
        self.assertFalse(cli.summarize(spec, records, 7)['extension_allowed'])
        for r in records:
            if r['label'] == 'candidate':
                r['rts_text'] = r['rts_text'].replace('"1000"', '"2000"')
        result = cli.summarize(spec, records, 7)
        self.assertFalse(result['non_time_passed'])
        self.assertEqual(result['decision'], 'fail')


if __name__ == '__main__':
    unittest.main()

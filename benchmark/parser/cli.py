#!/usr/bin/env python3
"""Paired, whole-process Felix CLI measurements (macOS time -l).

The JSON specification pins executables, source/build provenance, inputs and
workloads. This deliberately does not consume parser-bench's corpus row. Run
`measure SPEC OUTPUT`, then at most one `extend OUTPUT` when screening allows it.
Correctness observations and builds run separately, before candidate trials.
"""
import argparse
import ast
import gzip
import json
import math
import os
from pathlib import Path
import platform
import re
import signal
import statistics
import subprocess
import sys
import time

sys.dont_write_bytecode = True
import run

LABELS = ['reference', 'candidate']
METRICS = ['elapsed_seconds', 'allocated_bytes', 'max_live_bytes',
           'max_rss_bytes', 'mutator_seconds', 'gc_seconds']


def write_json(path, value):
    path.write_text(json.dumps(value, indent=2) + '\n')


def read_records(output):
    path = output / 'samples.jsonl'
    if path.exists():
        raw = path.read_text()
    else:
        with gzip.open(output / 'samples.jsonl.gz', 'rt') as stream:
            raw = stream.read()
    return [json.loads(line) for line in raw.splitlines()]


def execute(executable, args, timeout=600, cwd=None):
    # time(1) has a child process. Bound the entire group, so a timed-out
    # measurement cannot leave Felix competing with subsequent work.
    started = time.monotonic_ns()
    with subprocess.Popen([executable, *args], stdout=subprocess.PIPE,
                          stderr=subprocess.PIPE, text=True, start_new_session=True,
                          cwd=cwd) as process:
        try:
            stdout, stderr = process.communicate(timeout=timeout)
        except subprocess.TimeoutExpired:
            os.killpg(process.pid, signal.SIGKILL)
            stdout, stderr = process.communicate()
            return {'status': 'timeout', 'timeout_seconds': timeout,
                    'stdout': stdout, 'stderr': stderr}
        except KeyboardInterrupt:
            os.killpg(process.pid, signal.SIGKILL)
            process.communicate()
            raise
        return {'status': 'ok' if process.returncode == 0 else 'failed',
                'returncode': process.returncode, 'stdout': stdout, 'stderr': stderr,
                'process_elapsed_ns': time.monotonic_ns() - started}


def check_identity(spec):
    for identity in spec['executables'].values():
        if run.identity(identity['path']) != identity:
            raise ValueError('executable changed')
    for path, sha in spec['inputs'].items():
        if run.digest(Path(path).read_bytes()) != sha:
            raise ValueError('input changed: ' + path)


def working_directory(workload, label):
    directories = workload.get('working_directories')
    if directories is None:
        return None
    if set(directories) != set(LABELS) or any(not Path(p).is_absolute() for p in directories.values()):
        raise ValueError('working directories must name both roles with absolute paths')
    return directories[label]


def check_output(record, workload, prime=False):
    if record['status'] != 'ok' or record['returncode'] != 0:
        raise ValueError('failed CLI process')
    if record['stdout'] != workload['stdout']:
        raise ValueError('unexpected stdout')
    if re.fullmatch(workload['stderr_pattern'], record['stderr']) is None:
        raise ValueError('unexpected stderr')
    if workload['kind'] == 'warm' and not prime:
        report = record['stderr']
        installations = re.search(r'module installations\s+(\d+)\s+(\d+)\s+(\d+)', report)
        if not installations or tuple(map(int, installations.groups())) != (workload['installations'], 0, 0):
            raise ValueError('store is not fully warm')
        if not re.search(r'^\s*live Vampire runs started: 0\s*$', report, re.M):
            raise ValueError('live prover work')
        if not re.search(r'^\s*verification completions:\s+0\s*$', report, re.M):
            raise ValueError('fresh source verification')


def metrics(record, workload):
    check_output(record, workload)
    rts = record['rts_text']
    # GHC writes a command header followed by its machine-readable association list.
    rts = dict(ast.literal_eval(rts[rts.index(' [(') + 1:]))
    rss = re.search(r'^\s*(\d+)\s+maximum resident set size\s*$', record['time_text'], re.M)
    if rss is None:
        raise ValueError('missing OS maximum RSS')
    values = dict(zip(METRICS, [record['process_elapsed_ns'] / 1e9,
        int(rts['bytes allocated']), int(rts['max_bytes_used']), int(rss[1]),
        float(rts['mut_wall_seconds']), float(rts['GC_wall_seconds'])]))
    if any(not math.isfinite(v) or v <= 0 for v in values.values()):
        raise ValueError('missing or nonpositive metric')
    return values


def timing_decision(interval, lower, upper, strict=False):
    lo, hi = interval
    if (lower is None or lo >= lower) and (hi < upper if strict else hi <= upper):
        return 'pass'
    if lo > upper or (strict and lo >= upper) or (lower is not None and hi < lower):
        return 'fail'
    return 'inconclusive'


def summarize(spec, records, pairs):
    if pairs not in [7, 21]:
        raise ValueError('comparison requires seven or twenty-one complete pairs')
    expected_order = [(w['name'], rep, label) for w in spec['workloads']
                      for rep in range(pairs)
                      for label in (LABELS if rep % 2 == 0 else LABELS[::-1])]
    # An extension appends all workloads' extra pairs to the initial seven.
    if pairs == 21:
        expected_order = [k for k in expected_order if k[1] < 7] + [k for k in expected_order if k[1] >= 7]
    if [(r['workload'], r['pair'], r['label']) for r in records] != expected_order:
        raise ValueError('duplicate, incomplete, or out-of-order comparison')
    samples = {}
    for record in records:
        workload = next(w for w in spec['workloads'] if w['name'] == record['workload'])
        if record['command'] != workload['command'] or record['executable'] != spec['executables'][record['label']]:
            raise ValueError('sample identity mismatch')
        if record.get('cwd') != working_directory(workload, record['label']):
            raise ValueError('sample working directory mismatch')
        samples[record['workload'], record['pair'], record['label']] = metrics(record, workload)
    summaries = {}
    decisions = []
    non_time_passed = True
    for w in spec['workloads']:
        rows = {}
        for metric in METRICS:
            ref, cand = [[samples[w['name'], rep, label][metric] for rep in range(pairs)] for label in LABELS]
            a, b = map(statistics.median, [ref, cand])
            rows[metric] = {'reference_median': a, 'candidate_median': b,
                            'ratio': b / a, 'paired_bootstrap_95': run.bootstrap_interval(ref, cand),
                            'reference_range': [min(ref), max(ref)], 'candidate_range': [min(cand), max(cand)]}
        mode = spec['mode']
        if mode == 'calibration':
            decision = timing_decision(rows['elapsed_seconds']['paired_bootstrap_95'], .90, 1.10)
        elif w['kind'] == 'warm':
            decision = 'secondary-review'
        else:
            nonregression = mode == 'nonregression' or w['kind'] == 'growth'
            upper = 1.10 if nonregression else (.90 if mode == 'final' else 1.0)
            decision = timing_decision(rows['elapsed_seconds']['paired_bootstrap_95'], None, upper,
                                       strict=w['kind'] == 'primary' and mode == 'incremental')
            allocation_limit = 1.10 if nonregression else (.90 if mode == 'final' else 1.01)
            non_time_passed &= (rows['allocated_bytes']['ratio'] <= allocation_limit
                                and rows['max_live_bytes']['ratio'] <= 1.10
                                and rows['max_rss_bytes']['ratio'] <= 1.10)
        decisions.append(decision)
        summaries[w['name']] = {'metrics': rows, 'timing': decision}
    if not non_time_passed or 'fail' in decisions:
        decision = 'fail'
    elif 'inconclusive' in decisions:
        decision = 'inconclusive'
    else:
        decision = 'pass'
    return {'pairs': pairs, 'workloads': summaries, 'non_time_passed': non_time_passed,
            'decision': decision, 'extension_allowed': pairs == 7 and decision == 'inconclusive',
            'scope': 'Timing screen; semantic checks and warm disposition remain separate.'}


def measure(spec, output, start, end):
    check_identity(spec)
    with (output / 'samples.jsonl').open('a') as stream:
        for w in spec['workloads']:
            for pair in range(start, end):
                for label in (LABELS if pair % 2 == 0 else LABELS[::-1]):
                    check_identity(spec)
                    stem = output / f'{w["name"]}-{pair}-{label}'
                    exe = spec['executables'][label]
                    args = ['-l', '-o', str(stem) + '.time', exe['path'], *w['command'],
                            '+RTS', '-T', '-t' + str(stem) + '.rts', '--machine-readable', '-RTS']
                    cwd = working_directory(w, label)
                    result = execute('/usr/bin/time', args, cwd=cwd)
                    record = {'workload': w['name'], 'pair': pair, 'label': label,
                              'command': w['command'], 'cwd': cwd, 'executable': exe, **result}
                    for key, suffix in [('rts_text', '.rts'), ('time_text', '.time')]:
                        path = Path(str(stem) + suffix)
                        record[key] = path.read_text() if path.exists() else ''
                    stream.write(json.dumps(record) + '\n')
                    stream.flush()  # Retain a failed/missing-metric sample before rejecting it.
                    values = metrics(record, w)
                    print(w['name'], pair, label, round(values['elapsed_seconds'], 3), flush=True)
    check_identity(spec)


def main():
    p = argparse.ArgumentParser(description=__doc__)
    sub = p.add_subparsers(dest='action', required=True)
    m = sub.add_parser('measure')
    m.add_argument('spec', type=Path)
    m.add_argument('output', type=Path)
    for action in ['extend', 'summary']:
        sub.add_parser(action).add_argument('output', type=Path)
    args = p.parse_args()
    output = args.output.resolve()
    if args.action == 'measure':
        spec = json.loads(args.spec.read_text())
        if spec['mode'] not in ['calibration', 'incremental', 'final', 'nonregression']:
            raise ValueError('unknown gate mode')
        if spec['mode'] == 'calibration' and spec['executables']['reference'] != spec['executables']['candidate']:
            raise ValueError('calibration requires the same pinned executable in both slots')
        if spec['mode'] != 'calibration' and not spec['correctness_checked']:
            raise ValueError('candidate correctness must be checked first')
        names = [w['name'] for w in spec['workloads']]
        if len(names) != len(set(names)) or not names:
            raise ValueError('duplicate or absent workloads')
        output.mkdir(parents=True, exist_ok=False)
        spec.update(schema='felix-cli-v1', cwd=str(Path.cwd()), platform=platform.platform(),
                    cpu_count=os.cpu_count(), driver_sha256=run.digest(Path(__file__).read_bytes()),
                    environment={k: os.environ.get(k) for k in ['GHCRTS', 'NAPROCHE_LIB', 'FELIX_VAMPIRE']},
                    schedule='fresh processes, alternating AB/BA; append 14 after eligible seven-pair screen',
                    timeout_seconds=600, filesystem_cache='uncontrolled; no flushing')
        write_json(output / 'metadata.json', spec)
        check_identity(spec)
        for w in spec['workloads']:
            if w['kind'] == 'warm':
                for label in LABELS:
                    result = execute(spec['executables'][label]['path'], w['command'],
                                     cwd=working_directory(w, label))
                    write_json(output / f'prime-{label}.json', result)
                    check_output(result, w, prime=True)
        measure(spec, output, 0, 7)
    else:
        spec = json.loads((output / 'metadata.json').read_text())
    records = read_records(output)
    pairs = len(records) // (2 * len(spec['workloads']))
    result = summarize(spec, records, pairs)
    if args.action == 'extend':
        if not result['extension_allowed']:
            raise ValueError('screen does not allow extension')
        if not (output / 'samples.jsonl').exists():
            raise ValueError('extend the working comparison, not a compressed archive')
        if str(Path.cwd()) != spec['cwd'] or any(os.environ.get(k) != v for k, v in spec['environment'].items()):
            raise ValueError('measurement environment changed')
        if run.digest(Path(__file__).read_bytes()) != spec['driver_sha256']:
            raise ValueError('measurement driver changed')
        write_json(output / 'screen-seven.json', result)
        measure(spec, output, 7, 21)
        records = read_records(output)
        result = summarize(spec, records, 21)
    write_json(output / 'summary.json', result)
    print(json.dumps(result, indent=2))


if __name__ == '__main__':
    main()

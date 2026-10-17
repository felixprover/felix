#!/usr/bin/env python3
"""Run one owned verifier with live RSS diagnostics and cooperative cancellation.

The command must launch the verifier directly, without make/Stack/time wrappers.
These sampled runs do not qualify ordinary elapsed-time improvements.
"""

import argparse
import json
from pathlib import Path
import signal
import subprocess
import sys
import time


SAMPLER = Path(__file__).with_name('sample_memory.py')


def cancel_and_wait(process):
    """Retain ownership until the process's normal interrupt cleanup ends."""
    interrupted = False
    while process.poll() is None:
        try:
            if not interrupted:
                process.send_signal(signal.SIGINT)
                interrupted = True
            process.wait()
        except KeyboardInterrupt:
            # A second interrupt must not abandon a checker still settling work.
            continue
    return process.wait()


def observe(verifier, output, limit_kib, interval):
    """Observe and settle an already-owned direct verifier, including on errors."""
    monitor = None
    exceeded = False
    monitor_error = None
    try:
        with (output / 'monitor.stderr').open('x') as errors:
            monitor = subprocess.Popen(
                [sys.executable, '-B', str(SAMPLER), str(verifier.pid),
                 '--output', str(output / 'memory.json'), '--limit-kib', str(limit_kib),
                 '--interval', str(interval)],
                stdout=subprocess.PIPE, stderr=errors, text=True)
            for line in monitor.stdout:
                event = json.loads(line)
                if (not isinstance(event, dict)
                        or event.get('event') != 'rss-limit-exceeded'
                        or event.get('root_pid') != verifier.pid
                        or event.get('limit_kib') != limit_kib
                        or event.get('tree_rss_kib', 0) <= limit_kib):
                    raise ValueError('invalid memory-threshold notification')
                exceeded = True
                cancel_and_wait(verifier)
            if monitor.wait():
                raise ValueError('memory sampler failed; see monitor.stderr')
            if verifier.poll() is None:
                raise ValueError('sampler ended before the verifier exited')
    except (OSError, ValueError) as error:
        monitor_error = str(error)
    finally:
        cancel_and_wait(verifier)
        if monitor is not None:
            # A failed/interrupted sampler cannot strand the owned verifier.
            # Live JSONL samples survive even when the summary is incomplete.
            cancel_and_wait(monitor)
            monitor.stdout.close()
    return {'verifier_exit_status': verifier.returncode,
            'monitor_exit_status': monitor.returncode if monitor is not None else None,
            'limit_exceeded': exceeded, 'monitor_error': monitor_error,
            'successful': verifier.returncode == 0 and not exceeded and monitor_error is None}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path, required=True)
    parser.add_argument('--limit-kib', type=int, required=True)
    parser.add_argument('--interval', type=float, default=0.25)
    parser.add_argument('command', nargs=argparse.REMAINDER)
    args = parser.parse_args()
    command = args.command[1:] if args.command[:1] == ['--'] else args.command
    if not command or args.limit_kib <= 0 or args.interval <= 0:
        parser.error('supply a direct verifier command and positive limit/interval')
    args.output.mkdir(parents=True, exist_ok=False)
    record = {'command': command, 'limit_kib': args.limit_kib,
              'interval_seconds': args.interval, 'started_unix_seconds': time.time(),
              'diagnostic_only': True}
    metadata = args.output / 'diagnostic.json'
    metadata.write_text(json.dumps(record, indent=2) + '\n')
    started = time.monotonic()
    with (args.output / 'verifier.log').open('x') as log:
        verifier = subprocess.Popen(command, stdout=log, stderr=subprocess.STDOUT,
                                    stdin=subprocess.DEVNULL, start_new_session=True)
        try:
            record.update(observe(verifier, args.output, args.limit_kib, args.interval))
        finally:
            record['verifier_exit_status'] = cancel_and_wait(verifier)
            record['elapsed_seconds'] = time.monotonic() - started
            metadata.write_text(json.dumps(record, indent=2) + '\n')
    print(json.dumps(record), flush=True)
    return 0 if record['successful'] else 1


if __name__ == '__main__':
    raise SystemExit(main())

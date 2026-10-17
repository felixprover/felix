#!/usr/bin/env python3
"""Sample simultaneous RSS for one running process and its descendants.

Use only in diagnostic trials. RSS can count shared pages more than once, and
periodic samples can miss short peaks. This is not a physical-memory census.
"""

import argparse
import json
from pathlib import Path
import subprocess
import time


def process_rows():
    output = subprocess.check_output(
        ['ps', '-axo', 'pid=,ppid=,rss=,stat=,comm='], text=True)
    rows = {}
    for line in output.splitlines():
        pid, parent, rss, state, executable = line.split(None, 4)
        # The controller reaps the verifier after this sampler exits. A zombie
        # is already finished; waiting for its PID to disappear would deadlock.
        if state.startswith('Z'):
            continue
        rows[int(pid)] = (int(parent), int(rss), executable)
    return rows


def tree_sample(rows, root):
    owned = {root}
    while True:
        expanded = owned | {pid for pid, (parent, _, _) in rows.items()
                            if parent in owned}
        if expanded == owned:
            break
        owned = expanded
    return {str(pid): rows[pid][1] for pid in sorted(owned)}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('pid', type=int)
    parser.add_argument('--output', type=Path, required=True)
    parser.add_argument('--interval', type=float, default=0.25)
    parser.add_argument('--limit-kib', type=int,
                        help='notify the owning controller on stdout when this RSS limit is exceeded')
    args = parser.parse_args()
    if args.interval <= 0:
        parser.error('interval must be positive')
    if args.limit_kib is not None and args.limit_kib <= 0:
        parser.error('limit must be positive')
    rows = process_rows()
    if args.pid not in rows:
        parser.error('root process is not running')
    executable = rows[args.pid][2]
    samples = []
    exceeded = False
    live_path = args.output.with_suffix('.samples.jsonl')
    with args.output.open('x') as output, live_path.open('x') as live:
        while args.pid in rows and rows[args.pid][2] == executable:
            rss = tree_sample(rows, args.pid)
            samples.append({'unix_seconds': time.time(), 'rss_kib_by_pid': rss,
                            'tree_rss_kib': sum(rss.values())})
            live.write(json.dumps(samples[-1]) + '\n')
            live.flush()
            if args.limit_kib is not None and sum(rss.values()) > args.limit_kib and not exceeded:
                exceeded = True
                print(json.dumps({'event': 'rss-limit-exceeded', 'root_pid': args.pid,
                                  'limit_kib': args.limit_kib,
                                  'tree_rss_kib': sum(rss.values())}), flush=True)
            time.sleep(args.interval)
            rows = process_rows()
        json.dump({'root_pid': args.pid, 'root_executable': executable,
                   'requested_interval_seconds': args.interval,
                   'limit_kib': args.limit_kib, 'limit_exceeded': exceeded,
                   'live_samples': str(live_path),
                   'sampled_maximum_tree_rss_kib': max(s['tree_rss_kib'] for s in samples),
                   'samples': samples}, output, indent=2)
        output.write('\n')


if __name__ == '__main__':
    main()

#!/usr/bin/env python3
"""Run an ordered full-library concurrency sweep with reproducible store states."""

import argparse
from contextlib import closing
import hashlib
import json
import os
from pathlib import Path
import re
import sqlite3
import subprocess
import time


def configuration(raw):
    try:
        values = tuple(int(value) for value in raw.split(':'))
    except ValueError as error:
        raise argparse.ArgumentTypeError('expected CAPABILITIES:MODULES:PROVERS') from error
    if len(values) != 3 or any(value < 1 for value in values):
        raise argparse.ArgumentTypeError('expected three positive counts: CAPABILITIES:MODULES:PROVERS')
    return values


def sha256(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def write_metadata(prefix, metadata):
    Path(f'{prefix}.json').write_text(json.dumps(metadata, indent=2) + '\n')


def restore_store(snapshot, destination):
    # SQLite backup gives each trial the same database without copying a live WAL.
    with closing(sqlite3.connect(snapshot.as_uri() + '?mode=ro', uri=True)) as source:
        with closing(sqlite3.connect(destination)) as target:
            source.backup(target)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--binary', type=Path, required=True)
    parser.add_argument('--source-manifest', type=Path, required=True)
    parser.add_argument('--input-manifest', type=Path, required=True)
    parser.add_argument('--environment-manifest', type=Path, required=True)
    parser.add_argument('--store', type=Path, required=True)
    parser.add_argument('--output', type=Path, required=True)
    parser.add_argument('--input', default='library/everything.tex')
    parser.add_argument('--check-render-hints', action='store_true',
                        help='include the render-hint validation used by make lib')
    parser.add_argument('--configuration', type=configuration, action='append', required=True)
    parser.add_argument('--rts-option', action='append', default=[],
                        help='additional RTS argument, e.g. --rts-option=-A32m; recorded in each trial')
    parser.add_argument('--mode', choices=['refresh', 'warm', 'incremental'], default='refresh')
    parser.add_argument('--store-snapshot', type=Path,
                        help='closed, populated SQLite database restored before every non-refresh trial')
    args = parser.parse_args()

    binary = args.binary.resolve(strict=True)
    binary_hash = sha256(binary)
    driver_hash = sha256(Path(__file__))
    source_manifest = json.loads(args.source_manifest.read_text())
    if source_manifest['binary_sha256'] != binary_hash:
        parser.error('binary does not match its source manifest')
    manifests = [args.source_manifest, args.input_manifest, args.environment_manifest]
    for manifest in manifests:
        if not manifest.is_file() or manifest.stat().st_size == 0:
            parser.error(f'missing or empty manifest: {manifest}')
    if (args.mode == 'refresh') != (args.store_snapshot is None):
        parser.error('warm/incremental modes require --store-snapshot; refresh does not use one')
    snapshot = args.store_snapshot.resolve(strict=True) if args.store_snapshot else None
    store = args.store.resolve()
    if snapshot == store:
        parser.error('trial store must differ from its immutable snapshot')
    if snapshot:
        wal = Path(f'{snapshot}-wal')
        if wal.exists() and wal.stat().st_size:
            parser.error('checkpoint and close the snapshot database before benchmarking')
    snapshot_hash = sha256(snapshot) if snapshot else None
    args.output.mkdir(parents=True, exist_ok=False)
    store.parent.mkdir(parents=True, exist_ok=True)
    manifest_records = {
        str(path.resolve()): sha256(path) for path in manifests
    }
    failed = False

    for ordinal, (capabilities, modules, provers) in enumerate(args.configuration, 1):
        prefix = args.output / f'{ordinal:02d}-N{capabilities}-M{modules}-P{provers}'
        command = [str(binary), args.input, '--store', str(store)]
        if args.mode == 'refresh':
            command.append('--refresh')
        if args.check_render_hints:
            command.append('--check-render-hints')
        rts_options = [f'-N{capabilities}', *args.rts_option]
        command += ['--module-jobs', str(modules), '--prover-jobs', str(provers),
                    '-t', '20', '--store-report', '+RTS', *rts_options,
                    f'-s{prefix}.rts', '-RTS']
        metadata = {
            'command': command, 'binary_sha256': binary_hash,
            'driver_sha256': driver_hash, 'manifests': manifest_records,
            'source_manifest': str(args.source_manifest),
            'input_manifest': str(args.input_manifest),
            'environment_manifest': str(args.environment_manifest),
            'vampire_cores': 2, 'requested_capabilities': capabilities,
            'module_limit': modules, 'prover_limit': provers,
            'additional_rts_options': args.rts_option,
            'cache_policy': args.mode, 'filesystem_cache': 'uncontrolled',
            'check_render_hints': args.check_render_hints,
            'load_average_before_trial': list(os.getloadavg()),
            'inherited_runtime_options': {name: os.environ.get(name)
                                          for name in ['GHCRTS', 'NAPROCHE_LIB', 'FELIX_VAMPIRE']},
            'store_snapshot': str(snapshot) if snapshot else None,
            'store_snapshot_sha256': snapshot_hash,
        }
        write_metadata(prefix, metadata)
        try:
            if snapshot:
                if sha256(snapshot) != snapshot_hash:
                    raise ValueError('store snapshot changed during the sweep')
                restore_store(snapshot, store)
            metadata['started_unix_seconds'] = time.time()
            write_metadata(prefix, metadata)
            started = time.monotonic()
            with Path(f'{prefix}.run.txt').open('w') as log:
                result = subprocess.run(
                    ['benchmark/run-timed.sh', 'resources', f'{prefix}.time', '--', *command],
                    stdout=log, stderr=subprocess.STDOUT, check=False)
            metadata['driver_elapsed_seconds'] = time.monotonic() - started
            metadata['exit_status'] = result.returncode
            Path(f'{prefix}.status').write_text(f'{result.returncode}\n')
            output = Path(f'{prefix}.run.txt').read_text()
            counts = re.search(r'Direct source authorization summary: (\d+) source axioms, (\d+) explicit proof gaps', output)
            completed = re.search(r'completed runs: (\d+)', output)
            rts_path = Path(f'{prefix}.rts')
            rts = rts_path.read_text() if rts_path.exists() else ''
            effective = re.search(r'using -N(\d+)', rts)
            if counts:
                metadata.update(source_axioms=int(counts[1]), proof_gaps=int(counts[2]))
            if completed:
                metadata['completed_runs'] = int(completed[1])
            if effective:
                metadata['effective_capabilities'] = int(effective[1])
            problems = []
            if result.returncode:
                problems.append(f'verification exited {result.returncode}')
            if counts is None or completed is None or effective is None:
                problems.append('missing authorization, execution, or effective-capability measurements')
            if effective and int(effective[1]) != capabilities:
                problems.append('effective capabilities differ from requested capabilities')
            if args.mode == 'warm' and completed and int(completed[1]) != 0:
                problems.append('unchanged warm trial executed ATP work')
            metadata['problems'] = problems
            metadata['valid_trial'] = not problems
        except (OSError, ValueError, sqlite3.Error) as error:
            # Keep operational failures distinct from a verifier exit status.
            metadata['valid_trial'] = False
            metadata['problems'] = [f'{type(error).__name__}: {error}']
        write_metadata(prefix, metadata)
        failed |= not metadata['valid_trial']
        print(f"{prefix.name}: {'valid' if metadata['valid_trial'] else 'FAILED'}; "
              f"completed={metadata.get('completed_runs', 'unknown')}; "
              f"problems={metadata['problems']}", flush=True)
    return 1 if failed else 0


if __name__ == '__main__':
    raise SystemExit(main())

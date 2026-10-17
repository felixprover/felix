#!/usr/bin/env python3
"""Parser-specific process isolation, observations, and interleaved trials.

No third-party Python dependencies. Run from the repository root. Executables
are copied/pinned by the caller; their SHA256, not a mutable path, is identity.
"""
import argparse
import ast
import gzip
import hashlib
import json
import os
from pathlib import Path
import platform
import random
import statistics
import subprocess
import time

ROOTS = ["library/topology/urysohn/chain.tex", "test/examples/formula.tex",
         "test/examples/relation-notation.tex"]
RTS = ["+RTS", "-T", "-t", "--machine-readable", "-RTS"]


def digest(data):
    return hashlib.sha256(data).hexdigest()


def identity(executable):
    return {"path": str(Path(executable).resolve()),
            "sha256": digest(Path(executable).read_bytes())}


def input_identity():
    paths = [Path("stack.yaml"), Path("stack.yaml.lock"), Path("package.yaml")]
    paths += sorted(Path("library").rglob("*.tex"))
    paths += sorted(Path("test/examples").glob("*.tex"))
    paths += sorted(Path("test/html-fixtures").rglob("*.tex"))
    paths += sorted(Path("benchmark/parser").glob("*.hs"))
    return {str(path): digest(path.read_bytes()) for path in paths}


def execute(executable, args, timeout=60, rts=False):
    started = time.monotonic_ns()
    try:
        result = subprocess.run([executable, *args, *(RTS if rts else [])],
                                capture_output=True, text=True, timeout=timeout)
        return {"status": "ok" if result.returncode == 0 else "failed",
                "returncode": result.returncode, "stdout": result.stdout,
                "stderr": result.stderr,
                "process_elapsed_ns": time.monotonic_ns() - started}
    except subprocess.TimeoutExpired as error:
        return {"status": "timeout", "timeout_seconds": timeout,
                "stdout": str(error.stdout or ""), "stderr": str(error.stderr or "")}


def cases(executable):
    result = execute(executable, ["cases"])
    if result["status"] != "ok":
        raise RuntimeError(result)
    return result["stdout"].splitlines()


def check(executable, output):
    output.mkdir(parents=True, exist_ok=True)
    records = []
    commands = [("controls", ["controls"])]
    commands += [(name, ["observe", name]) for name in cases(executable)]
    commands += [("html-" + name, ["observe-html", name]) for name in ["short", "noun-shared-128-1", "constant-disjoint-128-1"]]
    commands += [("corpus-" + Path(root).stem, ["manifest", root]) for root in ROOTS]
    with gzip.open(output / "observations.txt.gz", "wt") as archive:
        for name, command in commands:
            result = execute(executable, command, timeout=180)
            raw = result["stdout"]
            # Raw derivation multiplicity is recorded, but is not a semantic
            # equivalence requirement. Selected failure remains in the oracle.
            semantic = "\n".join(line for line in raw.splitlines()
                                 if not line.startswith(('("counts",', '("concrete-failures-in-order",')))
            record = {"case": name, "command": command,
                      "status": result["status"], "semantic_sha256": digest(semantic.encode()),
                      "raw_sha256": digest(raw.encode()), "stderr": result["stderr"],
                      "counts": [line for line in raw.splitlines() if line.startswith('("counts",')]}
            records.append(record)
            archive.write(json.dumps({"case": name, **result}) + "\n")
            print(name, result["status"], flush=True)
    (output / "correctness.json").write_text(json.dumps(
        {"executable": identity(executable), "inputs": input_identity(), "records": records}, indent=2) + "\n")
    if any(record["status"] != "ok" for record in records):
        raise SystemExit("correctness cases failed; inspect retained observations")


def compare_correctness(reference, candidate):
    old = json.loads((reference / "correctness.json").read_text())
    new = json.loads((candidate / "correctness.json").read_text())
    expected = {r["case"]: (r["status"], r["semantic_sha256"]) for r in old["records"]}
    actual = {r["case"]: (r["status"], r["semantic_sha256"]) for r in new["records"]}
    changed = sorted(k for k in expected.keys() | actual.keys() if expected.get(k) != actual.get(k))
    print(json.dumps({"changed": changed}, indent=2))
    if changed:
        raise SystemExit(1)


def trials(executable, full):
    selected = cases(executable) if full else [
        "short", "many-small", "few-large", "malformed", "duplicate-relation", "ambiguous-relation", "owned-field-failure",
        "derivations-128-equal", "derivations-128-distinct",
        "relation-disjoint-128-1", "relation-disjoint-128-1-failure",
        "constant-disjoint-128-1", "constant-disjoint-128-1-match",
        "prefix-disjoint-128-1", "prefix-disjoint-128-8",
        "noun-shared-128-1", "noun-disjoint-128-1",
        "adjective-shared-128-1", "adjective-disjoint-128-1",
        "verb-shared-128-1", "function-shared-128-1", "mixfix-disjoint-128-1"]
    commands = [["measure", name, mode, "8"] for name in selected for mode in ["parse", "report"]]
    commands += [["measure", name, mode, "8"] for name in ["short", "noun-shared-128-1", "constant-disjoint-128-1"]
                 for mode in ["native", "markup", "rebuild"]]
    commands += [["corpus", root] for root in ROOTS]
    commands += [["html", name] for name in ["short", "noun-shared-128-1", "constant-disjoint-128-1"]]
    commands += [["materialize", str(n)] for n in [0, 32, 128]]
    return commands


def measure(reference, candidate, output, repetitions, full):
    output.mkdir(parents=True, exist_ok=True)
    executables = {"reference": identity(reference), "candidate": identity(candidate)}
    metadata = {"executables": executables, "platform": platform.platform(),
                "machine": platform.machine(), "python": platform.python_version(),
                "cpu_count": os.cpu_count(), "cwd": str(Path.cwd()),
                "NAPROCHE_LIB": os.environ.get("NAPROCHE_LIB"),
                "rts": RTS, "repetitions": repetitions,
                "filesystem_cache": "uncontrolled OS cache; no cache flushing",
                "schedule": "alternate AB / BA by repetition, fresh process per command",
                "allocation_scope": "local rows: getAllocationCounter, calling Haskell thread; RTS: completed process including setup and harness",
                "residency_scope": "RTS sampled process high-water, including setup/retained inputs/harness; no subtraction"}
    metadata["inputs"] = input_identity()
    metadata["revision"] = subprocess.check_output(["git", "rev-parse", "HEAD"], text=True).strip()
    (output / "metadata.json").write_text(json.dumps(metadata, indent=2) + "\n")
    with (output / "samples.jsonl").open("w") as stream:
        for repetition in range(repetitions):
            for command in trials(reference, full):
                for label in (["reference", "candidate"] if repetition % 2 == 0 else ["candidate", "reference"]):
                    executable = executables[label]
                    result = execute(executable["path"], command, rts=True)
                    record = {"repetition": repetition, "label": label, "executable_sha256": executable["sha256"],
                              "command": command, **result}
                    if result["status"] == "ok":
                        record["rows"] = [dict(zip(["stage", "iteration", "elapsed_ns", "thread_allocated_bytes"],
                                                   [fields[0], *map(int, fields[1:])]))
                                          for line in result["stdout"].splitlines() if len(fields := line.split("\t")) == 4]
                        try:
                            record["rts"] = dict(ast.literal_eval(result["stderr"].strip()))
                        except (SyntaxError, ValueError):
                            record["status"] = "invalid-rts-output"
                    stream.write(json.dumps(record) + "\n")
                    stream.flush()
                    print(repetition, label, " ".join(command), record["status"], flush=True)
    summarize(output)


def summarize(output):
    groups = {}
    failures = []
    source = output / "samples.jsonl"
    raw = source.read_text() if source.exists() else gzip.open(output / "samples.jsonl.gz", "rt").read()
    for line in raw.splitlines():
        row = json.loads(line)
        if row["status"] != "ok":
            failures.append({"command": row["command"], "status": row["status"]})
            continue
        command = " ".join(row["command"])
        selected = [r for r in row["rows"] if r["stage"] not in ["lexical-data", "prepare-lexicon"]]
        metrics = {"elapsed_ns": sum(r["elapsed_ns"] for r in selected),
                   "thread_allocated_bytes": sum(r["thread_allocated_bytes"] for r in selected),
                   "first_ns": selected[0]["elapsed_ns"],
                   "subsequent_median_ns": statistics.median([r["elapsed_ns"] for r in selected[1:]]) if len(selected) > 1 else None,
                   "process_allocated_bytes": float(row["rts"]["bytes allocated"]),
                   "max_live_bytes": float(row["rts"]["max_bytes_used"])}
        for metric, value in metrics.items():
            if value is not None:
                groups.setdefault((command, metric), {}).setdefault(row["label"], []).append(value)
    summaries = []
    for (command, metric), labels in groups.items():
        if set(labels) != {"reference", "candidate"}:
            continue
        ref, cand = (statistics.median(labels[label]) for label in ["reference", "candidate"])
        interval = bootstrap_interval(labels["reference"], labels["candidate"])
        summaries.append({"command": command, "metric": metric,
                          "reference_median": ref, "candidate_median": cand,
                          "ratio": cand / ref if ref else None,
                          "paired_bootstrap_95": interval,
                          "reference_range": [min(labels["reference"]), max(labels["reference"])],
                          "candidate_range": [min(labels["candidate"]), max(labels["candidate"])]})
    (output / "summary.json").write_text(json.dumps({"failures": failures, "comparisons": summaries}, indent=2) + "\n")
    if failures:
        raise SystemExit("measurement failures retained in report")


def bootstrap_interval(reference, candidate):
    """Paired repetition resampling of the ratio of medians (fixed seed)."""
    if not statistics.median(reference):
        return None
    if len(set(reference)) == len(set(candidate)) == 1:
        ratio = candidate[0] / reference[0]
        return [ratio, ratio]
    rng = random.Random(0)
    ratios = []
    for _ in range(2000):
        indices = [rng.randrange(len(reference)) for _ in reference]
        ratios.append(statistics.median(candidate[i] for i in indices) /
                      statistics.median(reference[i] for i in indices))
    ratios.sort()
    return [ratios[49], ratios[1950]]


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    sub = parser.add_subparsers(dest="command", required=True)
    p = sub.add_parser("check")
    p.add_argument("executable")
    p.add_argument("output", type=Path)
    p = sub.add_parser("compare")
    p.add_argument("reference", type=Path)
    p.add_argument("candidate", type=Path)
    p = sub.add_parser("measure")
    p.add_argument("reference")
    p.add_argument("candidate")
    p.add_argument("output", type=Path)
    p.add_argument("--repetitions", type=int, default=7)
    p.add_argument("--full", action="store_true")
    p = sub.add_parser("summary")
    p.add_argument("output", type=Path)
    args = parser.parse_args()
    if args.command == "check":
        check(args.executable, args.output)
    elif args.command == "compare":
        compare_correctness(args.reference, args.candidate)
    elif args.command == "measure":
        measure(args.reference, args.candidate, args.output, args.repetitions, args.full)
    else:
        summarize(args.output)


if __name__ == "__main__":
    main()

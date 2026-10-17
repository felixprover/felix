#!/usr/bin/env python3
"""Summarize Felix's formation-v1 completion records (stdin or log files)."""

import argparse
import collections
import json
import math
import re
import sys


def records(lines):
    for line in lines:
        if not line.startswith("formation-v1\t"):
            continue
        _, kind, *fields = line.rstrip("\n").split("\t")
        decoded = {}
        for field in fields:
            key, value = field.split("=", 1)
            value = re.sub(r"\\([\\tnr])", lambda match: {
                "\\": "\\", "t": "\t", "n": "\n", "r": "\r"
            }[match[1]], value)
            decoded[key] = int(value) if value.isascii() and value.isdigit() else value
        yield kind, decoded


def percentile(histogram, fraction):
    rank = math.ceil(sum(histogram.values()) * fraction)
    if not rank:
        return 0
    cumulative = 0
    for work, frequency in sorted(histogram.items()):
        cumulative += frequency
        if cumulative >= rank:
            return work
    raise ValueError("invalid group histogram")


def atomic_cohort(parsed):
    cohort = {}
    for kind, fields in parsed:
        if kind == "leaf" and fields["kind"] == "atomic":
            key = tuple(fields[name] for name in ("source", "consumer", "requirement"))
            counts = cohort.setdefault(key, collections.Counter())
            counts["leaves"] += 1
            counts["direct"] += fields["outcome"] == "ExactDirect"
    if not cohort:
        raise ValueError("atomic cohort comparison needs detailed leaf records")
    return cohort


def compare_cohort(baseline, current):
    # Equal occurrence counts keep expansion-created or removed leaves out of
    # the unchanged population; source labels are never work-deduplication keys.
    keys = {key for key in baseline.keys() & current.keys()
            if baseline[key]["leaves"] == current[key]["leaves"]}
    leaves = sum(baseline[key]["leaves"] for key in keys)
    if not leaves:
        raise ValueError("no unchanged atomic cohort")
    before = sum(baseline[key]["direct"] for key in keys) / leaves
    after = sum(current[key]["direct"] for key in keys) / leaves
    return {"sites": len(keys), "leaves": leaves,
            "baseline_direct_fraction": before, "current_direct_fraction": after,
            "drop_percentage_points": 100 * (before - after),
            "excluded_baseline_sites": len(baseline) - len(keys),
            "excluded_current_sites": len(current) - len(keys)}


def summarize(lines, include_groups=False, baseline=None):
    parsed = list(records(lines))
    summaries = [fields for kind, fields in parsed if kind == "summary"]
    if not summaries:
        raise ValueError("no verification completion summary (the run may be incomplete)")
    versions = {record["work-version"] for record in summaries}
    if len(versions) != 1:
        raise ValueError("cannot add different formation work-unit versions")
    totals = collections.Counter()
    histogram = collections.Counter()
    limits = {}
    for record in summaries:
        for key, value in record.items():
            if key == "work-version":
                continue
            if key.startswith("hist."):
                histogram[int(key[5:])] += value
            elif key.startswith("limit."):
                limits[key[6:]] = max(limits.get(key[6:], 0), value)
            elif isinstance(value, int):
                totals[key] += value
    if sum(histogram.values()) != totals["groups"]:
        raise ValueError("group histogram disagrees with completion count")
    result = {
        "work_version": versions.pop(),
        "verifications": len(summaries),
        "groups": totals.pop("groups", 0),
        "leaves": totals.pop("leaves", 0),
        "group_work": {"p50": percentile(histogram, 0.50),
                       "p99": percentile(histogram, 0.99),
                       "max": max(histogram, default=0)},
        "work": sum(value for key, value in totals.items() if key.startswith("phase-work.")),
        "seconds": sum(value for key, value in totals.items() if key.startswith("time-ns.")) / 1e9,
        "counters": dict(sorted(totals.items())),
        "limit_high_water": dict(sorted(limits.items())),
    }
    if include_groups:
        result["group_details"] = [fields for kind, fields in parsed if kind == "group"]
        result["leaf_details"] = [fields for kind, fields in parsed if kind == "leaf"]
    if baseline is not None:
        result["atomic_cohort"] = compare_cohort(baseline, atomic_cohort(parsed))
    return result


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("logs", nargs="*", help="each log is summarized separately; default: stdin")
    parser.add_argument("--json", action="store_true", help="emit machine-readable results")
    parser.add_argument("--groups", action="store_true", help="include detailed group completion records")
    parser.add_argument("--cohort-baseline", help="compare unchanged atomic leaves with this detailed log")
    args = parser.parse_args()
    baseline = None
    if args.cohort_baseline:
        try:
            with open(args.cohort_baseline, encoding="utf-8") as source:
                baseline = atomic_cohort(records(source))
        except (OSError, ValueError, KeyError) as error:
            parser.exit(1, f"{args.cohort_baseline}: {error}\n")
    results = {}
    for path in args.logs or ["-"]:
        try:
            if path == "-":
                results[path] = summarize(sys.stdin, args.groups, baseline)
            else:
                with open(path, encoding="utf-8") as source:
                    results[path] = summarize(source, args.groups, baseline)
        except (OSError, ValueError, KeyError) as error:
            parser.exit(1, f"{path}: {error}\n")
    if args.json:
        print(json.dumps(results, indent=2))
        return
    for name, result in results.items():
        print(f"{name}: {result['groups']} groups, {result['leaves']} leaves; "
              f"{result['work']:,} work, {result['seconds']:.6f} phase seconds")
        work = result["group_work"]
        print(f"  Group work: p50 {work['p50']:,}, p99 {work['p99']:,}, max {work['max']:,}")
        for key, value in result["counters"].items():
            print(f"  {key}: {value:,}")
        for key, value in result["limit_high_water"].items():
            print(f"  limit.{key}: {value:,}")
        for group in result.get("group_details", []):
            print("  " + json.dumps(group, ensure_ascii=False, sort_keys=True))
        for leaf in result.get("leaf_details", []):
            print("  " + json.dumps(leaf, ensure_ascii=False, sort_keys=True))
        if "atomic_cohort" in result:
            print("  Atomic cohort: " + json.dumps(result["atomic_cohort"], sort_keys=True))


if __name__ == "__main__":
    main()

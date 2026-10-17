#!/usr/bin/env python3
"""Compare Felix ATP dumps without changing the inputs sent to the prover.

The grammar below follows Checking/Backend/Tptp.hs: fully parenthesized FOF
and monomorphic THF, including typed quantifiers, lambdas and applications.
This is deliberately not a general TPTP simplifier. It retains every formula
constructor, symbol, type and role. Only tg_h<N> declaration labels, bound
variable names and declaration order are ignored. Unknown syntax is an error.
"""

import argparse
from collections import Counter, defaultdict
import hashlib
import json
from pathlib import Path
import re


TOKEN = re.compile(r"\s+|<=>|=>|\$[a-z]+|[A-Za-z][A-Za-z0-9_]*|[(),.\[\]:!?^~=@>]")
ATOM = re.compile(r"[a-z][A-Za-z0-9_]*\Z")
VARIABLE = re.compile(r"[A-Z][A-Za-z0-9_]*\Z")
PREMISE_LABEL = re.compile(r"tg_h[0-9]+\Z")


class SyntaxError(ValueError):
    """Input is outside the supported Felix emitter grammar."""


class Parser:
    def __init__(self, source):
        self.tokens = []
        end = 0
        for match in TOKEN.finditer(source):
            if match.start() != end:
                raise SyntaxError(f"unsupported syntax at byte {end}: {source[end:end + 30]!r}")
            if not match[0].isspace():
                self.tokens.append(match[0])
            end = match.end()
        if end != len(source):
            raise SyntaxError(f"unsupported syntax at byte {end}: {source[end:end + 30]!r}")
        self.position = 0

    def peek(self):
        return self.tokens[self.position] if self.position < len(self.tokens) else None

    def take(self, expected=None):
        token = self.peek()
        if token is None or (expected is not None and token != expected):
            raise SyntaxError(f"token {self.position}: expected {expected!r}, found {token!r}")
        self.position += 1
        return token

    def atom(self):
        token = self.take()
        if not ATOM.fullmatch(token):
            raise SyntaxError(f"expected an atomic word, found {token!r}")
        return token

    def core_type(self):
        token = self.take()
        if token in ("$i", "$o"):
            return token
        if token == "(":
            domain = self.core_type()
            self.take(">")
            codomain = self.core_type()
            self.take(")")
            return (">", domain, codomain)
        raise SyntaxError(f"unsupported type {token!r}")

    def expression(self, dialect, binders=()):
        token = self.take()
        if token == "(":
            operator = self.peek()
            if operator in ("!", "?", "^"):
                self.take()
                if operator == "^" and dialect != "thf":
                    raise SyntaxError("a FOF formula contains a lambda")
                self.take("[")
                variable = self.take()
                if not VARIABLE.fullmatch(variable):
                    raise SyntaxError("a binder must bind a variable")
                annotation = None
                if dialect == "thf":
                    self.take(":")
                    annotation = self.core_type()
                self.take("]")
                self.take(":")
                body = self.expression(dialect, (variable,) + binders)
                self.take(")")
                return (operator, annotation, body)
            if operator == "~":
                self.take()
                body = self.expression(dialect, binders)
                self.take(")")
                return ("~", body)
            left = self.expression(dialect, binders)
            operator = self.take()
            if operator not in ("=", "=>", "<=>") and not (operator == "@" and dialect == "thf"):
                raise SyntaxError(f"unsupported {dialect} operator {operator!r}")
            right = self.expression(dialect, binders)
            self.take(")")
            return (operator, left, right)
        if VARIABLE.fullmatch(token):
            # De Bruijn indices distinguish shadowing and capture. A free
            # variable keeps its spelling; it is never treated as a binder.
            if token in binders:
                return ("bound", binders.index(token))
            return ("free", token)
        if token in ("$true", "$false"):
            return ("constant", token)
        if ATOM.fullmatch(token):
            arguments = []
            if self.peek() == "(":
                if dialect != "fof":
                    raise SyntaxError("THF application must use @")
                self.take("(")
                arguments.append(self.expression(dialect, binders))
                while self.peek() == ",":
                    self.take(",")
                    arguments.append(self.expression(dialect, binders))
                self.take(")")
            return ("symbol", token, arguments)
        raise SyntaxError(f"unsupported expression {token!r}")

    def declaration(self):
        dialect = self.take()
        if dialect not in ("fof", "thf"):
            raise SyntaxError(f"unsupported dialect {dialect!r}")
        self.take("(")
        label = self.atom()
        self.take(",")
        role = self.atom()
        self.take(",")
        if role == "type" and dialect == "thf":
            self.take("(")
            symbol = self.atom()
            self.take(":")
            body = ("type", symbol, self.core_type())
            self.take(")")
        elif role in ("axiom", "conjecture"):
            body = self.expression(dialect)
        else:
            raise SyntaxError(f"unsupported {dialect} role {role!r}")
        self.take(")")
        self.take(".")
        # Only generated premise labels are disposable. In particular, type
        # declaration names and the conjecture's name remain observable.
        normalized_label = "tg_h" if role == "axiom" and PREMISE_LABEL.fullmatch(label) else label
        return label, (dialect, normalized_label, role, body)


def normalize_problem(source):
    parser = Parser(source)
    declarations = []
    labels = set()
    while parser.peek() is not None:
        label, declaration = parser.declaration()
        if label in labels:
            raise SyntaxError(f"duplicate declaration label {label!r}")
        labels.add(label)
        declarations.append(json.dumps(declaration, separators=(",", ":")))
    if not declarations:
        raise SyntaxError("empty ATP input")
    # A sorted list, not a set: repeated premises and repeated problems count.
    return "\n".join(sorted(declarations)).encode("ascii")


def digest(content):
    return hashlib.sha256(content).hexdigest()


def read_dump(directory):
    raw, normalized = Counter(), Counter()
    by_normalized = defaultdict(list)
    paths = sorted(directory.glob("*.p"))
    if not paths:
        raise SyntaxError(f"no ATP inputs in {directory}")
    for path in paths:
        content = path.read_bytes()
        try:
            normal = digest(normalize_problem(content.decode("ascii")))
        except (ValueError, RecursionError) as error:
            raise SyntaxError(f"{path}: {error}") from error
        exact = digest(content)
        raw[exact] += 1
        normalized[normal] += 1
        by_normalized[normal].append({"file": path.name, "raw_sha256": exact})
    return raw, normalized, by_normalized


def hash_multiset(counts):
    return "".join(value + "\n" for value in sorted(counts.elements())).encode("ascii")


def compare_dumps(baseline, candidate):
    old_raw, old_normal, old_files = read_dump(baseline)
    new_raw, new_normal, new_files = read_dump(candidate)
    def comparison(old, new):
        return {"equal": old == new, "missing": (old - new).total(),
                "added": (new - old).total(),
                "baseline_multiset_sha256": digest(hash_multiset(old)),
                "candidate_multiset_sha256": digest(hash_multiset(new))}
    differences = []
    for normal in sorted(old_files.keys() | new_files.keys()):
        before, after = old_files[normal], new_files[normal]
        if Counter(x["raw_sha256"] for x in before) != Counter(x["raw_sha256"] for x in after):
            differences.append({"normalized_sha256": normal, "baseline": before, "candidate": after})
    return ({"normalization_version": 1, "baseline": str(baseline), "candidate": str(candidate),
             "baseline_inputs": old_raw.total(), "candidate_inputs": new_raw.total(),
             "raw": comparison(old_raw, new_raw), "normalized": comparison(old_normal, new_normal),
             "raw_differences": differences}, new_raw, new_normal)


def main():
    arguments = argparse.ArgumentParser(description=__doc__)
    arguments.add_argument("baseline", type=Path)
    arguments.add_argument("candidate", type=Path)
    arguments.add_argument("output", type=Path, help="JSON report; raw and normalized hash lists are written beside it")
    args = arguments.parse_args()
    try:
        report, raw, normalized = compare_dumps(args.baseline, args.candidate)
    except (OSError, ValueError, RecursionError) as error:
        arguments.exit(2, f"ATP comparison failed: {error}\n")
    args.output.write_text(json.dumps(report, indent=2) + "\n", encoding="utf-8")
    args.output.with_suffix(".raw.sha256").write_bytes(hash_multiset(raw))
    args.output.with_suffix(".normalized.sha256").write_bytes(hash_multiset(normalized))
    print(json.dumps({key: value for key, value in report.items() if key != "raw_differences"}, indent=2))
    return 0 if report["normalized"]["equal"] else 1


if __name__ == "__main__":
    raise SystemExit(main())

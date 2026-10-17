#!/usr/bin/env python3
"""Semantic boundaries of the comparison-only ATP normalizer."""

from pathlib import Path
import runpy
import tempfile
import unittest

oracle = runpy.run_path(str(Path(__file__).with_name("atp-compare.py")))
normalize = oracle["normalize_problem"]


class AtpComparisonTests(unittest.TestCase):
    def test_permitted_changes_and_scoped_shadowing(self):
        before = "fof(tg_h0,axiom,(![V0]:(?[V1]:tg_g0(V0,V1)))).\nfof(tg_h1,axiom,$true)."
        after = "fof(tg_h92,axiom,$true).\nfof(tg_h47,axiom,(![V99]:(?[V12]:tg_g0(V99,V12))))."
        self.assertEqual(normalize(before), normalize(after))
        self.assertEqual(normalize("fof(tg_h0,axiom,(![V0]:(?[V0]:tg_g0(V0))))."),
                         normalize("fof(tg_h9,axiom,(![X]:(?[Y]:tg_g0(Y))))."))

    def test_rejects_substantive_formula_changes(self):
        original = "fof(tg_h0,axiom,(![V0]:(?[V1]:tg_g0(V0,V1))))."
        for changed in [original.replace("tg_g0", "tg_g1"),
                        original.replace("axiom", "conjecture"),
                        original.replace("?[V1]", "![V1]"),
                        original.replace("tg_g0(V0,V1)", "tg_g0(V1,V0)"),
                        original.replace("tg_g0(V0,V1)", "tg_g0(V0,V0)"),
                        original.replace("?[V1]", "?[V0]"),
                        original.replace("tg_g0(V0,V1)", "(~tg_g0(V0,V1))"),
                        original + original.replace("tg_h0", "tg_h1")]:
            with self.subTest(changed=changed):
                self.assertNotEqual(normalize(original), normalize(changed))
        self.assertNotEqual(normalize("fof(tg_h0,axiom,tg_g0(X))."),
                            normalize("fof(tg_h0,axiom,tg_g0(Y))."))
        self.assertNotEqual(normalize("fof(tg_q0,conjecture,$true)."),
                            normalize("fof(tg_q1,conjecture,$true)."))
        for operator in ["=", "=>", "<=>"]:
            self.assertNotEqual(normalize(f"fof(tg_h0,axiom,(tg_g0{operator}tg_g1))."),
                                normalize(f"fof(tg_h0,axiom,(tg_g1{operator}tg_g0))."))

    def test_thf_preserves_types_binding_application_and_logical_constants(self):
        # The exact parenthesization and lambda spacing emitted by Tptp.hs.
        problem = "\n".join([
            "thf(tg_g_type_0,type,(tg_g0:(($i>$o)>$i))).",
            "thf(tg_h0,axiom,(! [V0:$i] : ((tg_g0@(^ [V1:$i] : (V1=V0)))=V0))).",
            "thf(tg_q0,conjecture,((tg_g1=>$false)=>$true))."])
        self.assertEqual(normalize(problem), normalize(problem.replace("V0", "V70").replace("V1", "V31")))
        for changed in [problem.replace("$i>$o", "$i>$i"),
                        problem.replace("V0:$i", "V0:$o"),
                        problem.replace("(V1=V0)", "(V1=V1)"),
                        problem.replace("$false", "$true"),
                        problem.replace("tg_g0@", "tg_g2@"),
                        problem.replace("^ [", "! ["),
                        problem.replace("tg_g_type_0", "tg_g_type_1")]:
            with self.subTest(changed=changed):
                self.assertNotEqual(normalize(problem), normalize(changed))

    def test_unsupported_or_malformed_input_fails_closed(self):
        for source in ["", "include('other.p').", "cnf(x,axiom,p).",
                       "fof(tg_h0,axiom,(![V0,V1]:tg_g0(V0,V1))).",
                       "thf(tg_h0,axiom,(![V0]:V0)).", "fof(tg_h0,axiom,(p@q)).",
                       "fof(tg_h0,axiom,('quoted'=p)).", "fof(tg_h0,axiom,p,extra).",
                       "fof(tg_h0,axiom,(![V0]:p).", "fof(tg_h0,axiom,p). garbage",
                       "fof(tg_h0,axiom,p). fof(tg_h0,axiom,p).",
                       "thf(tg_g_type_0,type,(tg_g0:$tType))."]:
            with self.subTest(source=source):
                with self.assertRaises(ValueError):
                    normalize(source)

    def test_dump_comparison_preserves_problem_multiplicity(self):
        with tempfile.TemporaryDirectory() as directory:
            before, after = Path(directory) / "before", Path(directory) / "after"
            before.mkdir()
            after.mkdir()
            (before / "1.p").write_text("fof(tg_h0,axiom,(![V0]:tg_g0(V0))).")
            (after / "different-name.p").write_text("fof(tg_h17,axiom,(![V39]:tg_g0(V39))).")
            report, _, _ = oracle["compare_dumps"](before, after)
            self.assertFalse(report["raw"]["equal"])
            self.assertTrue(report["normalized"]["equal"])
            (after / "duplicate.p").write_text((after / "different-name.p").read_text())
            report, _, _ = oracle["compare_dumps"](before, after)
            self.assertFalse(report["normalized"]["equal"])
            self.assertEqual(report["normalized"]["added"], 1)


if __name__ == "__main__":
    unittest.main()

"""Focused positive and adversarial tests for the external certificate bridge."""
from __future__ import annotations

import json
import shutil
import subprocess
import sys
import tempfile
import time
import unittest
from fractions import Fraction as Q
from pathlib import Path
from unittest.mock import patch

from flint import arb, ctx

from arb_simple import Computation, I, WitnessWriter, bounds, rational_hull
from check_arithmetic import CertificateError, check_arithmetic
from verify_export import rational, verify_export

HERE = Path(__file__).resolve().parent
OUTPUT = HERE/"certificates/arb_simple"
TEMP = HERE/"test_outputs"
TEMP.mkdir(exist_ok=True)


class CertificateTests(unittest.TestCase):
    def setUp(self):
        ctx.prec = 192

    def test_exact_dyadic_endpoints_and_rational_input(self):
        for x in (Q(0), Q(3, 8), Q(-17, 32), Q(2**80+1, 2**31)):
            self.assertEqual(bounds(I(x)), (x, x))
        lo, hi = bounds(I(Q(1, 3)))
        self.assertLessEqual(lo, Q(1, 3))
        self.assertLessEqual(Q(1, 3), hi)
        with self.assertRaises(CertificateError):
            I(0.1)

    def test_hull_and_nonfinite_rejection(self):
        a, b = Q(1, 3), Q(2, 5)
        lo, hi = bounds(rational_hull(a, b))
        self.assertLessEqual(lo, a)
        self.assertLessEqual(b, hi)
        with self.assertRaises(CertificateError):
            bounds(arb("nan"))
        with self.assertRaises(CertificateError):
            rational_hull(b, a)

    def test_rational_schema_rejects_decimals(self):
        for bad in ("0.5", "1e-3", "2/4", "1/-3", "nan", 1):
            with self.assertRaises(CertificateError):
                rational(bad)

    def test_domain_and_bad_root_proposal_rejected(self):
        with tempfile.TemporaryDirectory(dir=TEMP) as directory:
            writer = WitnessWriter(Path(directory)/"test.jsonl")
            computation = Computation(writer, 192, Q(1, 10**14))
            try:
                with self.assertRaises(CertificateError):
                    computation.log(I(0))
                with self.assertRaises(CertificateError):
                    computation.sqrt(I(-1))
                with patch("arb_simple.proposed_root", return_value=3.0):
                    with self.assertRaisesRegex(CertificateError, "endpoint signs"):
                        computation.b_for(Q(1, 100))
            finally:
                writer.close()

    def test_complete_export(self):
        result = verify_export(OUTPUT)
        self.assertTrue(result["passed"])
        self.assertEqual(result["distinct_roots"], 12180)

    def mutated_export(self, predicate, mutate):
        temporary = tempfile.TemporaryDirectory(dir=TEMP)
        directory = Path(temporary.name)
        shutil.copyfile(OUTPUT/"summary.json", directory/"summary.json")
        changed = False
        with (OUTPUT/"witnesses.jsonl").open() as source, (directory/"witnesses.jsonl").open("w") as destination:
            for line in source:
                record = json.loads(line)
                if not changed and predicate(record):
                    mutate(record)
                    changed = True
                    line = json.dumps(record)+"\n"
                destination.write(line)
        self.assertTrue(changed)
        return temporary, directory

    def test_rejects_wrong_root_sign(self):
        temporary, directory = self.mutated_export(
            lambda r: r["kind"] == "root_bracket",
            lambda r: r["left_residual"].update(hi="0"))
        try:
            with self.assertRaisesRegex(CertificateError, "endpoint signs"):
                verify_export(directory, check_identity=False, check_partition=False)
        finally:
            temporary.cleanup()

    def test_rejects_wrong_sample_weight(self):
        temporary, directory = self.mutated_export(
            lambda r: r["kind"] == "sample",
            lambda r: r.update(weight=str(2*Q(r["weight"]))))
        try:
            with self.assertRaisesRegex(CertificateError, "coordinate/weight"):
                verify_export(directory, check_identity=False, check_partition=False)
        finally:
            temporary.cleanup()

    def test_rejects_wrong_guard(self):
        temporary, directory = self.mutated_export(
            lambda r: r["kind"] == "guard_evaluation",
            lambda r: r["value"].update(lo=r["threshold"]))
        try:
            with self.assertRaisesRegex(CertificateError, "Guard sign"):
                verify_export(directory, check_identity=False, check_partition=False)
        finally:
            temporary.cleanup()

    def test_rejects_inconsistent_sum(self):
        temporary, directory = self.mutated_export(
            lambda r: r["kind"] == "finite_sum" and r["family"] == "analytic",
            lambda r: r["enclosure"].update(hi=str(Q(r["enclosure"]["hi"])+1)))
        try:
            with self.assertRaisesRegex(CertificateError, "finite sum mismatch"):
                verify_export(directory, check_identity=False, check_partition=False)
        finally:
            temporary.cleanup()

    def test_rejects_changed_cell_profile(self):
        with tempfile.TemporaryDirectory(dir=TEMP) as directory:
            lines = (HERE/"reference/arithmetic_cells.tsv").read_text().splitlines()
            fields = lines[0].split()
            fields[2] = str(Q(fields[2])+1)
            lines[0] = "\t".join(fields)
            bad = Path(directory)/"bad.tsv"
            bad.write_text("\n".join(lines)+"\n")
            with self.assertRaisesRegex(CertificateError, "Profile coefficients"):
                check_arithmetic(bad, check_identity=False)

    def test_rejects_optimized_reference_execution(self):
        result = subprocess.run([sys.executable, "-O", str(HERE/"check_arithmetic.py")],
                                capture_output=True, text=True, check=False)
        self.assertNotEqual(result.returncode, 0)
        self.assertIn("Run without -O", result.stderr)


if __name__ == "__main__":
    start = time.time()
    suite = unittest.defaultTestLoader.loadTestsFromTestCase(CertificateTests)
    names = [test.id() for test in suite]
    result = unittest.TextTestRunner(verbosity=2).run(suite)
    report = {"passed": result.wasSuccessful(), "tests_run": result.testsRun,
              "tests": names, "failures": len(result.failures), "errors": len(result.errors),
              "wall_seconds": time.time()-start,
              "scope": "Finite connector and export integrity tests, not mathematical theorem verification."}
    (HERE/"certificates/test_report.json").write_text(json.dumps(report, indent=2)+"\n")
    raise SystemExit(0 if result.wasSuccessful() else 1)

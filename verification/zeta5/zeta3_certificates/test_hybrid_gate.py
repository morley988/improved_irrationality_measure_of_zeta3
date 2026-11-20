"""Focused fail-closed tests for the hybrid replay driver; no Lean or Arb run."""
from __future__ import annotations

import hashlib
import json
import os
from pathlib import Path
import sys
import tempfile
import unittest

from verify_hybrid import (
    ARB_AXIOMS, ARITHMETIC_AXIOM, CORE_DECLARATIONS, HYBRID_DECLARATIONS,
    MANIFEST_DIGEST, REPO, STANDARD_AXIOMS, Gate, GateFailure,
    check_file_hashes, check_semantic_manifest, digest, parse_axioms, validate_axioms,
)


def report(names, axioms):
    return "\n".join(f"'{name}' depends on axioms: [" + ",\n ".join(sorted(axioms)) + "]"
                     for name in sorted(names))


class AxiomBoundaryTests(unittest.TestCase):
    def test_accept_standard_core(self):
        result = validate_axioms(report(CORE_DECLARATIONS, STANDARD_AXIOMS),
                                 CORE_DECLARATIONS, frozenset())
        self.assertTrue(result["passed"])

    def test_accept_exact_eight_external(self):
        external = ARB_AXIOMS | {ARITHMETIC_AXIOM}
        result = validate_axioms(report(HYBRID_DECLARATIONS, STANDARD_AXIOMS | external),
                                 HYBRID_DECLARATIONS, external)
        self.assertEqual(len(result["required_external"]), 8)

    def test_reject_sorry_or_native_or_mathematical_axiom(self):
        for forbidden in ("sorryAx", "Lean.ofReduceBool", "Zeta3.Assumed.asymptoticRate"):
            with self.subTest(axiom=forbidden), self.assertRaises(GateFailure):
                validate_axioms(report(CORE_DECLARATIONS, STANDARD_AXIOMS | {forbidden}),
                                CORE_DECLARATIONS, frozenset())

    def test_reject_missing_declaration(self):
        with self.assertRaises(GateFailure):
            validate_axioms(report(set(CORE_DECLARATIONS) - {next(iter(CORE_DECLARATIONS))},
                                   STANDARD_AXIOMS), CORE_DECLARATIONS, frozenset())

    def test_reject_extra_declaration(self):
        with self.assertRaises(GateFailure):
            validate_axioms(report(CORE_DECLARATIONS | {"Unexpected.theorem"}, STANDARD_AXIOMS),
                            CORE_DECLARATIONS, frozenset())

    def test_reject_duplicate_report(self):
        text = report(CORE_DECLARATIONS, STANDARD_AXIOMS)
        with self.assertRaises(GateFailure):
            parse_axioms(text + "\n" + text)

    def test_reject_changed_arithmetic_boundary(self):
        with self.assertRaises(GateFailure):
            validate_axioms(report(HYBRID_DECLARATIONS, STANDARD_AXIOMS | ARB_AXIOMS),
                            HYBRID_DECLARATIONS, ARB_AXIOMS | {ARITHMETIC_AXIOM})
        with self.assertRaises(GateFailure):
            validate_axioms(report(HYBRID_DECLARATIONS, STANDARD_AXIOMS | ARB_AXIOMS | {ARITHMETIC_AXIOM}),
                            HYBRID_DECLARATIONS, ARB_AXIOMS)

    def test_accept_explicit_kernel_arithmetic_mode(self):
        self.assertTrue(validate_axioms(report(HYBRID_DECLARATIONS, STANDARD_AXIOMS | ARB_AXIOMS),
                                        HYBRID_DECLARATIONS, ARB_AXIOMS)["passed"])

    def test_reject_malformed_axiom_name(self):
        with self.assertRaises(GateFailure):
            parse_axioms("'x' depends on axioms: [propext, bad-name]")


class IdentityTests(unittest.TestCase):
    def test_reviewed_manifest_current(self):
        result = check_semantic_manifest(REPO, REPO / "zeta3_certificates/certificates/finite_semantic_manifest.json")
        self.assertEqual(result["manifest_sha256"], MANIFEST_DIGEST)

    def test_reject_manifest_mutation(self):
        original = REPO / "zeta3_certificates/certificates/finite_semantic_manifest.json"
        with tempfile.TemporaryDirectory() as directory:
            changed = Path(directory) / "manifest.json"
            changed.write_bytes(original.read_bytes() + b" ")
            with self.assertRaises(GateFailure):
                check_semantic_manifest(REPO, changed)

    def test_reject_source_mutation(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            source = root / "A.lean"
            source.write_text("theorem exact : True := True.intro\n")
            expected = {"A.lean": digest(source)}
            self.assertEqual(check_file_hashes(root, expected), expected)
            source.write_text("axiom exact : True\n")
            with self.assertRaises(GateFailure):
                check_file_hashes(root, expected)

    def test_reject_path_escape(self):
        with tempfile.TemporaryDirectory() as directory:
            with self.assertRaises(GateFailure):
                check_file_hashes(Path(directory), {"../outside": "0" * 64})


class ProcessFailureTests(unittest.TestCase):
    def test_nonzero_is_recorded_and_rejected(self):
        with tempfile.TemporaryDirectory() as directory:
            gate = Gate(Path(directory), 3, os.environ.copy())
            with self.assertRaises(GateFailure):
                gate.run("deliberate_failure", [sys.executable, "-c", "print('test-only failure');raise SystemExit(7)"])
            gate.finish(GateFailure("expected test failure"))
            result = json.loads((Path(directory) / "report.json").read_text())
            self.assertFalse(result["passed"])
            self.assertEqual(result["steps"][0]["exit_code"], 7)
            self.assertEqual(result["steps"][0]["status"], "failed")

    def test_timeout_is_recorded_and_rejected(self):
        with tempfile.TemporaryDirectory() as directory:
            gate = Gate(Path(directory), 0.15, os.environ.copy())
            with self.assertRaises(GateFailure):
                gate.run("deliberate_timeout", [sys.executable, "-c", "import time;time.sleep(3)"])
            gate.finish(GateFailure("expected test timeout"))
            result = json.loads((Path(directory) / "report.json").read_text())
            self.assertFalse(result["passed"])
            self.assertEqual(result["steps"][0]["status"], "failed")


if __name__ == "__main__":
    unittest.main(verbosity=2)

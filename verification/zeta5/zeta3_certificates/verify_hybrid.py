#!/usr/bin/env python3
"""Reproduce the explicitly delimited zeta(3) hybrid verification.

This gate does not convert Arb or Lean runtime results into kernel proofs.
It checks their pinned finite specification, replays the finite computations,
rechecks the mathematical modules with Lean --trust=0, and rejects every
unlisted axiom. Run only after the final endpoint modules have been built.
"""
from __future__ import annotations

import argparse
import hashlib
import json
import os
from pathlib import Path
import platform
import re
import shutil
import signal
import subprocess
import sys
import time
from datetime import datetime, timezone
from fractions import Fraction
from typing import Any
import uuid

HERE = Path(__file__).resolve().parent
REPO = HERE.parent
MANIFEST_DIGEST = "c0ddbb89b837c672e7a31265169e96054cabf503eed0a3324fa853d4b52b02af"
EXPECTED_LEAN_VERSION = "4.33.1"
EXPECTED_LEAN_COMMIT = "819816b2e0a3bf405af45ae5c7af2491d8f5bee6"
EXPECTED_FLINT = {"python_flint": "0.9.0", "flint": "3.6.0"}
EXPECTED_LEAN_CELLS = 5949
STANDARD_AXIOMS = frozenset({"propext", "Classical.choice", "Quot.sound"})
ARB_FIELDS = frozenset({"analytic_sum_lower", "physical_guard", "linear_sum_lower",
                        "angular_guard", "response_sum_upper", "endpoint_lower", "endpoint_upper"})
ARB_AXIOMS = frozenset(f"Zeta3.Hybrid.ExternalArb.{name}" for name in ARB_FIELDS)
ARITHMETIC_AXIOM = "Zeta3.Hybrid.ExternalArithmetic.arithmeticFiniteCheck_eq_true"
CORE_DECLARATIONS = frozenset({
    "Zeta3.Endpoint.actualArithmeticRate_of_finiteEvidence",
    "Zeta3.Endpoint.actualResponseRate_of_finiteEvidence",
    "Zeta3.Endpoint.riemannZeta_three_exponent_le_of_finiteEvidence",
    "Zeta3.Endpoint.riemannZeta_three_irrational_of_finiteEvidence",
    "Zeta3.Endpoint.riemannZeta_three_rational_separation_of_finiteEvidence",
    "Zeta3.Certificate.arithmeticFiniteCheck_sound",
})
HYBRID_DECLARATIONS = frozenset({
    "Zeta3.Hybrid.zeta3_irrationality_exponent_bound",
    "Zeta3.Hybrid.zeta3_irrational",
    "Zeta3.Hybrid.zeta3_rational_separation",
})
SEMANTIC_SOURCES = frozenset({
    "Zeta3/Certificate/FiniteNumerics.lean", "Zeta3/Certificate/Analytic.lean",
    "Zeta3/Parameters.lean", "Zeta3/Analysis/PhysicalMass.lean",
    "Zeta3/Analysis/PhysicalProfile.lean", "Zeta3/Analysis/ContourLinear.lean",
    "Zeta3/Analysis/AngularMass.lean", "Zeta3/Analysis/AngularProfile.lean",
    "Zeta3/Analysis/PhysicalGamma.lean", "Zeta3/Analysis/GammaKernel.lean",
    "Zeta3/Analysis/SimpleResponse.lean", "Zeta3/Analysis/CertifiedResponse.lean",
    "zeta3_certificates/arb_simple.py",
    "zeta3_certificates/certificates/arb_simple/summary.json",
    "zeta3_certificates/certificates/arb_simple/witnesses.jsonl",
})
AXIOM_REPORT = re.compile(r"'([^'\n]+)' depends on axioms:\s*\[([^\]]*)\]", re.DOTALL)
NO_AXIOM_REPORT = re.compile(r"'([^'\n]+)' does not depend on any axioms")


class GateFailure(RuntimeError):
    """A condition required for a successful hybrid gate was not met."""


def require(condition: bool, message: str) -> None:
    if not condition:
        raise GateFailure(message)


def utc_now() -> str:
    return datetime.now(timezone.utc).isoformat()


def digest(path: Path) -> str:
    value = hashlib.sha256()
    with path.open("rb") as stream:
        for block in iter(lambda: stream.read(1024 * 1024), b""):
            value.update(block)
    return value.hexdigest()


def atomic_json(path: Path, value: Any) -> None:
    temporary = path.with_name(path.name + ".partial")
    temporary.write_text(json.dumps(value, indent=2, sort_keys=True) + "\n")
    temporary.replace(path)


def check_file_hashes(root: Path, expected: dict[str, str]) -> dict[str, str]:
    """Fail closed on traversal, missing files, or any identity mismatch."""
    root = root.resolve()
    checked: dict[str, str] = {}
    for relative, expected_digest in expected.items():
        require(isinstance(relative, str) and not Path(relative).is_absolute(),
                "Manifest paths must be relative")
        path = (root / relative).resolve()
        require(path.is_relative_to(root), f"Manifest path escapes source root: {relative}")
        require(isinstance(expected_digest, str) and
                re.fullmatch(r"[0-9a-f]{64}", expected_digest) is not None,
                f"Invalid SHA256 in manifest: {relative}")
        require(path.is_file(), f"Missing pinned input: {relative}")
        actual = digest(path)
        require(actual == expected_digest, f"Pinned source hash mismatch: {relative}")
        checked[relative] = actual
    return checked


def check_semantic_manifest(root: Path, path: Path) -> dict:
    require(digest(path) == MANIFEST_DIGEST, "Semantic manifest itself has changed; explicit review is required")
    data = json.loads(path.read_text())
    require(data.get("seven_fields_match") is True and data.get("formula_mismatches") == [],
            "Semantic review does not certify all seven finite fields")
    require(set(data.get("positive_exact_slacks", {})) == ARB_FIELDS,
            "Semantic manifest has the wrong finite field set")
    for name, slack in data["positive_exact_slacks"].items():
        require(isinstance(slack, str) and Fraction(slack) > 0,
                f"Nonpositive or inexact semantic slack: {name}")
    require(set(data.get("sha256", {})) == SEMANTIC_SOURCES,
            "Semantic manifest source set has changed")
    return {"manifest_sha256": MANIFEST_DIGEST,
            "checked_sources": check_file_hashes(root, data["sha256"]),
            "scope": data["scope"]}


def parse_axioms(text: str) -> dict[str, list[str]]:
    reports: dict[str, list[str]] = {}
    for match in AXIOM_REPORT.finditer(text):
        name, body = match.groups()
        require(name not in reports, f"Duplicate axiom report: {name}")
        names = [part.strip() for part in body.split(",") if part.strip()]
        require(all(re.fullmatch(r"[A-Za-z_][A-Za-z_0-9.]*", axiom) for axiom in names),
                f"Malformed axiom name in report: {name}")
        require(len(names) == len(set(names)), f"Duplicate axiom in report: {name}")
        reports[name] = sorted(names)
    for match in NO_AXIOM_REPORT.finditer(text):
        name = match.group(1)
        require(name not in reports, f"Duplicate axiom report: {name}")
        reports[name] = []
    return reports


def validate_axioms(text: str, required: frozenset[str], external: frozenset[str]) -> dict:
    reports = parse_axioms(text)
    require(set(reports) == required,
            f"Axiom report declaration mismatch: missing={sorted(required-set(reports))}, "
            f"unexpected={sorted(set(reports)-required)}")
    allowed = STANDARD_AXIOMS | external
    for name, axioms in reports.items():
        actual = frozenset(axioms)
        require(actual <= allowed, f"Unexpected axiom for {name}: {sorted(actual-allowed)}")
        require(actual - STANDARD_AXIOMS == external,
                f"External axiom boundary changed for {name}: "
                f"expected={sorted(external)}, actual={sorted(actual-STANDARD_AXIOMS)}")
    return {"passed": True, "allowed_standard": sorted(STANDARD_AXIOMS),
            "required_external": sorted(external), "declarations": reports}


def source_snapshot(root: Path) -> dict[str, str]:
    """A race-detection snapshot, distinct from the reviewed semantic pin."""
    result: dict[str, str] = {}
    excluded = {".git", ".lake", ".venv", "__pycache__", "certificates", "node_modules"}
    names = {"lean-toolchain", "lake-manifest.json", "lakefile.zeta3.toml", "lakefile.toml", "lakefile.lean"}
    for parent, directories, files in os.walk(root):
        directories[:] = [name for name in directories if name not in excluded]
        for name in files:
            path = Path(parent) / name
            if path.suffix in {".lean", ".py"} or name in names:
                result[str(path.relative_to(root))] = digest(path)
    return result


class Gate:
    def __init__(self, output: Path, timeout: float, env: dict[str, str]):
        self.output = output
        self.timeout = timeout
        self.env = env
        self.started = time.monotonic()
        self.report: dict[str, Any] = {
            "schema": "zeta3-hybrid-gate-v1", "passed": False, "status": "running",
            "started_utc": utc_now(), "steps": [], "source_root": str(REPO),
            "driver_sha256": digest(Path(__file__)),
            "trust_boundary": "Lean kernel checks the mathematical implication; seven fixed real inequalities are external Arb evidence. The optional eighth external assertion is one closed finite rational Boolean. No external rank, valuation, integral, asymptotic, or irrationality premise is allowed.",
        }
        self.save()

    def save(self) -> None:
        atomic_json(self.output / "report.json", self.report)

    def run(self, name: str, command: list[str]) -> Path:
        number = len(self.report["steps"]) + 1
        log = self.output / f"{number:02d}_{name}.log"
        step = {"name": name, "command": command, "cwd": str(REPO),
                "started_utc": utc_now(), "log": log.name, "status": "running"}
        self.report["steps"].append(step)
        self.save()
        print(json.dumps({"step": name, "status": "started", "log": str(log)}), flush=True)
        started = time.monotonic()
        process = None
        try:
            with log.open("w") as stream:
                process = subprocess.Popen(command, cwd=REPO, env=self.env, stdout=stream,
                                           stderr=subprocess.STDOUT, text=True, start_new_session=True)
                last_notice = started
                while process.poll() is None:
                    now = time.monotonic()
                    if now - started > self.timeout:
                        os.killpg(process.pid, signal.SIGTERM)
                        try:
                            process.wait(timeout=5)
                        except subprocess.TimeoutExpired:
                            os.killpg(process.pid, signal.SIGKILL)
                            process.wait()
                        raise GateFailure(f"Step timed out: {name}")
                    if now - last_notice >= 30:
                        print(json.dumps({"step": name, "status": "running",
                                          "elapsed_seconds": round(now-started, 1)}), flush=True)
                        last_notice = now
                    time.sleep(0.2)
                step["exit_code"] = process.returncode
                require(process.returncode == 0, f"Step {name} exited with {process.returncode}; see {log}")
            step["status"] = "passed"
        except BaseException:
            step["status"] = "failed"
            if process is not None and process.poll() is None:
                os.killpg(process.pid, signal.SIGTERM)
                try:
                    process.wait(timeout=5)
                except subprocess.TimeoutExpired:
                    os.killpg(process.pid, signal.SIGKILL)
                    process.wait()
            raise
        finally:
            step["wall_seconds"] = time.monotonic() - started
            step["ended_utc"] = utc_now()
            if log.exists():
                step["log_sha256"] = digest(log)
            self.save()
        print(json.dumps({"step": name, "status": "passed", "wall_seconds": step["wall_seconds"]}), flush=True)
        return log

    def finish(self, error: BaseException | None = None) -> None:
        self.report["wall_seconds"] = time.monotonic() - self.started
        self.report["ended_utc"] = utc_now()
        self.report["passed"] = error is None
        self.report["status"] = "passed" if error is None else "failed"
        if error is not None:
            self.report["error"] = {"type": type(error).__name__, "message": str(error)}
        self.save()


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output-dir", type=Path,
                        help="New output directory; existing directories are rejected")
    parser.add_argument("--toolchain-bin", type=Path,
                        help="Directory containing the pinned Lean 4.33.1 and lake binaries")
    parser.add_argument("--arithmetic-mode", choices=("external", "kernel"), default="external",
                        help="Exact expected axiom boundary; kernel mode is usable only after an actual kernel arithmetic proof")
    parser.add_argument("--timeout-seconds", type=float, default=1800,
                        help="Maximum elapsed time per subprocess (default: 1800)")
    args = parser.parse_args(argv)
    output = args.output_dir or HERE / "certificates" / (
        "hybrid_gate_" + datetime.now(timezone.utc).strftime("%Y%m%dT%H%M%SZ") + "_" + uuid.uuid4().hex[:8])
    output = output.resolve()
    output.mkdir(parents=True, exist_ok=False)
    environment = os.environ.copy()
    gate = Gate(output, args.timeout_seconds, environment)
    try:
        require(sys.flags.optimize == 0, "Optimized Python execution is not permitted")
        require(args.timeout_seconds > 0, "The subprocess timeout must be positive")
        binary_dir = args.toolchain_bin
        if binary_dir is None:
            located = shutil.which("lean")
            require(located is not None, "Lean is unavailable; pass --toolchain-bin")
            binary_dir = Path(located).resolve().parent
        binary_dir = binary_dir.resolve()
        lean, lake = binary_dir / "lean", binary_dir / "lake"
        require(lean.is_file() and lake.is_file(), "The toolchain directory must contain both lean and lake")
        environment["PATH"] = str(binary_dir) + os.pathsep + environment.get("PATH", "")
        gate.report["arithmetic_mode"] = args.arithmetic_mode
        external = ARB_AXIOMS | (frozenset({ARITHMETIC_AXIOM}) if args.arithmetic_mode == "external" else frozenset())
        gate.report["expected_external_axioms"] = sorted(external)
        gate.report["semantic_review"] = check_semantic_manifest(
            REPO, HERE / "certificates/finite_semantic_manifest.json")
        baseline = source_snapshot(REPO)
        atomic_json(output / "source_snapshot.json", baseline)
        gate.report["source_snapshot_sha256"] = digest(output / "source_snapshot.json")
        gate.save()

        version_log = gate.run("lean_version", [str(lean), "--version"])
        version = version_log.read_text()
        require(f"version {EXPECTED_LEAN_VERSION}," in version and EXPECTED_LEAN_COMMIT in version,
                "Unexpected Lean version or source commit")
        env_log = gate.run("arb_environment", [sys.executable, "-c",
            "import json,sys,platform,flint; print(json.dumps({'python':sys.version,'python_flint':flint.__version__,'flint':flint.__FLINT_VERSION__,'platform':platform.platform()}))"])
        runtime = json.loads(env_log.read_text())
        require(all(runtime.get(key) == value for key, value in EXPECTED_FLINT.items()),
                "Unexpected python-flint or FLINT version")
        gate.report["runtime"] = runtime

        stored_report = output / "stored_192_export.json"
        gate.run("stored_192_export", [sys.executable, str(HERE / "verify_export.py"),
                 str(HERE / "certificates/arb_simple"), "--report", str(stored_report)])
        stored = json.loads(stored_report.read_text())
        require(stored.get("passed") is True, "Stored export was not validated")
        require(json.loads((HERE / "certificates/arb_simple/summary.json").read_text())["precision_bits"] == 192,
                "Stored baseline is not the reviewed 192-bit run")
        fresh = output / "arb_256"
        gate.run("fresh_arb_256", [sys.executable, str(HERE / "arb_simple.py"),
                 "--precision", "256", "--output-dir", str(fresh)])
        fresh_report = output / "fresh_256_export.json"
        gate.run("fresh_256_export", [sys.executable, str(HERE / "verify_export.py"),
                 str(fresh), "--report", str(fresh_report)])
        fresh_result = json.loads(fresh_report.read_text())
        require(fresh_result.get("passed") is True, "Fresh export was not validated")
        fresh_summary = json.loads((fresh / "summary.json").read_text())
        require(fresh_summary["precision_bits"] == 256, "Fresh run did not use 256-bit precision")
        require(stored["final_rational_expression"] == fresh_result["final_rational_expression"],
                "The two exports disagree on the exact final target")
        gate.report["arb_replays"] = {"stored_192": stored, "fresh_256": fresh_result,
            "fresh_summary_sha256": digest(fresh / "summary.json"),
            "fresh_witness_sha256": digest(fresh / "witnesses.jsonl")}

        base = [str(lake), "-f", "lakefile.zeta3.toml"]
        gate.run("build_finite_profile", base + ["build", "Zeta3.Certificate.ArithmeticFinite"])
        arithmetic_log = gate.run("actual_lean_finite_profile", base + ["env", str(lean), "--run",
                                           "zeta3_certificates/CheckFiniteProfile.lean"])
        arithmetic_text = arithmetic_log.read_text()
        require(f"PASS: {EXPECTED_LEAN_CELLS} cells;" in arithmetic_text and "FAIL:" not in arithmetic_text,
                "Actual Lean finite profile did not report the expected complete cell check")
        gate.report["lean_finite_profile"] = {"cells": EXPECTED_LEAN_CELLS, "passed": True,
            "scope": "Exact Lean runtime computation; not a kernel proof of the Boolean result."}

        gate.run("build_final_modules", base + ["build", "Zeta3.FinalAudit", "Zeta3.Hybrid.Verified"])
        core_log = gate.run("core_trust_zero", base + ["env", str(lean), "--trust=0", "Zeta3/FinalAudit.lean"])
        gate.report["core_axioms"] = validate_axioms(core_log.read_text(), CORE_DECLARATIONS, frozenset())
        hybrid_log = gate.run("hybrid_trust_zero", base + ["env", str(lean), "--trust=0", "Zeta3/Hybrid/Verified.lean"])
        gate.report["hybrid_axioms"] = validate_axioms(hybrid_log.read_text(), HYBRID_DECLARATIONS, external)
        check_semantic_manifest(REPO, HERE / "certificates/finite_semantic_manifest.json")
        final_snapshot = source_snapshot(REPO)
        require(final_snapshot == baseline, "Project source files changed during the gate; replay from a stable checkout")
        gate.report["source_stable_during_replay"] = True
        gate.finish()
        print(json.dumps({"passed": True, "report": str(output / "report.json"),
                          "external_axioms": sorted(external)}, indent=2), flush=True)
        return 0
    except BaseException as error:
        gate.finish(error)
        print(json.dumps({"passed": False, "report": str(output / "report.json"),
                          "error": str(error)}, indent=2), file=sys.stderr, flush=True)
        return 130 if isinstance(error, KeyboardInterrupt) else 1


if __name__ == "__main__":
    raise SystemExit(main())

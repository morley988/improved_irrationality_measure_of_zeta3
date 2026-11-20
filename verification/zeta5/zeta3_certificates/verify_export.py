"""Check the exported data's exact consistency with the finite specification.

This uses only the Python standard library.  It verifies all record counts,
node coordinates, references, interval signs, exact rational sums and final
comparison, plus the original arithmetic partition.  It does not independently
prove the real-function inclusions reported by Arb.  Those remain external
numerical evidence and must not be represented as kernel proofs.
"""
from __future__ import annotations

import argparse
import collections
import json
import re
import time
from fractions import Fraction as Q
from pathlib import Path

from check_arithmetic import CertificateError, check_arithmetic, require, sha256

HERE = Path(__file__).resolve().parent
PARAMETERS = {"s1": Q(2, 25), "s2": Q(8, 25), "delta": Q(51, 50),
              "u": Q(1000001, 1000000), "T": Q(17, 125),
              "Tcap": Q(7, 50), "degree_rate": Q(17, 25)}
TARGETS = {
    "arithmetic_constant": Q(1926282169226183949, 500000000000000000),
    "analytic_sum_lower": Q(300854183181, 62500000000),
    "linear_sum_lower": Q(3835733171, 31250000000),
    "response_sum_upper": Q(191284115113, 200000000000),
    "endpoint_lower": Q(6545408942519, 1000000000000),
    "endpoint_upper": Q(6545408942957, 1000000000000),
    "announced_upper": Q(2487, 500),
}
PANELS = {"analytic": 8192, "linear": 2048, "angular": 128, "response": 1024}


def rational(text) -> Q:
    require(isinstance(text, str) and re.fullmatch(r"-?\d+(?:/[1-9]\d*)?", text) is not None,
            "Expected an exact rational string")
    result = Q(text)
    require(str(result) == text, "Noncanonical rational string")
    return result


def interval(record) -> tuple[Q, Q]:
    require(set(record) == {"lo", "hi"}, "Malformed interval")
    lo, hi = rational(record["lo"]), rational(record["hi"])
    require(lo <= hi, "Reversed exported interval")
    return lo, hi


def qmap(record) -> dict[str, Q]:
    return {k: rational(v) for k, v in record.items()}


def verify_export(directory: Path, check_identity: bool = True,
                  check_partition: bool = True) -> dict:
    start = time.time()
    summary = json.loads((directory/"summary.json").read_text())
    require(summary["schema"] == "zeta3-arb-simple-summary-v1", "Wrong summary schema")
    require(summary["passed"] is True, "Summary is not marked successful")
    require(qmap(summary["parameters"]) == PARAMETERS, "Wrong parameters")
    require(qmap(summary["targets"]) == TARGETS, "Wrong targets")
    require(summary["panels"] == PANELS, "Wrong panel counts")
    witness_path = directory/summary["witnesses"]["file"]
    require(witness_path.resolve().parent == directory.resolve(), "Witness path escapes output directory")
    if check_identity:
        require(sha256(witness_path) == summary["witnesses"]["sha256"], "Witness hash mismatch")
        require(witness_path.stat().st_size == summary["witnesses"]["bytes"], "Witness size mismatch")
        for filename, digest in summary["source_sha256"].items():
            require(filename in ("arb_simple.py", "check_arithmetic.py"), "Unexpected source hash key")
            require(sha256(HERE/filename) == digest, f"Source hash mismatch: {filename}")
    counts = collections.Counter()
    roots: dict[str, tuple[Q, Q]] = {}
    guards: dict[str, tuple[Q, Q]] = {}
    widths: list[Q] = []
    sample_counts = {"analytic": 0, "linear": 0, "response": 0}
    sums = {family: [Q(0), Q(0)] for family in sample_counts}
    finished = set()
    endpoint = None
    target_checked = False
    s1, s2, delta, u, T, Tcap, lam = (PARAMETERS[k] for k in
        ("s1", "s2", "delta", "u", "T", "Tcap", "degree_rate"))
    steps = {"analytic": delta/8192, "linear": (delta-Tcap)/2048, "response": T/1024}
    for line_no, line in enumerate(witness_path.open(), 1):
        record = json.loads(line)
        kind = record["kind"]
        counts[kind] += 1
        require(line_no == 1 or kind != "header", "Duplicate header")
        if line_no == 1:
            require(kind == "header", "Missing initial header")
        if kind == "header":
            require(record["schema"] == "zeta3-arb-finite-witness-v1", "Wrong witness schema")
            require(qmap(record["parameters"]) == PARAMETERS, "Header parameter mismatch")
            require(record["panels"] == PANELS, "Header panel mismatch")
            require(rational(record["linear_coefficient"]) == TARGETS["linear_sum_lower"],
                    "Header coefficient mismatch")
        elif kind == "angular_charge":
            j = counts[kind]-1
            require(record["index"] == j and j < 128, "Charge ordering/count failure")
            node = s1+s2+(Q(j)+Q(1, 2))*(1-s1-s2)/128
            e = (u*u-node*node)**2/(2*u*u*node*node)
            require(rational(record["node"]) == node, "Wrong angular midpoint")
            require(rational(record["weight"]) == (1-s1-s2)/256, "Wrong charge weight")
            require(rational(record["pole_distance"]) == e and e > 0, "Wrong pole distance")
        elif kind == "root_bracket":
            family, parameter = record["family"], rational(record["parameter"])
            require(family in ("physical", "angular"), "Unknown root family")
            root_id = f"{family}:{parameter}"
            require(root_id == record["id"] and root_id not in roots, "Wrong or duplicate root id")
            require(0 < parameter <= (delta if family == "physical" else Tcap), "Root parameter out of range")
            left, right = rational(record["left"]), rational(record["right"])
            require(0 < left < right, "Invalid positive root bracket")
            left_value, right_value = interval(record["left_residual"]), interval(record["right_residual"])
            require(left_value[1] < 0 < right_value[0], "Root endpoint signs are not certified")
            root_ball = interval(record["enclosing_ball"])
            require(root_ball[0] <= left < right <= root_ball[1], "Root ball loses a bracket endpoint")
            roots[root_id] = root_ball
            widths.append(right-left)
        elif kind == "guard_evaluation":
            family = record["family"]
            require(family in ("physical_at_u", "angular_at_one") and family not in guards,
                    "Wrong or repeated guard evaluation")
            argument, threshold = (u, delta) if family == "physical_at_u" else (Q(1), Tcap)
            require(rational(record["argument"]) == argument and
                    rational(record["threshold"]) == threshold, "Wrong guard parameters")
            value = interval(record["value"])
            require(value[0] > threshold, "Guard sign failed")
            guards[family] = value
        elif kind == "sample":
            family = record["family"]
            require(family in ("analytic", "linear") and family not in finished, "Invalid sample family/order")
            k = sample_counts[family]
            require(record["index"] == k and k < PANELS[family], "Sample ordering/count failure")
            parameter, weight = rational(record["parameter"]), rational(record["weight"])
            require(parameter == k*steps[family] and weight == steps[family], "Wrong sample coordinate/weight")
            expected_root = f"physical:{parameter}" if parameter else "exact_zero"
            require(record["physical_root"] == expected_root, "Wrong sample root reference")
            require(parameter == 0 or expected_root in roots, "Unknown physical root")
            lo, hi = interval(record["value"])
            sums[family][0] += weight*lo
            sums[family][1] += weight*hi
            sample_counts[family] += 1
        elif kind == "response_sample":
            require("response" not in finished, "Response sample after completed sum")
            k = sample_counts["response"]
            require(record["index"] == k and k <= 1024, "Response ordering/count failure")
            t = rational(record["parameter"])
            require(t == k*steps["response"], "Wrong response coordinate")
            require(rational(record["physical_parameter"]) == delta-t, "Wrong physical response parameter")
            require(record["physical_root"] == f"physical:{delta-t}", "Wrong response physical root")
            require(record["physical_root"] in roots, "Unknown response physical root")
            angular_id = f"angular:{t}" if t else "exact_zero"
            require(record["angular_root"] == angular_id and (not t or angular_id in roots),
                    "Unknown or wrong response angular root")
            gamma, angular = interval(record["gamma"]), interval(record["angular_F"])
            value = interval(record["value"])
            require(value == (gamma[0]+angular[0], gamma[1]+angular[1]), "Response interval addition mismatch")
            weight = rational(record["weight"])
            require(weight == (steps["response"] if k < 1024 else Q(0)), "Wrong response weight")
            sums["response"][0] += weight*value[0]
            sums["response"][1] += weight*value[1]
            if k == 1024:
                endpoint = value
            sample_counts["response"] += 1
        elif kind == "finite_sum":
            family = record["family"]
            require(family in sample_counts and family not in finished, "Wrong or repeated finite sum")
            require(record["count"] == PANELS[family], "Wrong sum panel count")
            expected_samples = PANELS[family]+(1 if family == "response" else 0)
            require(sample_counts[family] == expected_samples, "Incomplete sample table")
            require(rational(record["step"]) == steps[family], "Wrong sum step")
            require(interval(record["enclosure"]) == tuple(sums[family]), "Exact finite sum mismatch")
            finished.add(family)
        elif kind == "target_checks":
            require(not target_checked and finished == set(sample_counts), "Premature or repeated target checks")
            require(qmap(record["targets"]) == TARGETS, "Target record mismatch")
            slack = TARGETS["analytic_sum_lower"]-TARGETS["arithmetic_constant"]-TARGETS["response_sum_upper"]
            result = lam*TARGETS["endpoint_upper"]/(slack+T*TARGETS["endpoint_upper"])
            require(slack > 0 and result < TARGETS["announced_upper"], "Final rational comparison failed")
            require(rational(record["response_slack"]) == slack, "Wrong target slack")
            require(rational(record["final_rational_expression"]) == result, "Wrong target final expression")
            target_checked = True
        else:
            raise CertificateError(f"Unknown record kind {kind!r}")
    require(target_checked, "Missing target checks")
    require(counts == summary["witnesses"]["records"], "Witness record count mismatch")
    require(counts["header"] == counts["target_checks"] == 1 and counts["angular_charge"] == 128,
            "Wrong fixed record counts")
    require(set(guards) == {"physical_at_u", "angular_at_one"}, "Missing numerical guards")
    require({k: interval(v) for k, v in summary["guard_evaluations"].items()} == guards,
            "Guard summary mismatch")
    expected_roots = {f"physical:{k*steps['analytic']}" for k in range(1, 8192)}
    expected_roots |= {f"physical:{k*steps['linear']}" for k in range(1, 2048)}
    expected_roots |= {f"physical:{delta-k*steps['response']}" for k in range(1025)}
    expected_roots |= {f"angular:{k*steps['response']}" for k in range(1, 1025)}
    expected_roots.add(f"angular:{Tcap}")
    require(set(roots) == expected_roots, "Root table does not exactly cover the required roots")
    require(len(roots) == summary["root_bracket_count"], "Wrong root count")
    require(max(widths) == rational(summary["largest_root_bracket_width"]), "Wrong largest root width")
    require(interval(summary["physical_support_endpoint"]) == roots[f"physical:{delta}"], "Wrong support endpoint")
    require(interval(summary["angular_endpoint_cap"]) == roots[f"angular:{Tcap}"], "Wrong angular cap")
    require(roots[f"physical:{delta}"][1] < u, "Support bound failed")
    require(roots[f"angular:{Tcap}"][1] < 1, "Angular cap bound failed")
    for family in sample_counts:
        require(interval(summary[f"{family}_finite_sum"]) == tuple(sums[family]), "Summary finite sum mismatch")
    require(endpoint == interval(summary["simple_endpoint"]), "Summary endpoint mismatch")
    require(sums["analytic"][0] >= TARGETS["analytic_sum_lower"], "Analytic target failed")
    require(sums["linear"][0] >= TARGETS["linear_sum_lower"] > 0, "Linear target failed")
    require(sums["response"][1] <= TARGETS["response_sum_upper"], "Response target failed")
    require(endpoint is not None and endpoint[0] >= TARGETS["endpoint_lower"] > 0,
            "Endpoint lower target failed")
    require(endpoint[1] <= TARGETS["endpoint_upper"], "Endpoint upper target failed")
    require(rational(summary["response_slack"]) == slack, "Summary slack mismatch")
    require(rational(summary["final_rational_expression"]) == result, "Summary final expression mismatch")
    if check_partition:
        require(check_arithmetic() == summary["arithmetic"], "Arithmetic summary mismatch")
    return {"passed": True, "record_counts": dict(counts), "distinct_roots": len(roots),
            "final_rational_expression": str(result), "wall_seconds": time.time()-start,
            "scope": "Exact data consistency, not independent proof of Arb's real-function enclosures."}


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("directory", nargs="?", type=Path, default=HERE/"certificates/arb_simple")
    parser.add_argument("--report", type=Path, help="Write validation JSON here instead of changing the input directory")
    args = parser.parse_args()
    result = verify_export(args.directory)
    report_path = args.report or args.directory/"export_validation.json"
    report_path.write_text(json.dumps(result, indent=2)+"\n")
    print(json.dumps(result, indent=2))

"""Finite exact checks of the existing cubic profile partition.

This checks a supplied partition rather than regenerating the subdivision.
Coverage, floors, guards, area and rounding are checked independently here.
The profile expression is re-evaluated using the pinned original source.
The mathematical valuation/profile and asymptotic theorems are not checked.
"""
from __future__ import annotations

import argparse
import hashlib
import importlib.util
import json
import sys
from fractions import Fraction as Q
from pathlib import Path

HERE = Path(__file__).resolve().parent
SOURCE_HASH = "dc7b2b828fed0c2757e21bd9e59142a0475a462314541c0114d991dc1f0f98ab"
CELLS_HASH = "fcfa9c5d70e7f54d40c74296354a97b82b4a04b5be7db9afaa06ebe09878d049"


class CertificateError(RuntimeError):
    pass


def require(condition: bool, message: str) -> None:
    if not condition:
        raise CertificateError(message)


def sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def load_profile(source: Path):
    require(sha256(source) == SOURCE_HASH, "Reference profile source hash mismatch")
    spec = importlib.util.spec_from_file_location("zeta3_pinned_profile", source)
    require(spec is not None and spec.loader is not None, "Could not load profile source")
    module = importlib.util.module_from_spec(spec)
    sys.modules[spec.name] = module
    spec.loader.exec_module(module)
    return module


def check_arithmetic(
    cell_path: Path = HERE / "reference/arithmetic_cells.tsv",
    source_path: Path = HERE / "reference/exact_arithmetic_original.py",
    check_identity: bool = True,
) -> dict:
    require(__debug__, "Run without -O: the pinned reference profile uses assertions")
    profile = load_profile(source_path)
    s1, s2, delta = Q(2, 25), Q(8, 25), Q(51, 50)
    cutoff, scale = 500, 10**18
    floor_arguments = [Q(1), Q(2), s1, s2, 2*s1, 2*s2,
                       2*(s1+delta), 2*(s2+delta)]
    guard_boundaries = [Q(1), Q(1, 2), Q(1, 3), 2*s2, 1-delta]
    previous, total, count = Q(1, cutoff), 0, 0
    for line_number, line in enumerate(cell_path.read_text().splitlines(), 1):
        fields = line.split()
        require(len(fields) == 5, f"Malformed cell at line {line_number}")
        left, right, intercept, slope = map(Q, fields[:4])
        rounded = int(fields[4])
        require(left == previous and left < right,
                f"Coverage/order failure at cell {line_number}")
        midpoint = (left + right) / 2
        # These inequalities establish floor(c/beta)=q on the open cell.
        # Endpoint discontinuities have measure zero; the mathematical
        # integral theorem must account for that separately.
        for numerator in floor_arguments:
            quotient = numerator / midpoint
            q = quotient.numerator // quotient.denominator
            require(q * right <= numerator <= (q+1) * left,
                    f"A floor boundary crosses cell {line_number}")
        require(all(not (left < x < right) for x in guard_boundaries),
                f"A guard boundary crosses cell {line_number}")
        # The source's Cell.le checks every affine min/max/order branch
        # against both endpoints and raises Split if an interior crossing
        # remains. All midpoint floor values were validated above.
        affine = profile.profile(profile.Cell(left, right), s1, s2, delta)
        require(Q(affine.a) == intercept and Q(affine.b) == slope,
                f"Profile coefficients disagree at cell {line_number}")
        area = (right-left) * (intercept+slope*(left+right)/2)
        require(Q(rounded-1, scale) < area <= Q(rounded, scale),
                f"Wrong outward area rounding at cell {line_number}")
        total += rounded
        count += 1
        previous = right
    require(previous == Q(67, 25), "Wrong partition endpoint")
    require(count == 6752, "Wrong cell count")
    digest = sha256(cell_path)
    if check_identity:
        require(digest == CELLS_HASH, "Reference cell file hash mismatch")
    finite_upper = Q(total, scale)
    tail_value = 4*delta/cutoff
    arithmetic_constant = finite_upper + tail_value
    require(finite_upper == Q(1922202169226183949, 500000000000000000),
            "Unexpected finite area upper bound")
    require(tail_value == Q(51, 6250), "Unexpected tail-expression value")
    require(arithmetic_constant == Q(1926282169226183949, 500000000000000000),
            "Unexpected arithmetic constant")
    return {
        "schema": "zeta3-arithmetic-finite-v1",
        "passed": True,
        "cell_count": count,
        "floor_checks_per_cell": len(floor_arguments),
        "interval": [str(Q(1, cutoff)), str(previous)],
        "scale": str(scale),
        "finite_affine_area_upper": str(finite_upper),
        "tail_expression_value": str(tail_value),
        "arithmetic_constant": str(arithmetic_constant),
        "rounding_error_upper": str(Q(count, scale)),
        "cell_sha256": digest,
        "profile_source_sha256": sha256(source_path),
        "scope": "Finite partition/profile evaluation only. No valuation, prime number theorem, integral-profile interpretation, or asymptotic tail assertion is certified here.",
    }


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--cells", type=Path, default=HERE/"reference/arithmetic_cells.tsv")
    parser.add_argument("--output", type=Path, default=HERE/"certificates/arithmetic_finite.json")
    args = parser.parse_args()
    result = check_arithmetic(args.cells)
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(result, indent=2)+"\n")
    print(json.dumps(result, indent=2))

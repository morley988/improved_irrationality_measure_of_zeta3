"""External Arb certificate for the finite SIMPLE-envelope zeta(3) data.

The output is numerical evidence, not a Lean proof.  No asymptotic theorem,
prime-number-theorem consequence, or integral-comparison theorem is asserted
by this program.  All supplied mathematical parameters and exported bounds
are exact rationals.  Python floats are used ONLY to propose root brackets;
Arb must verify both endpoint signs before any proposed bracket is used.
"""
from __future__ import annotations

import argparse
import hashlib
import json
import math
import platform
import sys
import time
from fractions import Fraction as Q
from pathlib import Path

import flint
from flint import arb, ctx, fmpq

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


def I(x: Q | int) -> arb:
    """An Arb ball enclosing an exact rational; floats are forbidden here."""
    require(isinstance(x, (Q, int)), f"Inexact input type {type(x).__name__}")
    q = Q(x)
    return arb(fmpq(q.numerator, q.denominator))


def dyadic(x: arb) -> Q:
    require(x.is_exact() and x.is_finite(), "Expected a finite exact Arb value")
    mantissa, exponent = x.man_exp()
    return Q(int(mantissa)) * Q(2)**int(exponent)


def bounds(x: arb) -> tuple[Q, Q]:
    """Exact endpoints of the stored binary ball, with no decimal conversion."""
    require(x.is_finite(), "Arb produced a nonfinite ball")
    middle, radius = dyadic(x.mid()), dyadic(x.rad())
    require(radius >= 0, "Negative ball radius")
    return middle-radius, middle+radius


def interval_record(x: arb | tuple[Q, Q]) -> dict[str, str]:
    lo, hi = bounds(x) if isinstance(x, arb) else x
    require(lo <= hi, "Inverted interval")
    return {"lo": str(lo), "hi": str(hi)}


def rational_hull(left: Q, right: Q) -> arb:
    require(left <= right, "Inverted rational hull")
    result = I(left).union(I(right))
    lo, hi = bounds(result)
    require(lo <= left and right <= hi, "Arb hull lost an endpoint")
    return result


def proposed_root(function, lo: float, hi: float) -> float:
    """Untrusted double-precision proposal; this never certifies a root."""
    for _ in range(80):
        middle = (lo+hi)/2
        if middle == lo or middle == hi:
            break
        if function(middle) < 0:
            lo = middle
        else:
            hi = middle
    return (lo+hi)/2


class WitnessWriter:
    def __init__(self, path: Path):
        self.path = path
        self.stream = path.open("w")
        self.counts: dict[str, int] = {}

    def write(self, kind: str, **fields) -> None:
        self.stream.write(json.dumps({"kind": kind, **fields}, sort_keys=True,
                                     separators=(",", ":"))+"\n")
        self.counts[kind] = self.counts.get(kind, 0)+1

    def close(self) -> None:
        self.stream.close()


class Computation:
    def __init__(self, writer: WitnessWriter, precision: int, root_radius: Q):
        require(precision >= 128, "Use at least 128 bits")
        require(0 < root_radius <= Q(1, 10**10), "Invalid root proposal radius")
        ctx.prec = precision
        ctx.threads = 1
        self.writer, self.root_radius = writer, root_radius
        self.s1, self.s2, self.delta, self.u, self.T, self.Tcap, self.lam = (
            PARAMETERS[k] for k in ("s1", "s2", "delta", "u", "T", "Tcap", "degree_rate"))
        self.S1, self.S2, self.DE, self.U = map(I, (self.s1, self.s2, self.delta, self.u))
        self.u2 = I(self.u*self.u)
        self.sqrt_count, self.log_count = 0, 0
        self.roots: dict[str, arb] = {}
        self.root_widths: list[Q] = []
        self.root_expansions = 0
        self.base = (self.ineg(self.s1)+self.ineg(self.s2)-self.ineg(Q(1))-2
                     +sum(2*S*(1-self.log(S)) for S in (self.S1, self.S2)))
        self.c = TARGETS["linear_sum_lower"]
        self.C = I(self.c)
        self.width = (1-self.s1-self.s2)/PANELS["angular"]
        self.K = self.width/2
        self.IK = I(self.K)
        self.nodes = [self.s1+self.s2+(Q(j)+Q(1, 2))*self.width
                      for j in range(PANELS["angular"])]
        self.es_q = [(self.u*self.u-x*x)**2/(2*self.u*self.u*x*x) for x in self.nodes]
        self.es = [I(e) for e in self.es_q]
        self.es_float = [float(e) for e in self.es_q]
        self.writer.write("header", schema="zeta3-arb-finite-witness-v1",
                          rational_encoding="integer or numerator/positive_denominator strings",
                          parameters={k: str(v) for k, v in PARAMETERS.items()},
                          precision_bits=precision, panels=PANELS,
                          linear_coefficient=str(self.c),
                          scope="Finite expression evaluations only; all analytic and asymptotic interpretation is separate.")
        for j, (node, e) in enumerate(zip(self.nodes, self.es_q)):
            self.writer.write("angular_charge", index=j, node=str(node),
                              weight=str(self.K), pole_distance=str(e))

    def sqrt(self, x: arb) -> arb:
        require(bool(x >= 0), "Square-root input is not certified nonnegative")
        result = x.sqrt()
        require(result.is_finite(), "Nonfinite square root")
        self.sqrt_count += 1
        return result

    def log(self, x: arb) -> arb:
        require(bool(x > 0), "Logarithm input is not certified positive")
        result = x.log()
        require(result.is_finite(), "Nonfinite logarithm")
        self.log_count += 1
        return result

    def mass(self, b: arb) -> arb:
        return (b+1-self.S1-self.S2-self.sqrt(1+b*b)
                +self.sqrt(self.S1*self.S1+b*b)+self.sqrt(self.S2*self.S2+b*b))/2

    def mass_float(self, b: float) -> float:
        return math.fsum((b, 1.0, -float(self.s1+self.s2), -math.hypot(1.0, b),
                          math.hypot(float(self.s1), b), math.hypot(float(self.s2), b)))/2

    def checked_root(self, family: str, parameter: Q, exact_function, float_function,
                     proposal_hi: float) -> arb:
        root_id = f"{family}:{parameter}"
        if root_id in self.roots:
            return self.roots[root_id]
        center = Q.from_float(proposed_root(float_function, 0.0, proposal_hi))
        radius = self.root_radius
        for expansion in range(10):
            left, right = max(Q(0), center-radius), center+radius
            left_value, right_value = exact_function(I(left)), exact_function(I(right))
            left_bounds, right_bounds = bounds(left_value), bounds(right_value)
            if left_bounds[1] < 0 < right_bounds[0]:
                result = rational_hull(left, right)
                self.roots[root_id] = result
                self.root_widths.append(right-left)
                self.root_expansions += expansion
                self.writer.write("root_bracket", id=root_id, family=family,
                                  parameter=str(parameter), left=str(left), right=str(right),
                                  left_residual=interval_record(left_bounds),
                                  right_residual=interval_record(right_bounds),
                                  enclosing_ball=interval_record(result),
                                  proposal_expansions=expansion)
                return result
            radius *= 10
        raise CertificateError(f"Could not verify endpoint signs for {root_id}")

    def b_for(self, v: Q) -> arb:
        require(0 <= v <= self.delta, "Physical parameter outside the specified range")
        if v == 0:
            return I(0)
        return self.checked_root("physical", v, lambda b: self.mass(b)-I(v),
                                 lambda b: self.mass_float(b)-float(v), 4.0)

    def angular_mass(self, B: arb) -> arb:
        return self.C*B/2+sum(self.IK*(1-1/self.sqrt(1+B/e)) for e in self.es)

    def angular_mass_float(self, B: float) -> float:
        return float(self.c)*B/2+float(self.K)*math.fsum(
            1-1/math.sqrt(1+B/e) for e in self.es_float)

    def angular_B(self, t: Q) -> arb:
        require(0 <= t <= self.Tcap, "Angular parameter outside the specified range")
        if t == 0:
            return I(0)
        return self.checked_root("angular", t, lambda B: self.angular_mass(B)-I(t),
                                 lambda B: self.angular_mass_float(B)-float(t), 1.0)

    def analytic_integrand(self, v: Q, b: arb) -> arb:
        if v == 0:
            return 2*(self.S1+self.S2)*self.log(I(2))
        V = I(v)
        return (sum(2*(S+V)*self.log(4*(S+V))-2*S*self.log(S+self.sqrt(S*S+b*b))
                    for S in (self.S1, self.S2))
                -4*V*self.log(b)+2*self.log((1+self.sqrt(1+b*b))/2))

    def linear_integrand(self, b: arb) -> arb:
        return self.U*b*b/((self.u2+b*b)*self.sqrt(self.u2+b*b))

    def ineg(self, a: Q) -> arb:
        A = I(a)
        return A*self.log(self.u2-A*A)+self.U*self.log((self.U+A)/(self.U-A))-2*A

    def gamma_at_b(self, b: arb) -> arb:
        v, uu = self.mass(b), self.sqrt(self.u2+b*b)
        def J(A: arb) -> arb:
            aa = self.sqrt(A*A+b*b)
            return (self.log((uu+aa)/(self.U+A))
                    -(A/self.U)*self.log((self.U*aa+A*uu)/(A*(uu+self.U))))
        return (self.base+4*v*self.log((self.U+uu)/b)
                +2*self.U*(self.log((b+uu)/self.U)-J(I(1))+J(self.S1)+J(self.S2)))

    def angular_F(self, t: Q, B: arb) -> arb:
        if t == 0:
            return I(0)
        return (I(t)*self.log(B/2)-self.C*B/2
                -2*sum(self.IK*self.log((1+self.sqrt(1+B/e))/2) for e in self.es))

    def finite_sum(self, family: str, n: int, step: Q, evaluate) -> tuple[Q, Q]:
        total_lo, total_hi = Q(0), Q(0)
        for k in range(n):
            parameter = k*step
            value = evaluate(parameter)
            lo, hi = bounds(value)
            self.writer.write("sample", family=family, index=k,
                              parameter=str(parameter), weight=str(step),
                              physical_root=(f"physical:{parameter}" if parameter else "exact_zero"),
                              value=interval_record((lo, hi)))
            total_lo += step*lo
            total_hi += step*hi
        self.writer.write("finite_sum", family=family, count=n, step=str(step),
                          enclosure=interval_record((total_lo, total_hi)))
        print(json.dumps({"stage": family, "samples": n, "lo": float(total_lo),
                          "hi": float(total_hi)}), flush=True)
        return total_lo, total_hi

    def run(self) -> dict:
        physical_endpoint = bounds(self.b_for(self.delta))
        require(physical_endpoint[1] < self.u, "Physical support enclosure does not lie below u")
        require(self.Tcap < min(self.delta, self.u/2), "Invalid auxiliary cutoff")
        physical_guard = bounds(self.mass(self.U))
        require(physical_guard[0] > self.delta, "Physical mass at u does not exceed delta")
        self.writer.write("guard_evaluation", family="physical_at_u", argument=str(self.u),
                          threshold=str(self.delta), value=interval_record(physical_guard))
        analytic = self.finite_sum("analytic", PANELS["analytic"],
                                   self.delta/PANELS["analytic"],
                                   lambda v: self.analytic_integrand(v, self.b_for(v)))
        require(analytic[0] >= TARGETS["analytic_sum_lower"], "Analytic finite sum misses its target")
        linear = self.finite_sum("linear", PANELS["linear"],
                                 (self.delta-self.Tcap)/PANELS["linear"],
                                 lambda v: self.linear_integrand(self.b_for(v)))
        require(linear[0] >= self.c > 0, "Linear finite sum misses its positive target")
        angular_cap = bounds(self.angular_B(self.Tcap))
        require(angular_cap[1] < 1, "Angular cap enclosure does not lie below one")
        angular_guard = bounds(self.angular_mass(I(1)))
        require(angular_guard[0] > self.Tcap, "Angular mass at one does not exceed Tcap")
        self.writer.write("guard_evaluation", family="angular_at_one", argument="1",
                          threshold=str(self.Tcap), value=interval_record(angular_guard))
        n, step = PANELS["response"], self.T/PANELS["response"]
        response_lo, response_hi = Q(0), Q(0)
        endpoint = None
        for k in range(n+1):
            t = k*step
            physical_parameter = self.delta-t
            gamma = bounds(self.gamma_at_b(self.b_for(physical_parameter)))
            angular = bounds(self.angular_F(t, self.angular_B(t)))
            value = gamma[0]+angular[0], gamma[1]+angular[1]
            self.writer.write("response_sample", index=k, parameter=str(t),
                              physical_parameter=str(physical_parameter),
                              physical_root=f"physical:{physical_parameter}",
                              angular_root=(f"angular:{t}" if t else "exact_zero"),
                              gamma=interval_record(gamma), angular_F=interval_record(angular),
                              value=interval_record(value),
                              weight=str(step if k < n else Q(0)))
            if k < n:
                response_lo += step*value[0]
                response_hi += step*value[1]
            else:
                endpoint = value
            if k and k % 256 == 0:
                print(json.dumps({"stage": "response", "completed": k, "panels": n}), flush=True)
        require(endpoint is not None, "Missing final endpoint")
        require(response_hi <= TARGETS["response_sum_upper"], "Response finite sum misses its target")
        require(endpoint[0] >= TARGETS["endpoint_lower"] > 0, "Endpoint lower target failed")
        require(endpoint[1] <= TARGETS["endpoint_upper"], "Endpoint upper target failed")
        self.writer.write("finite_sum", family="response", count=n, step=str(step),
                          enclosure=interval_record((response_lo, response_hi)))
        return {
            "physical_support_endpoint": interval_record(physical_endpoint),
            "angular_endpoint_cap": interval_record(angular_cap),
            "guard_evaluations": {"physical_at_u": interval_record(physical_guard),
                                  "angular_at_one": interval_record(angular_guard)},
            "analytic_finite_sum": interval_record(analytic),
            "linear_finite_sum": interval_record(linear),
            "response_finite_sum": interval_record((response_lo, response_hi)),
            "simple_endpoint": interval_record(endpoint),
            "root_bracket_count": len(self.root_widths),
            "largest_root_bracket_width": str(max(self.root_widths)),
            "root_radius_expansion_count": self.root_expansions,
            "elementary_evaluation_counts": {"sqrt": self.sqrt_count, "log": self.log_count},
        }


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--precision", type=int, default=192)
    parser.add_argument("--root-radius", type=Q, default=Q(1, 10**14))
    parser.add_argument("--output-dir", type=Path, default=HERE/"certificates/arb_simple")
    args = parser.parse_args()
    started = time.time()
    args.output_dir.mkdir(parents=True, exist_ok=True)
    partial = args.output_dir/"witnesses.jsonl.partial"
    witness_path = args.output_dir/"witnesses.jsonl"
    writer = WitnessWriter(partial)
    try:
        arithmetic = check_arithmetic()
        require(Q(arithmetic["arithmetic_constant"]) == TARGETS["arithmetic_constant"],
                "Arithmetic input does not match target")
        computation = Computation(writer, args.precision, args.root_radius)
        values = computation.run()
        # This last operation is only exact rational algebra.  It does not
        # assert that the mathematical transfer theorem has been formalized.
        slack = (TARGETS["analytic_sum_lower"]-TARGETS["arithmetic_constant"]
                 -TARGETS["response_sum_upper"])
        require(slack > 0, "The rational response slack is not positive")
        endpoint_upper = TARGETS["endpoint_upper"]
        result = PARAMETERS["degree_rate"]*endpoint_upper/(slack+PARAMETERS["T"]*endpoint_upper)
        require(result == Q(2225439040605380000, 447428816560392051),
                "Unexpected final rational expression")
        require(result < TARGETS["announced_upper"], "The rational comparison with 4.974 failed")
        writer.write("target_checks", targets={k: str(v) for k, v in TARGETS.items()},
                     response_slack=str(slack), final_rational_expression=str(result))
        writer.close()
        partial.replace(witness_path)
        summary = {
            "schema": "zeta3-arb-simple-summary-v1", "passed": True,
            "envelope": "Gamma_u(delta-t)+F(t)",
            "parameters": {k: str(v) for k, v in PARAMETERS.items()},
            "panels": PANELS, "precision_bits": args.precision,
            "initial_root_radius": str(args.root_radius),
            "targets": {k: str(v) for k, v in TARGETS.items()},
            "arithmetic": arithmetic, **values,
            "response_slack": str(slack), "final_rational_expression": str(result),
            "final_decimal_for_display_only": float(result),
            "witnesses": {"file": witness_path.name, "sha256": sha256(witness_path),
                          "bytes": witness_path.stat().st_size, "records": writer.counts},
            "environment": {"python": sys.version, "python_flint": flint.__version__,
                            "flint": flint.__FLINT_VERSION__, "platform": platform.platform()},
            "source_sha256": {"arb_simple.py": sha256(Path(__file__)),
                              "check_arithmetic.py": sha256(HERE/"check_arithmetic.py")},
            "wall_seconds": time.time()-started,
            "scope": "External finite numerical evidence. No Lean theorem, asymptotic estimate, integral comparison, or irrationality-measure theorem is established by this executable.",
        }
        (args.output_dir/"summary.json").write_text(json.dumps(summary, indent=2)+"\n")
        (args.output_dir/"failure.json").unlink(missing_ok=True)
        print(json.dumps({"passed": True, "final_rational_expression": str(result),
                          "display_decimal": float(result), "root_brackets": len(computation.roots),
                          "witnesses": str(witness_path), "wall_seconds": summary["wall_seconds"]}, indent=2))
    except Exception as error:
        writer.close()
        failure = {"passed": False, "type": type(error).__name__, "message": str(error),
                   "wall_seconds": time.time()-started, "partial_witnesses": str(partial)}
        (args.output_dir/"failure.json").write_text(json.dumps(failure, indent=2)+"\n")
        raise


if __name__ == "__main__":
    main()

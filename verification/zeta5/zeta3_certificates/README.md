# External finite certificates for the zeta(3) simple envelope

This directory implements the **external numerical branch** of the hybrid
formalization. The new Arb replay succeeds with the original constants and
reproduces the exact rational expression

\[
\frac{2225439040605380000}{447428816560392051}<\frac{2487}{500}=4.974.
\]

This calculation is not itself a Lean proof of an irrationality-measure bound.
It supplies finite numerical evidence for the mathematical implication checked
in `Zeta3.FinalAudit`. The final hybrid theorem is in
`Zeta3.Hybrid.Verified`, with its external assumptions printed explicitly. In particular, no asymptotic rate, integral comparison,
local valuation theorem, prime number theorem application, spectral theorem,
or transfer theorem is an output assumption of this program.

## Replay

From the `zeta5` directory:

```bash
python3 -m venv zeta3_certificates/.venv
zeta3_certificates/.venv/bin/python -m pip install -r zeta3_certificates/requirements.txt
zeta3_certificates/.venv/bin/python zeta3_certificates/arb_simple.py
zeta3_certificates/.venv/bin/python zeta3_certificates/verify_export.py
zeta3_certificates/.venv/bin/python zeta3_certificates/test_certificates.py
```

The recorded environment uses Python 3.12.14, python-flint 0.9.0, and its bundled
FLINT 3.6.0. The default precision is 192 bits, with a separate 256-bit run
available in `certificates/arb_simple_256/`. Do not run with Python `-O`: the
pinned reference profile uses assertions, and the checker rejects that mode.

The replay uses the **simple** response `Gamma_u(delta - t) + F(t)` only. It
does not evaluate the optional Green-function response, the compressed physical
root, or its quadratic penalty. It uses no SciPy, NumPy, or mpmath dependency.

## What is certified externally

All parameters are exact rationals:

| Parameter | Value |
| --- | ---: |
| `s1`, `s2` | `2/25`, `8/25` |
| `delta` | `51/50` |
| `u` | `1000001/1000000` |
| `T`, `Tcap` | `17/125`, `7/50` |
| Degree rate | `17/25` |

The fixed numerical targets are:

| Finite quantity | Required bound |
| --- | ---: |
| Arithmetic constant, after adding the explicit tail-expression value | `<= 1926282169226183949/500000000000000000` |
| 8,192-term analytic left sum | `>= 300854183181/62500000000` |
| 2,048-term linear left sum | `>= 3835733171/31250000000` |
| 1,024-term simple-response left sum | `<= 191284115113/200000000000` |
| Simple response at `T` | `>= 6545408942519/1000000000000` |
| Simple response at `T` | `<= 6545408942957/1000000000000` |

Both precision runs meet these exact targets. The rational subtraction gives
the positive slack `2341008439316051/500000000000000000`.

The 128 angular nodes, weights and pole distances are exact rationals. The
run checks 12,180 **distinct** positive root brackets after caching repeated
arguments. It also handles the zero endpoint explicitly. All proposed
positive brackets have width `1/50000000000000` in the recorded runs; none
required widening.

### Exact input, rigorous real enclosures, exact output

`I` accepts only Python integers or `Fraction` values. Rational inputs are
converted through FLINT `fmpq`, then enclosed by Arb. Python binary floats are
used only by the untrusted bisection proposer. Its proposed midpoint is
converted to its exact binary rational value, and the following two signs
must be certified by Arb before any bracket is used:

\[
f(a)<0<f(b).
\]

The code does not call Arb's general Newton root-refinement routines. The
mathematical continuity and strict monotonicity needed to identify the unique
root belong to the Lean branch.

For each stored Arb ball, its exact midpoint and radius are extracted as
integer mantissa/power-of-two pairs. Their exact rational difference and sum
are exported. No decimal formatting is used to derive proof bounds.
Square-root and logarithm calls require certified domains and finite output.
Sample intervals are aggregated using exact rational arithmetic.

## Data format and Lean interface

`certificates/arb_simple/summary.json` contains small aggregate data, environment
information, source/witness hashes and the final exact rational comparison.
`witnesses.jsonl` contains one JSON object per record, with this schema:

| Record kind | Meaning |
| --- | --- |
| `header` | Exact parameters, panel counts, fixed coefficient and precision |
| `angular_charge` | Index, rational midpoint, weight and pole distance |
| `root_bracket` | Family and parameter; rational endpoints; residual enclosures at each endpoint; enclosing root ball |
| `guard_evaluation` | Direct bounds proving physical mass at `u` exceeds `delta` and angular mass at `1` exceeds `Tcap` |
| `sample` | Analytic or linear node, weight, physical-root reference and value enclosure |
| `response_sample` | Response node, both root references, separate Gamma/F enclosures and their exact sum |
| `finite_sum` | Exact sum of the displayed interval endpoints and weights |
| `target_checks` | Fixed target comparisons and final rational expression |

Every rational is a canonical JSON **string**, either an integer or
`numerator/positive_denominator`; JSON floating-point numbers are never used
for mathematical evidence. Intervals are objects with `lo` and `hi` fields.
Floating-point display values in the summary are explicitly marked as such.

The intended finite external interface consists of the reported **real
expression enclosures** at the listed nodes and root endpoints, together
with the exact partition evidence. The Lean development proves how the fixed finite evidence implies root
inclusion, the required finite-grid/integral comparisons, and the subsequent
analytic and arithmetic rates. `Zeta3.Certificate.FiniteNumerics` narrows the
Arb interface to seven fixed real inequalities; the separate arithmetic
interface is one closed finite Boolean. The export does not replace those
theorems.

An even narrower future interface can replace the composed-expression
enclosures with certified primitive logarithm/square-root witnesses. That
would require additional export and a proved interval evaluator. No claim is
made that this narrower interface has already been implemented.

### Trust boundary

`arb_simple.py` is an external rigorous-numerics computation. Its real-function
enclosures depend on FLINT/Arb, its build and dependencies, python-flint, and
the correctness of the formula translation in this script. A hash pins an
artifact's identity; it is not a mathematical proof of the artifact.

`verify_export.py` uses only the Python standard library. It checks the
complete required root set, all coordinates/references, strict endpoint-sign
claims, interval ordering, exact weighted sums, fixed targets, and the final
rational comparison. It **does not independently establish Arb's claimed
real-function inclusions**. That is precisely the external numerical boundary
of this hybrid stage. Importing the file into Lean or calling a native/FFI
operation does not turn it into a kernel proof.

Official background: [FLINT correctness guarantees](https://flintlib.org/doc/guide/correctness/guarantees.html),
[ball arithmetic](https://flintlib.org/doc/guide/types/ball-arithmetic.html),
and [predicates](https://flintlib.org/doc/arb/predicates.html).

## Exact arithmetic cells

`reference/` preserves unmodified copies of the earlier exact-arithmetic
source, its 6,752-cell table and its original aggregate JSON. The pinned source
hash is `dc7b2b828fed0c2757e21bd9e59142a0475a462314541c0114d991dc1f0f98ab`.

`check_arithmetic.py` independently checks interval coverage, all relevant
floor and guard boundaries, exact affine areas and their upward rounding.
It also re-evaluates the profile on every accepted cell using the pinned
canonical source, whose affine branch comparisons check both endpoints.
This is a separate checker of supplied cells, **not an independent derivation
of the mathematical profile**. Floor constancy is checked on open cells;
the measure-zero treatment of boundaries belongs to the mathematical integral
argument. The exact value `51/6250` is the expression `4*delta/500`; the theorem
that it bounds the omitted prime contribution is not asserted by the script.

## Validation and failures

The focused test suite checks exact rational input/output, hulls, nonfinite
rejection, real-function domains, rejection of a deliberately wrong root
proposal, rejection of corrupted root signs/sample weights/sum records,
rejection of a corrupted affine profile, and rejection of optimized Python
execution. Results are recorded in `certificates/test_report.json`.

On failure, `arb_simple.py` records `failure.json` and retains a `.partial`
witness file. A complete witness is promoted to `witnesses.jsonl` only after
all target checks succeed. The original research scripts and certificate
files outside this directory are never modified.

## End-to-end hybrid gate

`verify_hybrid.py` reproduces the external finite computations and checks the
actual final Lean modules. Run it from a stable checkout after preparing the
Lean dependencies and the Python environment above:

```bash
zeta3_certificates/.venv/bin/python zeta3_certificates/test_hybrid_gate.py
zeta3_certificates/.venv/bin/python zeta3_certificates/verify_hybrid.py \
  --toolchain-bin /absolute/path/to/lean-4.33.1-linux/bin \
  --output-dir zeta3_certificates/certificates/hybrid_validation
```

The output directory must be new. If `--output-dir` is omitted, the driver
creates a timestamped directory with a random suffix. It records each command,
its exit status, timing, full output and log hash, and maintains `report.json`
with `passed: false` until every check has completed. A failed command, timeout,
changed source hash, missing axiom report or unexpected axiom rejects the run.
The default subprocess timeout is 30 minutes, adjustable with
`--timeout-seconds`.

The gate performs these checks in order:

1. Verify the pinned semantic-review manifest itself, all of its source and
   witness hashes, its exact seven-field mapping and its positive rational
   slacks. The manifest cannot be silently regenerated by this driver.
2. Check the Lean version and source commit, and python-flint/FLINT versions.
3. Verify the stored 192-bit export, make a fresh 256-bit Arb replay in the new
   output directory, and check the complete fresh export independently for
   exact data consistency.
4. Build the finite-profile dependency and execute
   `CheckFiniteProfile.lean`, checking the **5,949 cells of the actual Lean
   profile**. These use a separate profile representation with the exact
   first-feature rank; the 6,752 reference cells remain with the original
   numerical calculation.
5. Build `Zeta3.FinalAudit` and `Zeta3.Hybrid.Verified`, then run each source file
   with `lean --trust=0`. This option type-checks imported modules as well.
6. Parse the named final theorems' axiom reports. The conditional mathematical
   core must have only `propext`, `Classical.choice` and `Quot.sound`. Each
   hybrid endpoint must have exactly the seven named `ExternalArb` assumptions
   and, in the default mode, the one named
   `ExternalArithmetic.arithmeticFiniteCheck_eq_true` assumption, in addition
   to the standard axioms. Every other axiom, including `sorryAx` or a native
   reduction axiom, is rejected.
7. Recheck the semantic pin and confirm that project source files stayed
   unchanged throughout the replay. The recorded source snapshot detects
   concurrent edits; it is distinct from the independently reviewed semantic
   identity and does not itself prove any theorem.

`--arithmetic-mode kernel` is a deliberately narrower alternate allowlist.
It accepts the seven Arb assumptions and rejects the external arithmetic
axiom. This mode may be used only when the Lean arithmetic Boolean has actually
been proved in the kernel and the final theorem's printed dependencies reflect
that fact. It is not a flag that upgrades runtime evidence into a proof.

The two final module families make the trust boundary explicit. The core
proves the result **from finite evidence** with standard Lean axioms. The hybrid
connector supplies that finite evidence as explicitly named external
assumptions. `--trust=0`, successful builds, file hashes and a successful gate
do not remove those assumptions. No asymptotic estimate, rank bound, integral
comparison, valuation theorem or irrationality statement is permitted as an
external premise.

`test_hybrid_gate.py` exercises rejection of changed source/manifests,
missing/duplicate reports, `sorryAx`, native-reduction or mathematical axioms,
changed arithmetic trust boundaries, process errors and timeouts. It does not
run Lean, Arb or the full gate. `verify_export.py --report PATH` lets the gate
write validation reports in its new output directory without modifying the
stored witness directory.

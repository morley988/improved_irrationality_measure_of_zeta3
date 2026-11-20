ZETA(3): COMPLETED HYBRID LEAN VERIFICATION
First stage, 19 November 2026

STATUS
======
The complete hybrid endpoint is built and audited. The final reproduction
gate passed with exit status zero at 09:28:19 UTC. It establishes the usual
rational-approximation upper-bound formulation for

  mu(zeta(3)) <= 2225439040605380000 / 447428816560392051
             = 4.973839319768086... < 4.974.

This is HYBRID verification. The mathematical implication is checked in Lean;
seven fixed real-expression inequalities are supported by external Arb
computations, and one closed finite rational Boolean is checked by external
execution of the actual Lean checker. These eight assertions are explicitly
declared axioms in two optional connector modules. They are not represented
as Lean kernel proofs. No mathematical rank, valuation, integral, asymptotic,
or irrationality statement is left as an external assumption.

The earlier intermediate checkpoint has been superseded by this completed
first-stage package. All source files required from the original project are
included, together with the new zeta(3) development. External dependency
sources, compiled caches, and the Lean toolchain are fetched using the pinned
lockfile; these large standard build dependencies are not bundled.

EXACT FINAL STATEMENT
====================
The principal declaration is

  Zeta3.Hybrid.zeta3_irrationality_exponent_bound :
    Zeta3.Transfer.HasApproximationExponentLE
      (riemannZeta 3).re Zeta3.Parameters.target

The predicate means that for every real nu strictly above the displayed
rational target, there is a natural Q such that for every natural q >= Q
and every integer p,

  q^(-nu) <= abs((riemannZeta 3).re - p/q).

The statement concerns Mathlib's ordinary Riemann-zeta function. It applies
to all sufficiently large denominators and all integer numerators, with no
selected-subsequence or coprimality restriction. The development also proves
ordinary Irrational (riemannZeta 3).re and an explicit rational-separation
statement. The exact comparison of the rational target with 2487/500 is
proved internally by rational arithmetic.

Reviewer entry points:

  zeta5/Zeta3/Endpoint/FiniteEvidence.lean
  zeta5/Zeta3/Hybrid/Verified.lean
  zeta5/Zeta3/FinalAudit.lean
  zeta5/Zeta3/Transfer/Approximation.lean

The core theorem in Endpoint/FiniteEvidence.lean takes only the two finite
numerical evidence structures. Its transitive axiom set is contained in
Lean's standard foundational axioms:

  propext, Classical.choice, Quot.sound.

The closed hybrid declarations add exactly the following eight assertions:

  Zeta3.Hybrid.ExternalArb.analytic_sum_lower
  Zeta3.Hybrid.ExternalArb.physical_guard
  Zeta3.Hybrid.ExternalArb.linear_sum_lower
  Zeta3.Hybrid.ExternalArb.angular_guard
  Zeta3.Hybrid.ExternalArb.response_sum_upper
  Zeta3.Hybrid.ExternalArb.endpoint_lower
  Zeta3.Hybrid.ExternalArb.endpoint_upper
  Zeta3.Hybrid.ExternalArithmetic.arithmeticFiniteCheck_eq_true

There is no sorryAx dependency, no native_decide assertion, and no externally
postulated asymptotic theorem in the final dependency set.

WHAT THE MATHEMATICAL FORMALIZATION COVERS
========================================
The proof uses the actual cubic Pearson determinant and its actual primitive
integer polynomial. The following are proved, rather than assumed:

1. The cubic moments, Stieltjes identity, positivity, determinant identity,
   integer polynomial construction, and degree bound.
2. Pearson nullity and the uniform real-root multiplicity bound of two,
   providing a nonzero Hasse derivative at every rational approximant.
3. First and second restriction ranks, residue reductions, two-kernel basis
   transport, parity-sensitive local ranks, and determinant valuations.
4. The comparison of those actual valuations with the finite piecewise
   arithmetic profile, including small primes, endpoint strips, floor
   errors, and the prime-number-theorem passage to the global rate.
5. Physical and angular potential comparisons, finite quadrature error
   directions, complex response bounds, spectral trial spaces, eigenvalue
   products, determinant decay, and their limiting error estimates.
6. Cauchy bounds, bounded-order integer-polynomial transfer, all-denominator
   rational separation, and the final exact target calculation.

The independent interface review specifically checked N=50*n, scale=2500*n^2,
degree <=34*n+1, the actual response slope, and the fact that multiplicity two
affects a lower-order Cauchy error rather than multiplying the final exponent.
It also checked the identity with the ordinary zeta value and the positive
rational normalization (the normalized polynomial is the integer object).

This development uses substantial existing formal mathematics: prime number
theory, integration, complex Cauchy estimates, and finite-dimensional spectral
theory. It is not an elementary-only formalization. See the construction-to-
endpoint audit for the exact interfaces and scope.

FINITE NUMERICAL EVIDENCE
========================
The seven Arb assertions consist of three fixed finite-sum bounds, two domain
guards for the inverse functions, and two endpoint bounds. The sum sizes are
8192, 2048, and 1024. The angular approximation uses 128 charges. The retained
witnesses include 12,180 positive-root brackets with interval sign evidence.

The finite arithmetic certificate has 5,949 rational cells. The actual Lean
runtime checker validates coverage, rational area, floor bands, parity
choices, and affine branch choices for the actual Lean data. Its soundness
implication is kernel checked; the Boolean's successful runtime evaluation
remains the eighth explicit hybrid assertion.

The new full-cell arithmetic upper bound, including the exact small-prime
tail 51/6250, is

  963141084613091877 / 250000000000000000
  = 3.852564338452367508.

It is slightly sharper than the paper's rounded upper bound. The final proof
uses the paper's bound through an internally proved exact comparison. The
older 6,752-cell reference calculation is preserved as provenance; it is not
substituted for checking the actual 5,949-cell Lean table.

The export checker verifies exact dyadic/rational consistency, root and
sample references, sums, and target comparisons. It does not independently
prove the real-function inclusions. Those inclusions rely on Arb/FLINT, the
Python binding, and the reviewed evaluator. The correspondence of that
evaluator's formulas and grids to the Lean definitions is recorded in
FINITE_SEMANTIC_AUDIT.md and pinned by the semantic manifest.

FINAL VALIDATION EVIDENCE
=========================
The endpoint build completed successfully (4,231 build jobs). The subsequent
frozen-source gate ran from 09:27:03 to 09:28:19 UTC in 75.42464 seconds.

  Pinned semantic manifest and reviewed input hashes       PASS
  Lean 4.33.1 version and compiler commit                  PASS
  python-flint 0.9.0 / FLINT 3.6.0                         PASS
  Stored 192-bit certificate export                       PASS
  Fresh 256-bit Arb evaluation                            PASS
  Fresh export's exact consistency checks                 PASS
  Actual Lean runtime arithmetic checker, 5,949 cells      PASS
  Final mathematical and hybrid module builds             PASS
  Core endpoint replay with --trust=0                     PASS
  Hybrid endpoint replay with --trust=0                   PASS
  Exact external-axiom allowlist                          PASS
  Sources unchanged throughout the replay                 PASS
  All 14 dependency revisions and tracked-source checks   PASS

The fresh Arb evaluation took about 12.4 seconds; the actual Lean arithmetic
runtime check took about 27.5 seconds. These are warm-environment replay times,
not estimates for a new machine's dependency installation or cold build.

There are also 11 certificate-integrity/domain mutation tests and 15 final-
gate tests. They cover changed hashes, wrong root signs or weights, inconsistent
sums, missing/duplicate axiom reports, disallowed axioms, process failures,
and timeouts. They check connector behavior, not substitute mathematics.

Primary machine-readable evidence:

  zeta5/zeta3_certificates/certificates/hybrid_validation/report.json
  zeta5/zeta3_certificates/certificates/hybrid_validation/source_snapshot.json
  zeta5/zeta3_certificates/certificates/dependency_identity_audit.json

Final gate report SHA-256:
  2fe00234a10f1de633fb5afcb67219b145782264dd664c505179d19195dd1d09
Frozen source snapshot SHA-256:
  333e87a8ceacfae00c9bbab6443463c4389a5ca78f5cdada253492edf36e7678

REPRODUCING THE HYBRID RESULT
============================
Use a Linux environment with Git, Python 3, Elan/Lean, a C/C++ toolchain,
network access for pinned dependencies and caches, and several gigabytes
of disk space. The recorded Python version was 3.12.14.

After extracting this archive, run from its zeta5 directory:

  elan toolchain install leanprover/lean4:v4.33.1
  lake -f lakefile.zeta3.toml exe cache get
  python3 -m venv zeta3_certificates/.venv
  zeta3_certificates/.venv/bin/python -m pip install -r zeta3_certificates/requirements.txt
  lake -f lakefile.zeta3.toml build Zeta3.FinalAudit Zeta3.Hybrid.Verified
  zeta3_certificates/.venv/bin/python zeta3_certificates/test_certificates.py
  zeta3_certificates/.venv/bin/python zeta3_certificates/test_hybrid_gate.py
  zeta3_certificates/.venv/bin/python zeta3_certificates/verify_hybrid.py --output-dir zeta3_certificates/certificates/replay_local

The replay output directory must not already exist. If the pinned lean/lake
binaries are not on PATH, pass --toolchain-bin /absolute/path/to/bin to the
driver. Keep the pinned lake-manifest.json; do not run lake update. Do not
run the Python checkers with -O. Do not overwrite the reviewed 192-bit witness
files: the driver pins their identities and writes fresh output separately.

The final gate rejects unlisted axioms, a changed semantic manifest, changed
reviewed formulas, missing reports, unsuccessful subprocesses, or source edits
during replay. Its default arithmetic mode is external. The optional kernel
mode is reserved for a later actual internal proof; selecting it on this
release fails the axiom check and does not remove an assumption.

The archive's FILE_MANIFEST.json hashes every bundled payload file other than
the manifest itself. The original Zeta5 README and its historical evidence
are preserved unchanged; use this report and the Zeta3 final gate for the
current zeta(3) verification status.

PROVENANCE
==========
Base repository:
  https://github.com/morley988/zeta5-independent-lean.git
Base revision:
  7cccd34d0f72cffa7fc05aafb133940c2386513b
Lean version / compiler commit:
  4.33.1 / 819816b2e0a3bf405af45ae5c7af2491d8f5bee6
Mathlib revision:
  0df444a360eaa60ab8c11dca51a86af692955474
PrimeNumberTheoremAnd revision:
  650d31264be65f4cd6e70c45d8b25d86d482a761

The new work is supplied as a source addition to that exact base, not as a
claim that it has already been committed or published upstream. The package
includes the 234 original tracked zeta5 files unchanged. The alternate Lake
configuration adds the Zeta3 library without modifying the original pins.

TIME SPENT AND REVISED ESTIMATE
==============================
The authorized work started at 06:26:26 UTC. The complete final gate passed
at 09:28:19 UTC: approximately three hours of elapsed work, followed by
packaging. This is elapsed time with parallel assistant workers and reuse
of the existing checked Zeta5 project, not a human-expert-hour benchmark.

The hybrid milestone is complete; no further mathematical formalization is
needed to obtain the stated hybrid endpoint. The earlier 15-40-hour estimate
for that milestone was conservative for the amount of reusable infrastructure
available in this project.

For a subsequent fully internal numerical stage, a provisional estimate is
10-25 additional active assistant working hours, with roughly 16-20 hours as
a planning allowance. These are engineering estimates, not measurements:

  Chunked exact kernel proofs for the finite arithmetic table: 1-4 hours.
  Kernel-checked interval/root/log certificates for seven bounds: 7-16 hours.
  Integration, resource tuning, fresh checks and packaging: 2-5 hours.

The components overlap, so the total is not a sum of independent worst cases.
Confidence is lower for the interval-certification work than for the finished
mathematical proof. Large proof terms or kernel evaluation costs could extend
that estimate. A human Lean specialist's time has not been benchmarked here;
the observed parallel-assistant elapsed time should not be treated as such a
benchmark.

A small monolithic decide+kernel arithmetic pilot was stopped by its
conservative aggregate-memory guard after 8.561 seconds. No kernel proof was
produced, and the original hybrid path remains unchanged. Aggregated RSS can
double-count shared imported pages, so this is not a measurement of an
intrinsic five-GiB requirement. The pilot supports trying chunked checking in
the later stage. Its source and logs are archived outside the Lean namespace;
there is no unfinished optional Lean module in the delivered development.

To remove external trust later, Arb may continue generating candidate
witnesses. The change required is to prove their validity in Lean and replace
the eight assertions by the resulting theorems. The already verified
mathematical implication and target statement can remain the same.

ACCURATE DESCRIPTION OF THIS MILESTONE
====================================
The mathematical derivation of the bound for mu(zeta(3)) has been formalized
in Lean. The resulting hybrid theorem depends only on eight explicitly
identified finite numerical assertions, checked by Arb and exact arithmetic.
It has passed an end-to-end numerical replay and transitive axiom audit.
It is not yet a fully kernel-verified numerical proof.

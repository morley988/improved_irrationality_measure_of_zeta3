# Construction-to-endpoint audit

Date: 2026-11-19. Scope: independent, read-only review of the proof interfaces,
definitions, index conversions, and mathematical premises connecting the
concrete cubic determinant to the final zeta statement.

## Completed build and scope of this review

The reviewed source supplies every mathematical construction, rank, valuation,
analytic, asymptotic, and Diophantine-transfer premise of the endpoint.
The only remaining inputs to the core endpoint are the two finite numerical
evidence structures described below. No additional mathematical premise was
found in the reviewed chain.

The complete core and hybrid endpoints **compiled successfully at 09:22 UTC
on 2026-11-19**, with exit status zero and `Build completed successfully (4231
jobs)`. The observed log is
`/workspace/scratch/707ccee40cd4/zeta3_hybrid_stage1/logs/build-final-hybrid-1.log`.
Its `Zeta3.FinalAudit` output reports only standard foundational axioms for the
core finite-evidence implications. Its `Zeta3.Hybrid.Verified` output reports
exactly the eight numerical assertions listed below, in addition to those
foundational axioms, for each of the exponent, irrationality, and rational
separation theorems. None has a `sorryAx` dependency.

This independent review inspected the completed build output and re-read the
final endpoint and transfer predicate. It did not repeat numerical formula/grid
validation or launch a duplicate build. The separate **fresh numerical replay
and trust-level-zero validation gate also passed**, with exit status zero. Its
recorded interval was 09:27:03–09:28:19 UTC on 2026-11-19, taking 75.42 seconds.
The authoritative machine-readable record is
`zeta3_certificates/certificates/hybrid_validation/report.json`.

| Fresh validation component | Observed result |
|---|---|
| Stored 192-bit certificate export checks | Passed |
| Fresh 256-bit Arb replay and exact export checks | Passed |
| Actual Lean runtime arithmetic check | All 5,949 cells passed |
| Core endpoint at trust level zero | Passed; standard foundational axioms only |
| Hybrid endpoint at trust level zero | Passed; exactly eight disclosed numerical assertions plus standard axioms |
| Frozen-source comparison | Passed; source hashes stable throughout replay |

The arithmetic replay explicitly checked coverage, area, floor guards, parity
choices, and affine branches. Its runtime success remains external evidence for
the closed Boolean; the replay did not turn that numerical assertion into a
kernel proof. The two trust-level-zero logs are `09_core_trust_zero.log` and
`10_hybrid_trust_zero.log` in the same validation directory. This review checked
their axiom output and the actual finite-profile result as well as the report.

### Source version and toolchain

- Base repository: `morley988/zeta5-independent-lean`, revision
  `7cccd34d0f72cffa7fc05aafb133940c2386513b`.
- Toolchain: `leanprover/lean4:v4.33.1`; observed executable version is Lean
  `4.33.1`, `x86_64-unknown-linux-gnu`, release commit
  `819816b2e0a3bf405af45ae5c7af2491d8f5bee6`.
- Build configuration: `lakefile.zeta3.toml`; the original toolchain and
  dependency pins were retained. The SHA-256 of `lake-manifest.json` is
  `f9e7d96aec7f57bca708fd47707d127bff4691bd401e4000d33b5f80f1ff5e03`.
- The new development is a working-tree addition to that base revision. Its
  frozen file-level source version is recorded in
  `zeta3_certificates/certificates/hybrid_validation/source_snapshot.json`,
  whose SHA-256 at this review is
  `333e87a8ceacfae00c9bbab6443463c4389a5ca78f5cdada253492edf36e7678`.
  This identifies the reviewed new sources without claiming they were already
  part of the base commit or publicly published.

## Exact object and target

The family is `Zeta3.Construction.windowIntegerPolynomial n : ℤ[X]`, obtained
from the actual asymmetric rational determinant by primitive normalization.
Its parameters are

| Quantity | Exact value |
|---|---:|
| Physical index `N` | `50*n` |
| First window start | `4*n` |
| Second window start | `16*n` |
| Matrix size | `51*n` |
| Proved polynomial degree bound | `34*n + 1` |
| `Zeta3.Analysis.windowScale n` | `(50*n)^2 = 2500*n^2` |
| Uniform real-root multiplicity bound | `2` |

`windowNormalizer n` is a **positive rational multiplier**; it need not be an
integer or exceed one. The normalized polynomial is the integer object. The
signed rational prime-product argument correctly bounds its normalizer, and
`windowIntegerPolynomial_response_identity` proves the response identity for
this same polynomial. The normalization and basis-change constants cancel in
that identity.

The final target is the ordinary value `(riemannZeta 3).re`.
`Zeta5.Endpoint.realZeta_eq_re` identifies the real series with this value using
Mathlib's convergent-series identity, without a zeta-irrationality assumption.

The exact bound is

\[
\mu_* = \frac{2225439040605380000}{447428816560392051}
       < \frac{2487}{500}=4.974.
\]

`Zeta3.Parameters.target_exact` proves the rational expression used for this
bound, and `Zeta3.Parameters.target_lt_4974` proves the strict comparison by
kernel-checked rational arithmetic.

The endpoint uses `Zeta3.Transfer.HasApproximationExponentLE`. Explicitly, it
asserts that for every real `ν > μ_*`, all sufficiently large natural
denominators `q`, and every integer numerator `p`,

\[
q^{-\nu}\leq\left|\operatorname{Re}\zeta(3)-p/q\right|.
\]

There is no coprimality or selected-subsequence restriction. This is the usual
eventual approximation formulation of an upper bound for the irrationality
exponent. The development separately derives ordinary `Irrational` and has a
bridge excluding Mathlib's `LiouvilleWith ν` for `ν > μ_*`.

The predicate is not vacuous: `μ_*` is a fixed finite real number, exponents
strictly above it exist, and the natural-number `atTop` filter contains all
sufficiently large positive denominators. The displayed rational-separation
theorem makes these quantifiers explicit. The proved irrationality consequence
also rules out an interpretation that would permit exact rational values.

## Scaling and bounded derivatives

Write `a = response cutoff`, `I = ∫ t in 0..cutoff, response t`, and
`T = cutoff = 17/125`. The concrete transfer invocation uses

| Transfer parameter | Supplied value |
|---|---:|
| Degree slope | `34` |
| Degree intercept | `1` |
| Radius slope | `50*a` |
| Small-value quadratic decay | `2500*(analyticLower - arithmeticUpper)` |
| Response quadratic growth | `2500*(I - T*a)` |
| Maximum Hasse derivative order | `B = 2` |

Consequently its leading quotient is exactly

\[
\frac{34\cdot50a}{2500(C_{\rm an}-C_{\rm ar}-I+Ta)}
=\frac{(17/25)a}{C_{\rm an}-C_{\rm ar}-I+Ta}.
\]

The error conversion from `E/windowScale → 0` to `E/n² → 0` explicitly
multiplies by `2500`. The actual slope `a` is retained in the response radius
and main rate until the final comparison. The positive lower enclosure for
`a`, the positive `savingLower`, and the proved monotonicity of the quotient
justify substituting `slopeUpper` at that last step.

The bound `B=2` supplies a nonzero Hasse derivative even if the polynomial
vanishes at a rational approximant. Cauchy's estimate adds only the term
`a*B*n` in the abstract transfer. This is lower order than the quadratic
stage exponent and does **not** multiply the leading irrationality bound.
The factor two in the complex response radius is the exact margin needed to
center a Cauchy circle at a nearby rational point. The empty stage `n=0` is
covered by the concrete nonzero and multiplicity results; asymptotic estimates
use positive stages eventually.

## Closure of mathematical premises

The arithmetic route is

`actual restriction ranks and local parity caps`
→ `actual first/second determinant valuation bounds`
→ `FullProfileComparison`
→ `finite-cell prime majorization`
→ `ActualArithmeticRate`.

The cell route covers `[1/500, 67/25]`. Its area includes the explicit small
prime-tail allowance `51/6250`. The uniform per-prime error and fixed-width
boundary strips are proved negligible on the quadratic scale. Thus the
`p+2 < cell.hi*N` restriction used to identify the exact restriction depths is
accounted for; it does not leave an unhandled family of boundary primes.

The analytic route proves the physical determinant decay and the actual
complex response bound, including spectral trial spaces, eigenvalue bounds,
finite products, and their limiting error. `CertifiedResponseRate` closes
`ActualResponseRate` from finite numerical evidence alone.

`ConcreteRateTransfer` then uses the actual integer polynomial, its nonzero
value at zeta, its degree bound, and its proved multiplicity bound. Its generic
rate premises are discharged by `Endpoint.FiniteEvidence`; they are not fields
of a numerical certificate.

Key reviewer entry points:

- `Zeta3.Construction.Rational.windowIntegerPolynomial_rootMultiplicity_le_two`
- `Zeta3.Construction.windowIntegerPolynomial_natDegree_le_effectivePoles`
- `Zeta3.Analysis.windowIntegerPolynomial_response_identity`
- `Zeta3.Endpoint.actualResponseRate_of_finiteEvidence`
- `Zeta3.Endpoint.actualArithmeticRate_of_finiteEvidence`
- `Zeta3.Endpoint.riemannZeta_three_exponent_le_of_finiteEvidence`
- `Zeta3.Endpoint.riemannZeta_three_rational_separation_of_finiteEvidence`
- `Zeta3.Hybrid.zeta3_irrationality_exponent_bound`
- `Zeta3.Hybrid.zeta3_irrational`
- `Zeta3.Hybrid.zeta3_rational_separation`

## Exact hybrid trust boundary

The optional external connectors designate exactly these eight nonstandard
assertions:

1. `Zeta3.Hybrid.ExternalArb.analytic_sum_lower`
2. `Zeta3.Hybrid.ExternalArb.physical_guard`
3. `Zeta3.Hybrid.ExternalArb.linear_sum_lower`
4. `Zeta3.Hybrid.ExternalArb.angular_guard`
5. `Zeta3.Hybrid.ExternalArb.response_sum_upper`
6. `Zeta3.Hybrid.ExternalArb.endpoint_lower`
7. `Zeta3.Hybrid.ExternalArb.endpoint_upper`
8. `Zeta3.Hybrid.ExternalArithmetic.arithmeticFiniteCheck_eq_true`

The first seven are fixed finite real-expression inequalities, supported by
the separately documented Arb replays. The eighth records a runtime result
for a closed Boolean checking the actual 5,949 Lean cells, rational coverage,
area, floor bands, and branch choices. Its soundness implication is proved in
Lean. A runtime evaluation of that Boolean is **not** a kernel proof of its
value. Both connectors label their assertions as axioms explicitly; the core
conditional endpoint does not import either connector.

The completed build's axiom output shows exactly those eight named assertions
and Lean's standard foundational axioms (`propext`, `Classical.choice`,
`Quot.sound`). It shows neither `sorryAx` nor an additional mathematical
assumption. The fresh trust-level-zero validation gate reproduced that exact
dependency set for the unchanged sources. The formal mathematical implication is kernel checked;
the finite numerical premises remain the explicitly identified hybrid trust
boundary until their assertions are replaced by internal proofs.

The development is not elementary-only: it uses proved PNT, measure and
integration results, complex Cauchy estimates, and finite-dimensional spectral
theory. The pinned upstream PNT package contains unrelated admitted lemmas in
`Wiener.lean`; existing compiled axiom reports for the actual
`chebyshev_asymptotic` and `theta_ratio_limit` dependencies contain only the
standard foundational axioms. Their unrelated source warnings do not imply a
dependency on an admitted theorem here.

No vacuity, target-identity, sign, scaling, index, normalization, or undisclosed
mathematical-premise issue was found in the final re-review. The completed build,
axiom reports, and successful fresh validation gate establish the hybrid theorem
with the stated numerical trust boundary. The independent final verdict is:
**the mathematical implication and its concrete application are formally
verified, with exactly the eight disclosed finite numerical assertions remaining
external.** An announcement should describe this as hybrid verification; fully
internal verification of the finite numerical assertions is a separate task.

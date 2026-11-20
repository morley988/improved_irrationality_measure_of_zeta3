# Semantic audit of the seven external finite inequalities

Reviewed against the current Lean sources on 2026-11-19. **No formula,
normalization, grid, endpoint, or inequality-direction mismatch was found.**
The review concerns the numerical boundary in
`Zeta3/Certificate/FiniteNumerics.lean`; it does not certify an asymptotic or
irrationality statement externally.

## Field correspondence

| Lean evidence field | Exact Arb quantity | Comparison |
| --- | --- | --- |
| `analytic_sum_lower` | 8,192-term left sum, step `(51/50)/8192` | Stored lower endpoint exceeds `300854183181/62500000000` |
| `physical_guard` | Physical mass at `u = 1000001/1000000` | Stored lower endpoint exceeds `51/50` |
| `linear_sum_lower` | 2,048-term left sum, step `(22/25)/2048` | Stored lower endpoint exceeds `3835733171/31250000000` |
| `angular_guard` | Angular mass at `B = 1` | Stored lower endpoint exceeds `7/50` |
| `response_sum_upper` | 1,024-term left sum, step `(17/125)/1024` | Stored upper endpoint is below `191284115113/200000000000` |
| `endpoint_lower` | Simple response at `T = 17/125` | Stored lower endpoint exceeds `6545408942519/1000000000000` |
| `endpoint_upper` | Same simple response at `T` | Stored upper endpoint is below `6545408942957/1000000000000` |

The precise positive rational differences are recorded in
`certificates/finite_semantic_manifest.json`. The manifest also hashes all
reviewed Lean formula/interface files and the Python source, summary and
witness file. Hashes identify the reviewed files; they do not prove numerical
inclusions.

## Formula correspondence

1. **Physical endpoint.** `Computation.mass` is literally
   `physicalMass`. Its root parameter is the physical mass `v`, not the
   squared support endpoint. The positive brackets solve `mass(b)-v = 0`.
   Lean constructs the unique nonnegative inverse and proves root-bracket
   soundness. The zero root is handled exactly.

2. **Analytic saving.** `analytic_integrand(v,b)` agrees with
   `physicalSavingFormula s1 s2 b v`, after distributing its two-term sum.
   The equivalence to the actual equilibrium saving is the proved
   `physicalSaving_eq_formula`. At `v=0`, Python uses
   `2*(s1+s2)*log(2)`; `physicalSaving_zero` together with
   `physicalSaving_eq_formula` proves this is exactly the Lean expression
   at the zero endpoint. No undefined numerical logarithm is evaluated.

3. **Linear coefficient.** The Python integrand is
   `u*b^2/((u^2+b^2)*sqrt(u^2+b^2))`. The Lean definition uses the cube of
   the radical; `physicalLinearKernel_formula` proves the exact equality.
   The Python upper integration coordinate is `delta-Tcap = 22/25`,
   exactly `CertificateLinear.cap`.

4. **Angular charges.** Python's angular width is `(1-s1-s2)/128 = 3/640`.
   Thus the common weight is `K = width/2 = 3/1280`, and midpoint `j` is
   `2/5 + 3*(2*j+1)/1280`. These are exactly `CertificateAngular.weight`
   and `CertificateAngular.node`. Both sides define the pole distance as
   `(u^2-x_j^2)^2/(2*u^2*x_j^2)`. The common linear coefficient is the
   same fixed rational `3835733171/31250000000`.

5. **Angular endpoint and response.** `angular_mass(B)` agrees with
   `angularMass`, including the factor `c*B/2`. The inverse variable is
   `B` itself (the angular squared support coordinate). The finite profile
   is `t*log(B/2)-c*B/2-2*sum(K*log((1+sqrt(1+B/e))/2))`, exactly the
   proved `angularProfile_formula`. Its special zero branch agrees with
   `angularProfile_zero`.

6. **Physical Gamma.** `ineg` agrees with `gammaNegativeIntegral`; the
   constant `base` agrees with `physicalGammaBase`. Python's local `J`
   agrees with `gammaJQuotient`, including the signs and both denominators.
   Consequently `gamma_at_b` agrees with `physicalGammaFormula` and,
   by `physicalGammaAtEndpoint_eq_formula`, with the actual response.
   Python evaluates `v = mass(b)` inside this expression, as does Lean's
   `physicalGammaAtEndpoint`. It does not silently substitute a different
   approximate mass. All response nodes have positive physical input
   `delta-t >= delta-T = 221/250`.

7. **Simple envelope and grid direction.** Both sides use
   `Gamma(delta-t)+F(t)`. The response sum includes indices `0..1023`.
   Index `1024` is evaluated solely for the two endpoint inequalities and
   has zero sum weight. Neither side uses the optional Green-function
   envelope or a compressed physical root. Lean, separately from Arb,
   proves the monotonicity and Riemann inequalities needed to turn these
   finite sums into integral estimates.

## Trust boundary and validation

This is a manual semantic review plus exact rational comparison of the
recorded bounds. The seven fields remain explicit external numerical
premises: their real-expression inclusions rely on Arb/FLINT, python-flint,
and the correctness of the reviewed evaluator. No native operation or
imported JSON is represented as a Lean kernel proof.

`verify_export.py` was rerun after the review to check witness identity,
required roots, endpoint sign claims, references, exact finite sums and
all target comparisons. Its log is
`certificates/semantic_export_check.log`. This standard-library checker
checks the consistency of the exported interval evidence; it does not
independently prove the real-function inclusions.

The formal contour bridge was also audited with
`ContourBridgeAudit.lean`; its theorem dependencies use only `propext`,
`Classical.choice` and `Quot.sound`. In particular,
`determinantResponse_eigenvalue_majorant` has no numerical assumption and
no new axiom. The root/equilibrium/integral/spectral arguments are separate
Lean theorems, not fields of the external certificate.

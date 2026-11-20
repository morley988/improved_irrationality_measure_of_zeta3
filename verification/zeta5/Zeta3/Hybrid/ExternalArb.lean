import Zeta3.Certificate.FiniteNumerics

/-!
# Explicit external numerical assumptions for the hybrid build

This optional module is the trust boundary of the hybrid verification.
The seven declarations below are AXIOMS, not Lean proofs or a claim that
loading a JSON file causes its contents to be checked by Lean's kernel.
Each is one fixed finite real-expression inequality. No asymptotic,
integral, arithmetic-rank, or irrationality statement is postulated here.

The assertions were checked by the 192-bit and 256-bit Arb replays in
`zeta3_certificates/arb_simple.py`. The root brackets and interval endpoints
are retained in `certificates/arb_simple/witnesses.jsonl`; the exact
export-consistency checker is `verify_export.py`. Formula/grid correspondence
is documented in `FINITE_SEMANTIC_AUDIT.md` and hashed in
`certificates/finite_semantic_manifest.json`.

Replacing these seven axioms by kernel-checked interval proofs is the
numerical task deferred to the later fully internal verification stage.
Core mathematical modules do not import this module.
-/

noncomputable section
namespace Zeta3.Hybrid.ExternalArb
open Zeta3.Analysis Zeta3.Certificate

def witnessSha256 : String :=
  "f6bbf2672c1386d28cd6bba96b132d42b4c216c81413262955c8d5a9677ada7c"

axiom analytic_sum_lower : Parameters.analyticLower≤analyticFiniteSum

axiom physical_guard : CertificateResponse.delta<
  physicalMass (2/25) (8/25) CertificateAngular.contour

axiom linear_sum_lower : CertificateAngular.coefficient≤linearFiniteSum

axiom angular_guard : CertificateResponse.angularCap<angularMass CertificateAngular.coefficient
  CertificateAngular.weight CertificateAngular.pole 1

axiom response_sum_upper : responseFiniteSum≤CertificateResponse.integralUpper

axiom endpoint_lower : CertificateResponse.endpointLower≤
  CertificateResponse.response CertificateResponse.cutoff

axiom endpoint_upper : CertificateResponse.response CertificateResponse.cutoff≤
  CertificateResponse.endpointUpper

theorem finiteEvidence : FiniteNumericalEvidence :=
  ⟨analytic_sum_lower,physical_guard,linear_sum_lower,angular_guard,
    response_sum_upper,endpoint_lower,endpoint_upper⟩

end Zeta3.Hybrid.ExternalArb

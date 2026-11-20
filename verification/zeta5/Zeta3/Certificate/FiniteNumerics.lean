import Zeta3.Certificate.Analytic
import Zeta3.Analysis.ContourLinear

/-!
# The finite numerical boundary of the hybrid proof

Every field below is a fixed finite real-expression inequality checked by
the external Arb replay.  No field mentions an integral, a determinant,
an asymptotic estimate, a valuation, or an irrationality exponent.

The analytic functions and inverse endpoints appearing in these expressions
are the actual functions defined in the proved mathematical development.
No instance is asserted here; the trusted external connector is kept separate.
-/

noncomputable section
namespace Zeta3.Certificate
open Zeta3.Analysis
open scoped BigOperators

def linearFiniteSum : ℝ :=
  (CertificateLinear.cap/2048)*∑ i ∈ Finset.range 2048,
    CertificateLinear.integrand ((CertificateLinear.cap/2048)*(i:ℝ))

def responseFiniteSum : ℝ :=
  (CertificateResponse.cutoff/1024)*∑ i ∈ Finset.range 1024,
    CertificateResponse.response ((CertificateResponse.cutoff/1024)*(i:ℝ))

structure FiniteNumericalEvidence : Prop where
  analytic_sum_lower : Parameters.analyticLower≤analyticFiniteSum
  physical_guard : CertificateResponse.delta<
    physicalMass (2/25) (8/25) CertificateAngular.contour
  linear_sum_lower : CertificateAngular.coefficient≤linearFiniteSum
  angular_guard : CertificateResponse.angularCap<angularMass CertificateAngular.coefficient
    CertificateAngular.weight CertificateAngular.pole 1
  response_sum_upper : responseFiniteSum≤CertificateResponse.integralUpper
  endpoint_lower : CertificateResponse.endpointLower≤
    CertificateResponse.response CertificateResponse.cutoff
  endpoint_upper : CertificateResponse.response CertificateResponse.cutoff≤
    CertificateResponse.endpointUpper

theorem FiniteNumericalEvidence.analytic (h : FiniteNumericalEvidence) : AnalyticFiniteEvidence :=
  ⟨h.analytic_sum_lower⟩

theorem FiniteNumericalEvidence.linear (h : FiniteNumericalEvidence) :
    CertificateLinear.FiniteEvidence
      (fun i => CertificateLinear.integrand ((CertificateLinear.cap/2048)*(i:ℝ))) := by
  exact ⟨h.physical_guard,fun _ _ => le_rfl,h.linear_sum_lower⟩

theorem FiniteNumericalEvidence.response (h : FiniteNumericalEvidence) :
    CertificateResponse.FiniteEvidence
      (fun i => CertificateResponse.response ((CertificateResponse.cutoff/1024)*(i:ℝ))) := by
  exact ⟨h.angular_guard,⟨fun _ _ => le_rfl,h.response_sum_upper,h.endpoint_lower,h.endpoint_upper⟩⟩

end Zeta3.Certificate

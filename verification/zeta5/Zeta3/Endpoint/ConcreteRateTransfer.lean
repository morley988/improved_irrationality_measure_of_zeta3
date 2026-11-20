import Zeta3.Analysis.IntegerValueRate
import Zeta3.Analysis.CertifiedResponse
import Zeta3.Construction.Nullity
import Zeta3.Construction.SharpDegree
import Zeta3.Transfer.Response

/-!
# Exact endpoint assembly for the concrete cubic family

The arithmetic and response rates are named mathematical premises here.
They are not external numerical certificate fields.  This module checks all
index scaling, the actual bounded multiplicity, the actual integer polynomial,
and the final rational comparison once those two rates are supplied.
-/

noncomputable section
namespace Zeta3.Endpoint
open Filter Polynomial
open Zeta3.Analysis Zeta3.Construction Zeta3.Transfer
open scoped Topology

def ActualArithmeticRate : Prop :=
  ∃ E : ℕ → ℝ, Tendsto (fun n => E n/windowScale n) atTop (𝓝 0) ∧
    (∀ᶠ n in atTop, Real.log (windowNormalizer n:ℝ) ≤
      Parameters.arithmeticUpper*windowScale n+E n)

def ActualResponseRate : Prop :=
  ∃ E : ℕ → ℝ, Tendsto (fun n => E n/windowScale n) atTop (𝓝 0) ∧
    (∀ᶠ n in atTop, ∀ h : ℂ,
      ‖h‖ ≤ 2*Real.exp (-((50*n:ℕ):ℝ)*CertificateResponse.response CertificateResponse.cutoff) →
      ‖determinantResponse n h‖ ≤ Real.exp
        (((∫ t in 0..CertificateResponse.cutoff, CertificateResponse.response t)-
            CertificateResponse.cutoff*CertificateResponse.response CertificateResponse.cutoff)*
          windowScale n+E n))

theorem approximation_exponent_le_target_of_actual_rates
    (hfinite : Certificate.AnalyticFiniteEvidence)
    {upper : ℕ → ℝ} (hresponseFinite : CertificateResponse.FiniteEvidence upper)
    (harithmetic : ActualArithmeticRate) (hresponse : ActualResponseRate) :
    HasApproximationExponentLE (Zeta5.Endpoint.realZeta 3) Parameters.target := by
  let a := CertificateResponse.response CertificateResponse.cutoff
  let I := ∫ t in 0..CertificateResponse.cutoff, CertificateResponse.response t
  have hb := CertificateResponse.endpoint_bounds hresponseFinite
  have ha : 0<a := by
    have hl : 0<CertificateResponse.endpointLower := by norm_num [CertificateResponse.endpointLower]
    exact hl.trans_le hb.1
  have haU : a≤Parameters.slopeUpper := hb.2
  have hI : I≤Parameters.responseIntegralUpper := CertificateResponse.integral_bound hresponseFinite
  have hratio := Parameters.ratio_le_from_actual_constants ha haU
    (le_refl Parameters.analyticLower) (le_refl Parameters.arithmeticUpper) hI
  have hgap : 2500*(I-Parameters.T*a)<2500*(Parameters.analyticLower-Parameters.arithmeticUpper) := by
    linarith [hratio.1]
  obtain ⟨Esmall,hEsmall,hsmall⟩ := exists_certified_integer_rate_error hfinite harithmetic
  obtain ⟨Eresponse,hEresponse,hresp⟩ := hresponse
  have hdegree : ∀ᶠ n : ℕ in atTop,
      ((windowIntegerPolynomial n).natDegree:ℝ)≤34*(n:ℝ)+1 := by
    filter_upwards [] with n
    exact_mod_cast windowIntegerPolynomial_natDegree_le_effectivePoles n
  have hsmall' : ∀ᶠ n : ℕ in atTop,
      ‖(windowIntegerPolynomial n).eval₂ (Int.castRingHom ℂ) (Zeta5.Endpoint.realZeta 3:ℂ)‖≤
        Real.exp (-(2500*(Parameters.analyticLower-Parameters.arithmeticUpper))*(n:ℝ)^2+Esmall n) := by
    convert hsmall using 1
    ext n
    congr 2
    unfold windowScale
    ring
  have hresp' : ∀ᶠ n : ℕ in atTop, ∀ h : ℂ,
      ‖h‖≤2*Real.exp (-(50*a)*(n:ℝ)) →
      ‖determinantResponse n h‖≤Real.exp (2500*(I-Parameters.T*a)*(n:ℝ)^2+Eresponse n) := by
    filter_upwards [hresp] with n hn
    intro h hh
    have hradius : -((50*n:ℕ):ℝ)*CertificateResponse.response CertificateResponse.cutoff=-(50*a)*(n:ℝ) := by
      dsimp only [a]
      push_cast
      ring
    have hr := hn h (by rwa [hradius])
    convert hr using 1
    dsimp only [I,a,Parameters.T,CertificateResponse.cutoff,windowScale]
    ring
  have hraw := approximation_exponent_le_of_response
    (Zeta5.Endpoint.realZeta 3) windowIntegerPolynomial determinantResponse
    2 34 1 (50*a) (2500*(Parameters.analyticLower-Parameters.arithmeticUpper))
    (2500*(I-Parameters.T*a)) Esmall Eresponse
    (by norm_num) (by positivity) hgap hdegree PhysicalMeasure.windowIntegerPolynomial_ne_zero
    (fun n p q _ => Rational.windowIntegerPolynomial_rootMultiplicity_le_two n ((p:ℝ)/(q:ℝ)))
    (quadratic_error_rescale hEsmall) (quadratic_error_rescale hEresponse)
    windowIntegerPolynomial_response_identity hsmall' hresp'
  apply hraw.mono
  calc
    34*(50*a)/(2500*(Parameters.analyticLower-Parameters.arithmeticUpper)-2500*(I-Parameters.T*a)) =
      Parameters.degreeRate*a/(Parameters.analyticLower-Parameters.arithmeticUpper-I+Parameters.T*a) := by
        unfold Parameters.degreeRate
        ring_nf
        field_simp
        ring
    _ ≤ Parameters.target := hratio.2

end Zeta3.Endpoint

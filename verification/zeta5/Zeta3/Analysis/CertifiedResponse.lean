import Zeta3.Analysis.PhysicalGamma
import Zeta3.Analysis.SimpleResponse

/-!
# The concrete response integral from finite external numerical evidence

All parameters and all 128 charges are the actual values used by the Arb
replay.  The physical and angular functions are defined, and their inverses
and monotonicity are proved.  `FiniteEvidence` contains only one finite guard
evaluation, the 1024 sample upper bounds, their finite sum, and endpoint
bounds.  There is no integral, asymptotic, or irrationality premise in it.
-/

namespace Zeta3.Analysis.CertificateResponse

open MeasureTheory Set
open scoped BigOperators

noncomputable section

def delta : ℝ := 51 / 50
def cutoff : ℝ := 17 / 125
def angularCap : ℝ := 7 / 50

def gamma (v : ℝ) : ℝ :=
  physicalGamma (2 / 25) (8 / 25) CertificateAngular.contour
    (by norm_num) (by norm_num) v

def response (t : ℝ) : ℝ :=
  simpleResponse gamma delta CertificateAngular.coefficient
    CertificateAngular.weight CertificateAngular.pole
    CertificateAngular.coefficient_pos CertificateAngular.weight_nonneg
    CertificateAngular.pole_pos t

def integralUpper : ℝ := 191284115113 / 200000000000
def endpointLower : ℝ := 6545408942519 / 1000000000000
def endpointUpper : ℝ := 6545408942957 / 1000000000000

theorem cutoff_pos : 0 < cutoff := by norm_num [cutoff]
theorem angularCap_pos : 0 < angularCap := by norm_num [angularCap]
theorem cutoff_le_angularCap : cutoff ≤ angularCap := by norm_num [cutoff, angularCap]
theorem contour_pos : 0 < CertificateAngular.contour := by norm_num [CertificateAngular.contour]

theorem gamma_monotoneOn : MonotoneOn gamma (Icc (delta - cutoff) delta) := by
  apply (physicalGamma_strictMonoOn (2 / 25) (8 / 25) CertificateAngular.contour
    (by norm_num) (by norm_num) contour_pos).monotoneOn.mono
  intro v hv
  change 0 < v
  have hlow : 0 < delta - cutoff := by norm_num [delta, cutoff]
  exact lt_of_lt_of_le hlow hv.1

theorem angular_cap_lt_one
    (hguard : angularCap < angularMass CertificateAngular.coefficient
      CertificateAngular.weight CertificateAngular.pole 1) :
    CertificateAngular.endpoint angularCap < 1 := by
  have h := CertificateAngular.endpoint_mem_Ioo_of_signs angularCap_pos.le
    (a := 0) (b := 1) (by norm_num) (by norm_num)
    (by simpa only [angularMass_zero] using angularCap_pos) hguard
  exact h.2

theorem angular_cutoff_lt_two
    (hguard : angularCap < angularMass CertificateAngular.coefficient
      CertificateAngular.weight CertificateAngular.pole 1) :
    CertificateAngular.endpoint cutoff < 2 := by
  have hmono := (angularEndpoint_strictMonoOn CertificateAngular.coefficient
    CertificateAngular.weight CertificateAngular.pole CertificateAngular.coefficient_pos
    CertificateAngular.weight_nonneg CertificateAngular.pole_pos).monotoneOn
    cutoff_pos.le angularCap_pos.le cutoff_le_angularCap
  have hcap := angular_cap_lt_one hguard
  change CertificateAngular.endpoint cutoff ≤ CertificateAngular.endpoint angularCap at hmono
  linarith

theorem response_strictAntiOn
    (hguard : angularCap < angularMass CertificateAngular.coefficient
      CertificateAngular.weight CertificateAngular.pole 1) :
    StrictAntiOn response (Icc 0 cutoff) :=
  simpleResponse_strictAntiOn gamma delta CertificateAngular.coefficient
    CertificateAngular.weight CertificateAngular.pole CertificateAngular.coefficient_pos
    CertificateAngular.weight_nonneg CertificateAngular.pole_pos cutoff_pos gamma_monotoneOn
    (angular_cutoff_lt_two hguard)

theorem response_intervalIntegrable
    (hguard : angularCap < angularMass CertificateAngular.coefficient
      CertificateAngular.weight CertificateAngular.pole 1) :
    IntervalIntegrable response volume 0 cutoff :=
  simpleResponse_intervalIntegrable gamma delta CertificateAngular.coefficient
    CertificateAngular.weight CertificateAngular.pole CertificateAngular.coefficient_pos
    CertificateAngular.weight_nonneg CertificateAngular.pole_pos cutoff_pos gamma_monotoneOn
    (angular_cutoff_lt_two hguard)

/-- The external part is finite: no analytic rates or integral claims are fields. -/
structure FiniteEvidence (upper : ℕ → ℝ) : Prop where
  angular_guard : angularCap < angularMass CertificateAngular.coefficient
    CertificateAngular.weight CertificateAngular.pole 1
  grid : ResponseGridEvidence response cutoff 1024 upper integralUpper endpointLower endpointUpper

theorem integral_bound {upper : ℕ → ℝ} (evidence : FiniteEvidence upper) :
    (∫ t in 0..cutoff, response t) ≤ integralUpper :=
  integral_le_of_responseGridEvidence response cutoff_pos.le (by norm_num : 0 < (1024 : ℕ))
    (response_strictAntiOn evidence.angular_guard).antitoneOn evidence.grid

theorem positive_on_interval {upper : ℕ → ℝ} (evidence : FiniteEvidence upper) :
    ∀ t ∈ Icc 0 cutoff, 0 < response t := by
  have hlo : 0 < endpointLower := by norm_num [endpointLower]
  exact simpleResponse_positive_of_evidence gamma delta CertificateAngular.coefficient
    CertificateAngular.weight CertificateAngular.pole CertificateAngular.coefficient_pos
    CertificateAngular.weight_nonneg CertificateAngular.pole_pos cutoff_pos gamma_monotoneOn
    (angular_cutoff_lt_two evidence.angular_guard) hlo evidence.grid

theorem endpoint_bounds {upper : ℕ → ℝ} (evidence : FiniteEvidence upper) :
    endpointLower ≤ response cutoff ∧ response cutoff ≤ endpointUpper :=
  ⟨evidence.grid.endpoint_lower, evidence.grid.endpoint_upper⟩

end

end Zeta3.Analysis.CertificateResponse

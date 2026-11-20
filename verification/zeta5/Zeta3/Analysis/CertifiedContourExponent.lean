import Zeta3.Analysis.PhysicalPotentialDeficit
import Zeta3.Analysis.AngularAbel

/-!
# The actual contour exponent is bounded by the certified response

The only external inputs are the finite linear-correction certificate.
All potential, logarithmic, support and contour comparisons are proved.
-/

noncomputable section
namespace Zeta3.Analysis
open Set
open scoped BigOperators

def physicalContourExponent (s₁ s₂ : ℝ) (h₁ : 0 < s₁) (h₂ : 0 < s₂)
    (v : ℝ) (z : ℂ) : ℝ :=
  rationalContourPotential s₁ s₂ z +
    2*complexLogPotential
      (physicalSquaredMeasure s₁ s₂ h₁ h₂ (physicalEndpoint s₁ s₂ h₁ h₂ v)) z-
    physicalEquilibrium s₁ s₂ h₁ h₂ v

theorem physicalGamma_eq_contourExponent (s₁ s₂ u : ℝ)
    (h₁ : 0 < s₁) (h₁one : s₁ ≤ 1) (h₂ : 0 < s₂) (h₂one : s₂ ≤ 1)
    (hu : 1 < u) (v : ℝ) :
    physicalGamma s₁ s₂ u h₁ h₂ v = physicalContourExponent s₁ s₂ h₁ h₂ v (-(u^2:ℝ):ℂ) := by
  have hb := physicalEndpoint_nonneg s₁ s₂ h₁ h₂ v
  rw [physicalGamma, physicalGammaAtEndpoint_eq_contour_potential s₁ s₂ u h₁ h₁one h₂ h₂one hu hb]
  unfold physicalContourExponent physicalEquilibrium
  rw [physicalComplexPotential_negative s₁ s₂ h₁ h₂ hb (by linarith)]
  ring

theorem physicalEndpoint_lt_of_mass_lt (s₁ s₂ : ℝ) (h₁ : 0 < s₁) (h₂ : 0 < s₂)
    {v u : ℝ} (hv : 0 ≤ v) (hu : 0 ≤ u) (hvu : v < physicalMass s₁ s₂ u) :
    physicalEndpoint s₁ s₂ h₁ h₂ v < u := by
  by_contra! h
  have hm := (physicalMass_strictMonoOn h₁ h₂).monotoneOn hu
    (physicalEndpoint_nonneg s₁ s₂ h₁ h₂ v) h
  rw [physicalMass_endpoint s₁ s₂ h₁ h₂ hv] at hm
  linarith

namespace CertificateResponse

def contourExponent (v : ℝ) (z : ℂ) : ℝ :=
  physicalContourExponent (2/25) (8/25) (by norm_num) (by norm_num) v z

theorem actual_contour_exponent_bound {lower : ℕ → ℝ}
    (hfinite : CertificateLinear.FiniteEvidence lower) {t : ℝ} (ht : t ∈ Icc 0 angularCap)
    (z : ℂ) (hz : Complex.normSq z=CertificateAngular.contour^4) :
    contourExponent (delta-t) z ≤ gamma (delta-t)-
      angularField CertificateAngular.coefficient CertificateAngular.weight CertificateAngular.pole
        (contourAngularCoordinate CertificateAngular.contour z) := by
  have hu : 1 < CertificateAngular.contour := by norm_num [CertificateAngular.contour]
  have huv : 0 < CertificateAngular.contour := by linarith
  have hv : 0 ≤ delta-t := by dsimp [delta,angularCap] at *; linarith [ht.2]
  have hcap : CertificateLinear.cap ≤ delta-t := by
    dsimp [CertificateLinear.cap,delta,angularCap] at *
    linarith [ht.2]
  have hmass : delta-t < physicalMass (2/25) (8/25) CertificateAngular.contour :=
    (sub_le_self delta ht.1).trans_lt hfinite.physical_guard
  have hbu := physicalEndpoint_lt_of_mass_lt (2/25) (8/25) (by norm_num) (by norm_num) hv huv.le hmass
  have hp := physical_potential_circle_deficit (2/25) (8/25) CertificateAngular.contour
    (by norm_num) (by norm_num) huv hv hbu z hz
  have hlin := CertificateLinear.integral_lower_of_cap_le hfinite hcap
  have hy := contourAngularCoordinate_mem huv hz
  have hlinmul := mul_le_mul_of_nonneg_right hlin hy.1
  have hrat := CertificateAngular.charge_sum_le_rationalContour_deficit hz
  have hgamma := physicalGamma_eq_contourExponent (2/25) (8/25) CertificateAngular.contour
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) hu (delta-t)
  unfold gamma
  rw [hgamma]
  unfold contourExponent physicalContourExponent angularField
  dsimp only [CertificateLinear.integral,contourAngularCoordinate] at hlinmul hp hrat ⊢
  linarith

end CertificateResponse
end Zeta3.Analysis

import Zeta3.Analysis.CertifiedEigenvalues
import Zeta3.Analysis.ContourEigenbasis
import Zeta3.Analysis.ResponseRegularity
import Zeta3.Analysis.SpectralResponseRate
import Zeta3.Certificate.FiniteNumerics
import Zeta3.Endpoint.ConcreteRateTransfer

/-!
# The actual response rate, with only finite numerical evidence

This closes the entire physical/contour/spectral branch for the actual
integer-polynomial family.  In particular, neither a spectral estimate nor
an asymptotic statement is assumed here.
-/

noncomputable section
namespace Zeta3.Analysis.CertificateResponse
open Filter Set
open scoped Topology BigOperators

def stageContourEigenvalues (n : ℕ) : Fin (51*n)→ℝ :=
  if hn : 0<n then actualContourEigenvalues n hn else fun _ => 0

theorem stageContourEigenvalues_eq (n : ℕ) (hn : 0<n) :
    stageContourEigenvalues n=actualContourEigenvalues n hn := by
  simp only [stageContourEigenvalues,dif_pos hn]

theorem stageContourEigenvalues_nonneg (n : ℕ) (j : Fin (51*n)) :
    0≤stageContourEigenvalues n j := by
  by_cases hn : 0<n
  · rw [stageContourEigenvalues_eq n hn]
    exact actualContourEigenvalues_nonneg n hn j
  · simp only [stageContourEigenvalues,dif_neg hn,le_refl]

theorem stageContourEigenvalues_antitone (n : ℕ) : Antitone (stageContourEigenvalues n) := by
  by_cases hn : 0<n
  · rw [stageContourEigenvalues_eq n hn]
    exact actualContourEigenvalues_antitone n hn
  · simp only [stageContourEigenvalues,dif_neg hn]
    exact antitone_const

theorem actual_determinant_spectral_majorant :
    ∀ᶠ n : ℕ in atTop, ∀ h : ℂ,
      ‖determinantResponse n h‖≤((51*n).factorial:ℝ)*
        ∏ j : Fin (51*n),(1+‖h‖*stageContourEigenvalues n j) := by
  filter_upwards [eventually_gt_atTop (0:ℕ)] with n hn
  intro h
  rw [stageContourEigenvalues_eq n hn]
  exact determinantResponse_eigenvalue_majorant n hn CertificateAngular.contour
    (by norm_num [CertificateAngular.contour]) h

theorem actual_even_eigenvalue_bounds (hfinite : Certificate.FiniteNumericalEvidence) :
    ∀ᶠ n : ℕ in atTop, ∀ (k:ℕ) (hk:2*k<51*n),
      2*(k:ℝ)/((50*n:ℕ):ℝ)≤cutoff →
        stageContourEigenvalues n ⟨2*k,hk⟩≤trialNormConstant*((50*n:ℕ):ℝ)^40*
          Real.exp (((50*n:ℕ):ℝ)*response (2*(k:ℝ)/((50*n:ℕ):ℝ))) := by
  filter_upwards [eventually_gt_atTop (0:ℕ)] with n hn
  intro k hk hkt
  have hcap : 2*(k:ℝ)/(50*n)≤angularCap := by
    have hh := hkt.trans cutoff_le_angularCap
    simpa only [Nat.cast_mul,Nat.cast_ofNat] using hh
  rw [stageContourEigenvalues_eq n hn]
  simpa only [Nat.cast_mul,Nat.cast_ofNat] using
    actualContourEigenvalues_even_bound n k hn hk hcap hfinite.linear hfinite.angular_guard

end Zeta3.Analysis.CertificateResponse

namespace Zeta3.Endpoint
open Zeta3.Analysis Zeta3.Analysis.CertificateResponse

theorem actualResponseRate_of_finiteEvidence (hfinite : Certificate.FiniteNumericalEvidence) :
    ActualResponseRate := by
  exact exists_response_rate_error_of_spectral_bounds response cutoff trialNormConstant
    cutoff_pos.le (by norm_num [cutoff]) trialNormConstant_pos.le
    (response_strictAntiOn hfinite.angular_guard).antitoneOn response_continuousWithinAt_cutoff
    stageContourEigenvalues determinantResponse stageContourEigenvalues_nonneg stageContourEigenvalues_antitone
    actual_determinant_spectral_majorant (actual_even_eigenvalue_bounds hfinite)

theorem approximation_exponent_le_target_of_arithmetic_rate
    (hfinite : Certificate.FiniteNumericalEvidence) (harithmetic : ActualArithmeticRate) :
    Zeta3.Transfer.HasApproximationExponentLE (Zeta5.Endpoint.realZeta 3) Parameters.target :=
  approximation_exponent_le_target_of_actual_rates hfinite.analytic hfinite.response harithmetic
    (actualResponseRate_of_finiteEvidence hfinite)

end Zeta3.Endpoint

import Zeta3.Analysis.CertifiedAngularTrial
import Zeta3.Analysis.ContourNorm

/-!
# Certified comparison of the actual trial norms

The actual angular factors yield a Rayleigh quotient estimate for the
positive contour form against the physical form.  All losses are bounded
by one fixed constant times N^40, independently of the trial dimension.
-/

noncomputable section
namespace Zeta3.Analysis.CertificateResponse
open Set Polynomial

def trialNormConstant : ℝ :=
  CertificateAngular.contour^4 * contourProductConstant CertificateAngular.contour * trialConstant

theorem trialNormConstant_pos : 0 < trialNormConstant := by
  unfold trialNormConstant
  exact mul_pos (mul_pos (by norm_num [CertificateAngular.contour])
    (contourProductConstant_pos (by norm_num [CertificateAngular.contour]))) trialConstant_pos

theorem exists_actual_trial_norm_bound (n m : ℕ) (hn : 0 < n)
    (hcap : 2*(m:ℝ)/(50*n) ≤ angularCap)
    {lower : ℕ → ℝ} (hfinite : CertificateLinear.FiniteEvidence lower)
    (hguard : angularCap < angularMass CertificateAngular.coefficient
      CertificateAngular.weight CertificateAngular.pole 1) :
    ∃ h : Fin m → ℝ, (∀ i, h i ∈ Icc 0 1) ∧
      ∀ p : ℝ[X], p.natDegree < 51*n-2*m →
        positiveContourNorm (50*n) (4*n) (16*n) CertificateAngular.contour
          (angularZeroProduct (CertificateAngular.contour^2) h*p) ≤
          (trialNormConstant*((50*n:ℕ):ℝ)^40*
            Real.exp (((50*n:ℕ):ℝ)*response (2*(m:ℝ)/(50*n)))) *
          normalizedPhysicalNorm (50*n) (4*n) (16*n)
            (angularZeroProduct (CertificateAngular.contour^2) h*p) := by
  obtain ⟨h,hh,hbound⟩ := exists_actual_trial_circle_bound n m hn hcap hfinite hguard
  refine ⟨h,hh,?_⟩
  intro p hp
  have hr := concrete_window_ratios n hn
  have hr₁ : ((4*n:ℕ):ℝ)/((50*n:ℕ):ℝ)=2/25 := by
    simpa only [Nat.cast_mul,Nat.cast_ofNat] using hr.1
  have hr₂ : ((16*n:ℕ):ℝ)/((50*n:ℕ):ℝ)=8/25 := by
    simpa only [Nat.cast_mul,Nat.cast_ofNat] using hr.2
  have hb := positiveContourNorm_le_of_exponential_bound
    (by norm_num [CertificateAngular.contour] : 1 < CertificateAngular.contour)
    (50*n) (4*n) (16*n) (by omega) (by omega) (by omega)
    (angularZeroProduct (CertificateAngular.contour^2) h*p)
    (by simpa only [hr₁,hr₂] using hbound p hp)
  convert hb using 1
  unfold trialNormConstant
  ring

end Zeta3.Analysis.CertificateResponse

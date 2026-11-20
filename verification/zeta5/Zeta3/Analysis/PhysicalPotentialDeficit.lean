import Zeta3.Analysis.PhysicalLinearMixture
import Zeta3.Analysis.PhysicalComplexComparison
import Zeta3.Analysis.ContourNegative

/-!
# The physical part of the angular deficit

The logarithmic inequality is proved pointwise on the actual contour and
integrated against the actual measure. Its coefficient is exactly the
mass integral used in the finite certificate.
-/

noncomputable section
namespace Zeta3.Analysis
open MeasureTheory Set Filter

theorem physical_log_circle_deficit {u w : ℝ} {z : ℂ}
    (hu : 0 < u) (hw : 0 ≤ w) (hwu : w < u^2) (hz : Complex.normSq z = u^4) :
    physicalLinearMeasureKernel u w*(1+z.re/u^2) ≤
      2*Real.log (u^2+w)-2*Real.log ‖z-(w:ℂ)‖ := by
  have ha : 0 < u^2 := sq_pos_of_pos hu
  have hd : 0 < u^2+w := by positivity
  have hnorm : ‖z‖ = u^2 := by
    rw [Complex.normSq_eq_norm_sq] at hz
    nlinarith [norm_nonneg z]
  have hn : 0 < ‖z-(w:ℂ)‖ := by
    have ht := norm_sub_norm_le z (w:ℂ)
    rw [hnorm, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hw] at ht
    linarith
  have hsq : ‖z-(w:ℂ)‖^2 = (u^2+w)^2-2*u^2*w*(1+z.re/u^2) := by
    have hz' : z.re^2+z.im^2=u^4 := by simpa only [Complex.normSq_apply,pow_two] using hz
    rw [← Complex.normSq_eq_norm_sq]
    simp only [Complex.normSq_apply, Complex.sub_re, Complex.sub_im, Complex.ofReal_re,
      Complex.ofReal_im, sub_zero]
    field_simp
    nlinarith [hz']
  have hratio : 0 < ‖z-(w:ℂ)‖^2/(u^2+w)^2 := by positivity
  have hl := Real.log_le_sub_one_of_pos hratio
  rw [Real.log_div (by positivity) (by positivity), Real.log_pow, Real.log_pow] at hl
  norm_num only [Nat.cast_ofNat] at hl
  have he : ‖z-(w:ℂ)‖^2/(u^2+w)^2-1 =
      -(physicalLinearMeasureKernel u w*(1+z.re/u^2)) := by
    rw [hsq]
    unfold physicalLinearMeasureKernel
    field_simp
    ring
  rw [he] at hl
  linarith

theorem physicalComplexPotential_negative (s₁ s₂ : ℝ)
    (h₁ : 0 < s₁) (h₂ : 0 < s₂) {b u : ℝ} (hb : 0 ≤ b) (hu : 0 < u) :
    complexLogPotential (physicalSquaredMeasure s₁ s₂ h₁ h₂ b) (-(u^2:ℝ):ℂ) =
      2*physicalImaginaryPotential s₁ s₂ h₁ h₂ b u := by
  rw [physicalImaginaryPotential_integral s₁ s₂ h₁ h₂ hb hu]
  have he : complexLogPotential (physicalSquaredMeasure s₁ s₂ h₁ h₂ b) (-(u^2:ℝ):ℂ) =
      ∫ w : ℝ, Real.log (u^2+w) ∂physicalSquaredMeasure s₁ s₂ h₁ h₂ b := by
    unfold complexLogPotential
    apply integral_congr_ae
    filter_upwards [physicalSquaredMeasure_ae_mem s₁ s₂ h₁ h₂ hb] with w hw
    rw [← Complex.ofReal_neg, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
    rw [show -u^2-w=-(u^2+w) by ring, abs_neg, abs_of_pos (add_pos_of_pos_of_nonneg (sq_pos_of_pos hu) hw.1)]
  rw [he]
  ring

theorem physical_potential_circle_deficit (s₁ s₂ u : ℝ)
    (h₁ : 0 < s₁) (h₂ : 0 < s₂) (hu : 0 < u) {v : ℝ} (hv : 0 ≤ v)
    (hbu : physicalEndpoint s₁ s₂ h₁ h₂ v < u) (z : ℂ) (hz : Complex.normSq z=u^4) :
    physicalLinearIntegral s₁ s₂ u h₁ h₂ v*(1+z.re/u^2) ≤
      2*complexLogPotential (physicalSquaredMeasure s₁ s₂ h₁ h₂ (physicalEndpoint s₁ s₂ h₁ h₂ v))
        (-(u^2:ℝ):ℂ) -
      2*complexLogPotential (physicalSquaredMeasure s₁ s₂ h₁ h₂ (physicalEndpoint s₁ s₂ h₁ h₂ v)) z := by
  let b := physicalEndpoint s₁ s₂ h₁ h₂ v
  let μ := physicalSquaredMeasure s₁ s₂ h₁ h₂ b
  have hb : 0 ≤ b := physicalEndpoint_nonneg s₁ s₂ h₁ h₂ v
  have hsupp := physicalSquaredMeasure_ae_mem s₁ s₂ h₁ h₂ hb
  have hc : 0 ≤ 3+(3/2:ℝ)*b := by positivity
  have hs := fun a ρ hρ => physicalSquaredMeasure_smallBall s₁ s₂ h₁ h₂ hb a ρ hρ
  have hlog := (complexLog_integrable_and_truncation_error μ hsupp hc
    (by norm_num : (0:ℝ)<1) hs z).1
  have hpos : Integrable (fun w : ℝ => Real.log (u^2+w)) μ :=
    ((squaredAuxiliaryMeasure_log_positive_integrable s₁ h₁ hb hu).add_measure
      (squaredAuxiliaryMeasure_log_positive_integrable s₂ h₂ hb hu)).smul_measure_nnreal
  have hk := physicalLinearMeasureKernel_integrable μ hu (hsupp.mono (fun _ hw => hw.1))
  have hi := integral_mono_ae (hk.mul_const (1+z.re/u^2))
    ((hpos.const_mul 2).sub (hlog.const_mul 2)) (by
      filter_upwards [hsupp] with w hw
      apply physical_log_circle_deficit hu hw.1 ?_ hz
      have hbu' : b < u := hbu
      nlinarith [hw.2])
  simp only [Pi.sub_apply] at hi
  rw [integral_mul_const, integral_sub (hpos.const_mul 2) (hlog.const_mul 2),
    integral_const_mul, integral_const_mul] at hi
  rw [physicalLinearIntegral_eq_measure s₁ s₂ u h₁ h₂ hu hv,
    physicalComplexPotential_negative s₁ s₂ h₁ h₂ hb hu,
    physicalImaginaryPotential_integral s₁ s₂ h₁ h₂ hb hu]
  change _ ≤ 2*(2*((1/2:ℝ)*(∫ w : ℝ, Real.log (u^2+w) ∂μ)))-2*(∫ w : ℝ, Real.log ‖z-(w:ℂ)‖ ∂μ)
  linarith

end Zeta3.Analysis

import Zeta3.Analysis.ComplexArcsine
import Zeta3.Analysis.PhysicalEquilibrium

/-! The actual two-window logarithmic potential on the imaginary axis. -/

noncomputable section
namespace Zeta3.Analysis
open MeasureTheory Set Filter Complex Real
open scoped NNReal

def imaginaryArcsineValue (u a : ℝ) : ℝ :=
  Real.log ((u + Real.sqrt (u ^ 2 + a ^ 2)) / 2)

theorem imaginaryArcsineValue_continuous {u : ℝ} (hu : 0 < u) :
    Continuous (imaginaryArcsineValue u) := by
  unfold imaginaryArcsineValue
  apply Continuous.log (by fun_prop)
  intro a
  positivity

theorem integral_angle_log_quadratic {b u : ℝ} (hb : 0 < b) (hu : 0 < u) :
    (∫ θ, Real.log (u ^ 2 + (b * Real.cos θ) ^ 2) ∂Zeta5.Analysis.angleMeasure) =
      2 * imaginaryArcsineValue u b := by
  obtain ⟨hi, hv⟩ := complexArcsinePotential_imaginary hb hu
  have hh := Zeta5.Analysis.circleAverage_realPart_eq_halfAngle
    (fun x : ℝ => Real.log ‖(u : ℂ) * I - (b * x : ℝ)‖) hi
  have hval : (1 / Real.pi) * (∫ θ in 0..Real.pi,
      Real.log ‖(u : ℂ) * I - (b * Real.cos θ : ℝ)‖) = imaginaryArcsineValue u b := by
    rw [← hh.2]
    exact hv
  have hfun : (fun θ : ℝ => Real.log (u ^ 2 + (b * Real.cos θ) ^ 2)) =
      (fun θ => 2 * Real.log ‖(u : ℂ) * I - (b * Real.cos θ : ℝ)‖) := by
    funext θ
    have hnorm : ‖(u : ℂ) * I - (b * Real.cos θ : ℝ)‖ ^ 2 = u ^ 2 + (b * Real.cos θ) ^ 2 := by
      rw [← Complex.normSq_eq_norm_sq]
      simp only [Complex.normSq_apply, Complex.sub_re, Complex.sub_im, Complex.mul_re,
        Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im]
      ring
    rw [← hnorm, Real.log_pow]
    norm_num
  rw [Zeta5.Analysis.integral_angleMeasure, hfun, intervalIntegral.integral_const_mul]
  linarith

theorem squaredAuxiliaryMeasure_log_positive_integrable (s : ℝ) (hs : 0 < s)
    {b u : ℝ} (hb : 0 ≤ b) (hu : 0 < u) :
    Integrable (fun w : ℝ => Real.log (u ^ 2 + w)) (Zeta5.Analysis.squaredAuxiliaryMeasure s hs b) := by
  apply (Zeta5.Analysis.squaredAuxiliaryMeasure_log_integrable s hs hb (-u ^ 2)).congr
  filter_upwards [Zeta5.Analysis.squaredAuxiliaryMeasure_ae_mem s hs hb] with w hw
  have hpos : 0 < u ^ 2 + w := add_pos_of_pos_of_nonneg (sq_pos_of_pos hu) hw.1
  rw [show -u ^ 2 - w = -(u ^ 2 + w) by ring, abs_neg, abs_of_pos hpos]

def auxiliaryImaginaryPotential (s : ℝ) (hs : 0 < s) (b u : ℝ) : ℝ :=
  (1 / 2 : ℝ) * ∫ w, Real.log (u ^ 2 + w) ∂Zeta5.Analysis.squaredAuxiliaryMeasure s hs b

theorem auxiliaryImaginaryPotential_eq_mixture (s : ℝ) (hs : 0 < s)
    {b u : ℝ} (hb : 0 ≤ b) (hu : 0 < u) :
    auxiliaryImaginaryPotential s hs b u =
      ∫ a in 0..b, Zeta5.Analysis.profileMassSlope s a * imaginaryArcsineValue u a := by
  have hm : Measurable (fun w : ℝ => Real.log (u ^ 2 + w)) := by fun_prop
  have hmapint : Integrable (fun p : ℝ × ℝ => Real.log (u ^ 2 + (p.1 * Real.cos p.2) ^ 2))
      ((Zeta5.Analysis.radialMeasure s hs b).prod Zeta5.Analysis.angleMeasure) := by
    exact (integrable_map_measure hm.aestronglyMeasurable
      Zeta5.Analysis.squaredAuxiliaryMap_measurable.aemeasurable).mp
        (squaredAuxiliaryMeasure_log_positive_integrable s hs hb hu)
  have hmain : (∫ w, Real.log (u ^ 2 + w) ∂Zeta5.Analysis.squaredAuxiliaryMeasure s hs b) =
      2 * ∫ a in 0..b, Zeta5.Analysis.profileMassSlope s a * imaginaryArcsineValue u a := by
    calc
      _ = ∫ p : ℝ × ℝ, Real.log (u ^ 2 + (p.1 * Real.cos p.2) ^ 2)
          ∂(Zeta5.Analysis.radialMeasure s hs b).prod Zeta5.Analysis.angleMeasure := by
        rw [Zeta5.Analysis.squaredAuxiliaryMeasure,
          integral_map Zeta5.Analysis.squaredAuxiliaryMap_measurable.aemeasurable hm.aestronglyMeasurable]
      _ = ∫ a, ∫ θ, Real.log (u ^ 2 + (a * Real.cos θ) ^ 2)
          ∂Zeta5.Analysis.angleMeasure ∂Zeta5.Analysis.radialMeasure s hs b := integral_prod _ hmapint
      _ = ∫ a, 2 * imaginaryArcsineValue u a ∂Zeta5.Analysis.radialMeasure s hs b := by
        apply integral_congr_ae
        filter_upwards [Zeta5.Analysis.radialMeasure_ae_mem s hs b] with a ha
        exact integral_angle_log_quadratic ha.1 hu
      _ = _ := by
        rw [Zeta5.Analysis.integral_radialMeasure,
          intervalIntegral.integral_of_le hb, ← integral_const_mul]
        apply setIntegral_congr_fun measurableSet_Ioc
        intro a _
        ring
  unfold auxiliaryImaginaryPotential
  rw [hmain]
  ring

def physicalImaginaryPotential (s₁ s₂ : ℝ) (h₁ : 0 < s₁) (h₂ : 0 < s₂) (b u : ℝ) : ℝ :=
  (auxiliaryImaginaryPotential s₁ h₁ b u + auxiliaryImaginaryPotential s₂ h₂ b u) / 2

theorem physicalImaginaryPotential_integral (s₁ s₂ : ℝ)
    (h₁ : 0 < s₁) (h₂ : 0 < s₂) {b u : ℝ} (hb : 0 ≤ b) (hu : 0 < u) :
    physicalImaginaryPotential s₁ s₂ h₁ h₂ b u =
      (1 / 2 : ℝ) * ∫ w, Real.log (u ^ 2 + w) ∂physicalSquaredMeasure s₁ s₂ h₁ h₂ b := by
  rw [physicalSquaredMeasure, integral_smul_nnreal_measure,
    integral_add_measure (squaredAuxiliaryMeasure_log_positive_integrable s₁ h₁ hb hu)
      (squaredAuxiliaryMeasure_log_positive_integrable s₂ h₂ hb hu)]
  simp only [NNReal.smul_def, smul_eq_mul]
  norm_num
  unfold physicalImaginaryPotential auxiliaryImaginaryPotential
  ring

theorem physicalImaginaryPotential_eq_mixture (s₁ s₂ : ℝ)
    (h₁ : 0 < s₁) (h₂ : 0 < s₂) {b u : ℝ} (hb : 0 ≤ b) (hu : 0 < u) :
    physicalImaginaryPotential s₁ s₂ h₁ h₂ b u =
      ∫ a in 0..b, physicalMassSlope s₁ s₂ a * imaginaryArcsineValue u a := by
  unfold physicalImaginaryPotential
  rw [auxiliaryImaginaryPotential_eq_mixture s₁ h₁ hb hu,
    auxiliaryImaginaryPotential_eq_mixture s₂ h₂ hb hu]
  have hfun : (fun a => physicalMassSlope s₁ s₂ a * imaginaryArcsineValue u a) =
      (fun a => (Zeta5.Analysis.profileMassSlope s₁ a * imaginaryArcsineValue u a +
        Zeta5.Analysis.profileMassSlope s₂ a * imaginaryArcsineValue u a) / 2) := by
    funext a
    rw [physicalMassSlope_eq_average]
    ring
  have hi₁ : IntervalIntegrable (fun a => Zeta5.Analysis.profileMassSlope s₁ a * imaginaryArcsineValue u a)
      volume 0 b := ((Zeta5.Analysis.profileMassSlope_continuous h₁).mul
        (imaginaryArcsineValue_continuous hu)).intervalIntegrable 0 b
  have hi₂ : IntervalIntegrable (fun a => Zeta5.Analysis.profileMassSlope s₂ a * imaginaryArcsineValue u a)
      volume 0 b := ((Zeta5.Analysis.profileMassSlope_continuous h₂).mul
        (imaginaryArcsineValue_continuous hu)).intervalIntegrable 0 b
  rw [hfun, intervalIntegral.integral_div, intervalIntegral.integral_add hi₁ hi₂]

end Zeta3.Analysis

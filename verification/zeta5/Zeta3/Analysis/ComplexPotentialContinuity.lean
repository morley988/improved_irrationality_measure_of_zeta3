import Zeta3.Analysis.ComplexLogTruncation
import Zeta5.Analysis.LogQuadrature
import Zeta5.Analysis.QuantilePartition
import Mathlib.MeasureTheory.Integral.Bochner.Set

/-!
# Continuity of the genuine complex logarithmic potential

A compactly supported real measure with uniform fourth-power small-ball
control has a continuous logarithmic potential on the whole complex plane.
The proof uses continuous truncated potentials and a proved uniform error.
-/

noncomputable section
namespace Zeta3.Analysis
open MeasureTheory Set Filter Metric

def complexLogPotential (μ : Measure ℝ) (z : ℂ) : ℝ :=
  ∫ w, Real.log ‖z - (w : ℂ)‖ ∂μ

def complexTruncatedLog (δ : ℝ) (z : ℂ) (w : ℝ) : ℝ :=
  Real.log (max δ ‖z - (w : ℂ)‖)

def complexTruncatedPotential (μ : Measure ℝ) (δ : ℝ) (z : ℂ) : ℝ :=
  ∫ w, complexTruncatedLog δ z w ∂μ

theorem complexTruncatedLog_joint_continuous {δ : ℝ} (hδ : 0 < δ) :
    Continuous (fun p : ℂ × ℝ => complexTruncatedLog δ p.1 p.2) := by
  unfold complexTruncatedLog
  apply Continuous.log (by fun_prop)
  intro p
  exact (lt_of_lt_of_le hδ (le_max_left _ _)).ne'

theorem complexTruncatedLog_continuous {δ : ℝ} (hδ : 0 < δ) (z : ℂ) :
    Continuous (complexTruncatedLog δ z) :=
  (complexTruncatedLog_joint_continuous hδ).comp (continuous_const.prodMk continuous_id)

theorem complexTruncatedPotential_continuous (μ : Measure ℝ) [IsFiniteMeasure μ]
    {B δ : ℝ} (hsupport : ∀ᵐ w ∂μ, w ∈ Icc 0 B) (hδ : 0 < δ) :
    Continuous (complexTruncatedPotential μ δ) := by
  have hrestrict : μ.restrict (Icc 0 B) = μ := Measure.restrict_eq_self_of_ae_mem hsupport
  have h := continuous_parametric_integral_of_continuous
    (μ := μ) (f := fun (z : ℂ) (w : ℝ) => complexTruncatedLog δ z w)
      (complexTruncatedLog_joint_continuous hδ) (s := Icc 0 B) isCompact_Icc
  change Continuous (fun z : ℂ => ∫ w : ℝ, complexTruncatedLog δ z w ∂μ)
  simpa only [hrestrict] using h

theorem complexTruncatedLog_le_log_add_loss (δ : ℝ) (z : ℂ) (w : ℝ) :
    complexTruncatedLog δ z w ≤ Real.log ‖z - (w : ℂ)‖ + complexLogTruncationLoss δ z w := by
  by_cases h : δ ≤ ‖z - (w : ℂ)‖
  · rw [complexTruncatedLog, max_eq_right h]
    exact le_add_of_nonneg_right (complexLogTruncationLoss_nonneg _ _ _)
  · rw [complexTruncatedLog, max_eq_left (le_of_not_ge h)]
    have hh := le_max_right 0 (Real.log δ - Real.log ‖z - (w : ℂ)‖)
    dsimp [complexLogTruncationLoss]
    linarith

theorem abs_complexLog_le_truncated_add_loss {δ : ℝ} (hδ : 0 < δ) (z : ℂ) (w : ℝ) :
    |Real.log ‖z - (w : ℂ)‖| ≤ |complexTruncatedLog δ z w| + complexLogTruncationLoss δ z w := by
  by_cases hd : ‖z - (w : ℂ)‖ = 0
  · simp only [hd, Real.log_zero, abs_zero]
    exact add_nonneg (abs_nonneg _) (complexLogTruncationLoss_nonneg _ _ _)
  have hdpos : 0 < ‖z - (w : ℂ)‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hd)
  by_cases h : δ ≤ ‖z - (w : ℂ)‖
  · rw [complexTruncatedLog, max_eq_right h]
    exact le_add_of_nonneg_right (complexLogTruncationLoss_nonneg _ _ _)
  · have hlog : Real.log ‖z - (w : ℂ)‖ ≤ Real.log δ :=
      Real.log_le_log hdpos (le_of_not_ge h)
    rw [complexTruncatedLog, max_eq_left (le_of_not_ge h)]
    rw [complexLogTruncationLoss, max_eq_right (sub_nonneg.mpr hlog)]
    apply abs_le.mpr
    constructor
    · have hh := neg_abs_le (Real.log δ)
      linarith
    · have hh := le_abs_self (Real.log δ)
      linarith

theorem complex_smallBall_of_real (μ : Measure ℝ) {C : ℝ}
    (hsmall : ∀ (v ρ : ℝ), 0 < ρ →
      μ {w : ℝ | |v - w| < ρ ^ 4} ≤ ENNReal.ofReal (C * ρ)) (z : ℂ) {ρ : ℝ} (hρ : 0 < ρ) :
    μ {w : ℝ | ‖z - (w : ℂ)‖ < ρ ^ 4} ≤ ENNReal.ofReal (C * ρ) := by
  apply (measure_mono ?_).trans (hsmall z.re ρ hρ)
  intro w hw
  have h := Complex.abs_re_le_norm (z - (w : ℂ))
  simp only [Complex.sub_re, Complex.ofReal_re] at h
  exact h.trans_lt hw

theorem complexLog_integrable_and_truncation_error (μ : Measure ℝ) [IsFiniteMeasure μ]
    {B C ε : ℝ} (hsupport : ∀ᵐ w ∂μ, w ∈ Icc 0 B) (hC : 0 ≤ C) (hε : 0 < ε)
    (hsmall : ∀ (v ρ : ℝ), 0 < ρ →
      μ {w : ℝ | |v - w| < ρ ^ 4} ≤ ENNReal.ofReal (C * ρ)) (z : ℂ) :
    Integrable (fun w : ℝ => Real.log ‖z - (w : ℂ)‖) μ ∧
      dist (complexTruncatedPotential μ (ε ^ 4) z) (complexLogPotential μ z) ≤ 4 * C * ε := by
  letI : NullSingletonClass μ := Zeta5.Analysis.nullSingletonClass_of_fourth_power_smallBall μ hC hsmall
  have hrestrict : μ.restrict (Icc 0 B) = μ := Measure.restrict_eq_self_of_ae_mem hsupport
  have ht : Integrable (complexTruncatedLog (ε ^ 4) z) μ := by
    have h := (complexTruncatedLog_continuous (pow_pos hε 4) z).integrableOn_Icc (a := 0) (b := B) (μ := μ)
    simpa only [IntegrableOn, hrestrict] using h
  obtain ⟨hloss, hbound⟩ := complexLogTruncationLoss_integrable_and_integral_le μ hC hε
    (fun ρ hρ => complex_smallBall_of_real μ hsmall z hρ)
  have hmeas : Measurable (fun w : ℝ => Real.log ‖z - (w : ℂ)‖) := by fun_prop
  have hlog : Integrable (fun w : ℝ => Real.log ‖z - (w : ℂ)‖) μ := by
    exact (ht.abs.add hloss).mono' hmeas.aestronglyMeasurable
      (Eventually.of_forall (fun w => by
        simpa only [Real.norm_eq_abs, Pi.add_apply] using
          abs_complexLog_le_truncated_add_loss (pow_pos hε 4) z w))
  have hupp := integral_mono ht (hlog.add hloss) (complexTruncatedLog_le_log_add_loss (ε ^ 4) z)
  dsimp only [Pi.add_apply] at hupp
  rw [integral_add hlog hloss] at hupp
  have hlower : (∫ w, Real.log ‖z - (w : ℂ)‖ ∂μ) ≤ complexTruncatedPotential μ (ε ^ 4) z := by
    apply integral_mono_ae hlog ht
    filter_upwards [μ.ae_ne z.re] with w hw
    have hne : z - (w : ℂ) ≠ 0 := by
      intro hz
      have h := congrArg Complex.re (sub_eq_zero.mp hz)
      simp only [Complex.ofReal_re] at h
      exact hw h.symm
    exact Real.log_le_log (norm_pos_iff.2 hne) (le_max_right _ _)
  refine ⟨hlog, ?_⟩
  rw [Real.dist_eq]
  change |complexTruncatedPotential μ (ε ^ 4) z - (∫ w, Real.log ‖z - (w : ℂ)‖ ∂μ)| ≤ _
  rw [abs_of_nonneg (sub_nonneg.2 hlower)]
  unfold complexTruncatedPotential
  linarith

theorem complexLogPotential_continuous (μ : Measure ℝ) [IsFiniteMeasure μ]
    {B C : ℝ} (hsupport : ∀ᵐ w ∂μ, w ∈ Icc 0 B) (hC : 0 ≤ C)
    (hsmall : ∀ (v ρ : ℝ), 0 < ρ →
      μ {w : ℝ | |v - w| < ρ ^ 4} ≤ ENNReal.ofReal (C * ρ)) :
    Continuous (complexLogPotential μ) := by
  apply continuous_iff_continuousAt.2
  intro z
  apply Metric.continuousAt_iff.2
  intro ε hε
  let η : ℝ := ε / (32 * (C + 1))
  have hη : 0 < η := by dsimp [η]; positivity
  have herr : 4 * C * η < ε / 4 := by
    dsimp [η]
    have hd : 0 < 32 * (C + 1) := by positivity
    apply (lt_div_iff₀ (by norm_num : (0 : ℝ) < 4)).2
    field_simp
    nlinarith
  have hcont := (complexTruncatedPotential_continuous μ hsupport (pow_pos hη 4)).continuousAt (x := z)
  obtain ⟨δ, hδ, hδbound⟩ := Metric.continuousAt_iff.1 hcont (ε / 2) (by positivity)
  refine ⟨δ, hδ, ?_⟩
  intro x hx
  have hxerr := (complexLog_integrable_and_truncation_error μ hsupport hC hη hsmall x).2
  have hzerr := (complexLog_integrable_and_truncation_error μ hsupport hC hη hsmall z).2
  have hmid := hδbound hx
  have htri := dist_triangle (complexLogPotential μ x) (complexTruncatedPotential μ (η ^ 4) x)
    (complexLogPotential μ z)
  have htri' := dist_triangle (complexTruncatedPotential μ (η ^ 4) x)
    (complexTruncatedPotential μ (η ^ 4) z) (complexLogPotential μ z)
  rw [dist_comm (complexLogPotential μ x) (complexTruncatedPotential μ (η ^ 4) x)] at htri
  linarith

end Zeta3.Analysis

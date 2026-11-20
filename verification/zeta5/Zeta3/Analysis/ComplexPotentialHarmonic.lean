import Zeta3.Analysis.ComplexPotentialContinuity
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.SpecialFunctions.Complex.LogBounds
import Mathlib.Analysis.InnerProductSpace.Harmonic.Constructions
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.MeasureTheory.Function.SpecialFunctions.Basic

/-!
# Harmonicity off the support of a genuine logarithmic potential

A local complex logarithm of the ratio `(z-w)/(z₀-w)` avoids any global
branch choice. Its derivative is uniformly dominated whenever the center
is separated from the support. Differentiation under the actual integral
then gives a local analytic representative of the real potential.
-/

noncomputable section
namespace Zeta3.Analysis
open MeasureTheory Set Filter Metric InnerProductSpace

private def relativeLog (z₀ z : ℂ) (w : ℝ) : ℂ :=
  Complex.log (1 + (z - z₀) / (z₀ - (w : ℂ)))

private theorem ratio_norm_le_half {r : ℝ} (hr : 0 < r) {z₀ z : ℂ} {w : ℝ}
    (hw : r ≤ ‖z₀ - (w : ℂ)‖) (hz : ‖z - z₀‖ ≤ r / 2) :
    ‖(z - z₀) / (z₀ - (w : ℂ))‖ ≤ 1 / 2 := by
  rw [norm_div]
  apply (div_le_iff₀ (lt_of_lt_of_le hr hw)).2
  linarith

private theorem relativeLog_integrable (μ : Measure ℝ) [IsFiniteMeasure μ]
    {r : ℝ} (hr : 0 < r) {z₀ z : ℂ}
    (hsep : ∀ᵐ (w : ℝ) ∂μ, r ≤ ‖z₀ - (w : ℂ)‖) (hz : ‖z - z₀‖ ≤ r / 2) :
    Integrable (relativeLog z₀ z) μ := by
  apply (integrable_const (1 : ℝ)).mono' (by
    apply Measurable.aestronglyMeasurable
    unfold relativeLog
    fun_prop)
  filter_upwards [hsep] with w hw
  have hhalf := ratio_norm_le_half hr hw hz
  have hh := Complex.norm_log_one_add_half_le_self hhalf
  change ‖Complex.log (1 + (z-z₀)/(z₀-(w:ℂ)))‖ ≤ 1
  nlinarith

private theorem relativeLog_hasDerivAt {r : ℝ} (hr : 0 < r) {z₀ z : ℂ} {w : ℝ}
    (hw : r ≤ ‖z₀ - (w : ℂ)‖) (hz : ‖z - z₀‖ < r / 2) :
    HasDerivAt (fun x => relativeLog z₀ x w) (1 / (z - (w : ℂ))) z := by
  have hhalf := ratio_norm_le_half hr hw hz.le
  have hlt : ‖(z-z₀)/(z₀-(w:ℂ))‖ < 1 := lt_of_le_of_lt hhalf (by norm_num)
  have hslit := Complex.mem_slitPlane_of_norm_lt_one hlt
  have h₀ : z₀ - (w : ℂ) ≠ 0 := norm_pos_iff.1 (hr.trans_le hw)
  have h₁ : 1 + (z-z₀)/(z₀-(w:ℂ)) ≠ 0 := Complex.slitPlane_ne_zero hslit
  have hder := (Complex.hasDerivAt_log hslit).comp z
    ((((hasDerivAt_id z).sub_const z₀).div_const (z₀-(w:ℂ))).const_add 1)
  convert hder using 1 <;> first | rfl | (field_simp [h₀, h₁] <;> ring)

private theorem relativeLog_deriv_bound {r : ℝ} (hr : 0 < r) {z₀ z : ℂ} {w : ℝ}
    (hw : r ≤ ‖z₀ - (w : ℂ)‖) (hz : ‖z - z₀‖ < r / 2) :
    ‖(1 : ℂ) / (z - (w : ℂ))‖ ≤ 2 / r := by
  have htri : ‖z₀ - (w : ℂ)‖ ≤ ‖z-z₀‖ + ‖z-(w:ℂ)‖ := by
    calc
      ‖z₀-(w:ℂ)‖ = ‖(z₀-z)+(z-(w:ℂ))‖ := by congr 1; ring
      _ ≤ ‖z₀-z‖ + ‖z-(w:ℂ)‖ := norm_add_le _ _
      _ = _ := by rw [norm_sub_rev z₀ z]
  have hl : r / 2 ≤ ‖z-(w:ℂ)‖ := by linarith
  rw [norm_div, norm_one]
  have := one_div_le_one_div_of_le (by positivity : 0 < r / 2) hl
  exact this.trans_eq (by field_simp)

private theorem relativeLogIntegral_analyticAt (μ : Measure ℝ) [IsFiniteMeasure μ]
    {r : ℝ} (hr : 0 < r) (z₀ : ℂ)
    (hsep : ∀ᵐ (w : ℝ) ∂μ, r ≤ ‖z₀ - (w : ℂ)‖) :
    AnalyticAt ℂ (fun z => ∫ w, relativeLog z₀ z w ∂μ) z₀ := by
  apply DifferentiableOn.analyticAt (s := ball z₀ (r/2)) ?_ (ball_mem_nhds _ (by positivity))
  intro z hz
  have hz' : ‖z-z₀‖ < r/2 := by simpa only [mem_ball, dist_eq_norm] using hz
  have hd := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := μ) (F := fun z w => relativeLog z₀ z w)
    (F' := fun z w => (1 : ℂ)/(z-(w:ℂ)))
    (bound := fun _ => 2/r) (s := ball z₀ (r/2))
    (isOpen_ball.mem_nhds hz)
    (Eventually.of_forall (fun z => by
      apply Measurable.aestronglyMeasurable
      unfold relativeLog
      fun_prop))
    (relativeLog_integrable μ hr hsep hz'.le)
    (by apply Measurable.aestronglyMeasurable; fun_prop)
    (hsep.mono (fun w hw z hz => relativeLog_deriv_bound hr hw
      (by simpa only [mem_ball, dist_eq_norm] using hz)))
    (integrable_const _)
    (hsep.mono (fun w hw z hz => relativeLog_hasDerivAt hr hw
      (by simpa only [mem_ball, dist_eq_norm] using hz)))
  exact hd.2.differentiableAt.differentiableWithinAt

/-- Uniform separation alone supplies a local harmonic representative; the
only logarithmic integrability needed is at the center. -/
theorem complexLogPotential_harmonicAt_of_separation (μ : Measure ℝ) [IsFiniteMeasure μ]
    {r : ℝ} (hr : 0 < r) (z₀ : ℂ)
    (hsep : ∀ᵐ (w : ℝ) ∂μ, r ≤ ‖z₀ - (w : ℂ)‖)
    (hlog : Integrable (fun w : ℝ => Real.log ‖z₀-(w:ℂ)‖) μ) :
    HarmonicAt (complexLogPotential μ) z₀ := by
  have ha := relativeLogIntegral_analyticAt μ hr z₀ hsep
  have hh := (harmonicAt_const (complexLogPotential μ z₀)).add ha.harmonicAt_re
  apply (harmonicAt_congr_nhds (f₁ := complexLogPotential μ)
    (f₂ := fun z => complexLogPotential μ z₀ + (∫ w, relativeLog z₀ z w ∂μ).re) ?_).2 hh
  filter_upwards [ball_mem_nhds z₀ (by positivity : 0 < r/2)] with z hz
  have hz' : ‖z-z₀‖ < r/2 := by simpa only [mem_ball, dist_eq_norm] using hz
  have hi := relativeLog_integrable μ hr hsep hz'.le
  have hre : Integrable (fun w => (relativeLog z₀ z w).re) μ :=
    Complex.reCLM.integrable_comp hi
  have heq : (fun w : ℝ => Real.log ‖z-(w:ℂ)‖) =ᵐ[μ]
      (fun w => Real.log ‖z₀-(w:ℂ)‖ + (relativeLog z₀ z w).re) := by
    filter_upwards [hsep] with w hw
    have h₀ : z₀ - (w : ℂ) ≠ 0 := norm_pos_iff.1 (hr.trans_le hw)
    have hlt : ‖(z-z₀)/(z₀-(w:ℂ))‖ < 1 :=
      lt_of_le_of_lt (ratio_norm_le_half hr hw hz'.le) (by norm_num)
    have h₁ : 1 + (z-z₀)/(z₀-(w:ℂ)) ≠ 0 :=
      Complex.slitPlane_ne_zero (Complex.mem_slitPlane_of_norm_lt_one hlt)
    have he : z-(w:ℂ) = (z₀-(w:ℂ))*(1+(z-z₀)/(z₀-(w:ℂ))) := by
      field_simp
      ring
    rw [he, norm_mul, Real.log_mul (norm_ne_zero_iff.2 h₀) (norm_ne_zero_iff.2 h₁)]
    simp only [relativeLog, Complex.log_re]
  unfold complexLogPotential
  rw [integral_congr_ae heq, integral_add hlog hre]
  congr 1
  exact integral_re hi

/-- The actual potential is harmonic at every point off its compact real support. -/
theorem complexLogPotential_harmonicOnNhd (μ : Measure ℝ) [IsFiniteMeasure μ]
    {B C : ℝ} (hsupport : ∀ᵐ w ∂μ, w ∈ Icc 0 B) (hC : 0 ≤ C)
    (hsmall : ∀ (v ρ : ℝ), 0 < ρ →
      μ {w : ℝ | |v-w| < ρ^4} ≤ ENNReal.ofReal (C*ρ)) :
    HarmonicOnNhd (complexLogPotential μ) (Complex.ofReal '' Icc 0 B)ᶜ := by
  intro z hz
  have hclosed : IsClosed (Complex.ofReal '' Icc 0 B) :=
    (isCompact_Icc.image Complex.continuous_ofReal).isClosed
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.1 hclosed.isOpen_compl z hz
  apply complexLogPotential_harmonicAt_of_separation μ hr z ?_
    (complexLog_integrable_and_truncation_error μ hsupport hC (by norm_num : (0:ℝ)<1) hsmall z).1
  filter_upwards [hsupport] with w hw
  by_contra hbad
  have hmem : (w:ℂ) ∈ ball z r := by
    simpa only [mem_ball, dist_eq_norm, norm_sub_rev] using lt_of_not_ge hbad
  exact hball hmem ⟨w, hw, rfl⟩

end Zeta3.Analysis

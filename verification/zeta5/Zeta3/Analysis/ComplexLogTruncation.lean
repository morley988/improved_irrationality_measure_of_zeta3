import Mathlib.MeasureTheory.Integral.Layercake
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Complex logarithmic truncation from uniform small-ball control

This adapts the layer-cake proof of Zeta5.Analysis.LogTruncation to the
complex distance from a real measure.  The resulting uniform error is the
input to continuity of the genuine complex logarithmic potential.
-/

open MeasureTheory Set Filter

namespace Zeta3.Analysis

noncomputable def complexLogTruncationLoss (δ : ℝ) (v : ℂ) (w : ℝ) : ℝ :=
  max 0 (Real.log δ - Real.log ‖v - (w : ℂ)‖)

lemma complexLogTruncationLoss_nonneg (δ : ℝ) (v : ℂ) (w : ℝ) :
    0 ≤ complexLogTruncationLoss δ v w := le_max_left _ _

lemma complexLogTruncationLoss_measurable (δ : ℝ) (v : ℂ) :
    Measurable (complexLogTruncationLoss δ v) := by
  unfold complexLogTruncationLoss
  fun_prop

lemma complexLogTruncationLoss_tail_subset {ε t : ℝ} {v : ℂ} (hε : 0 < ε) (ht : 0 < t) :
    {w : ℝ | t < complexLogTruncationLoss (ε ^ 4) v w} ⊆
      {w : ℝ | ‖v - (w : ℂ)‖ < (ε * Real.exp (-(1 / 4 : ℝ) * t)) ^ 4} := by
  intro w hw
  have hδ : 0 < ε ^ 4 := pow_pos hε _
  have hr : 0 < (ε * Real.exp (-(1 / 4 : ℝ) * t)) ^ 4 := by positivity
  by_cases hd : ‖v - (w : ℂ)‖ = 0
  · simpa [hd] using hr
  have hdpos : 0 < ‖v - (w : ℂ)‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hd)
  have hlog : t < Real.log (ε ^ 4) - Real.log ‖v - (w : ℂ)‖ := by
    exact (lt_max_iff.mp hw).resolve_left (not_lt_of_ge ht.le)
  have hexp : Real.exp t < ε ^ 4 / ‖v - (w : ℂ)‖ := by
    have hh := Real.exp_lt_exp.mpr hlog
    rw [Real.exp_sub, Real.exp_log hδ, Real.exp_log hdpos] at hh
    exact hh
  have hdist : ‖v - (w : ℂ)‖ < ε ^ 4 / Real.exp t := by
    exact (lt_div_iff₀ (Real.exp_pos _)).mpr
      (by simpa [mul_comm] using (lt_div_iff₀ hdpos).mp hexp)
  have hid : (ε * Real.exp (-(1 / 4 : ℝ) * t)) ^ 4 = ε ^ 4 / Real.exp t := by
    rw [mul_pow, ← Real.exp_nat_mul]
    norm_num only [Nat.cast_ofNat]
    rw [show (4 : ℝ) * (-(1 / 4 : ℝ) * t) = -t by ring, Real.exp_neg]
    rfl
  rw [hid]
  exact hdist

/-- The integral of the exponential majorant appearing in the layer-cake proof. -/
lemma integral_complexLogTruncation_majorant (C ε : ℝ) :
    (∫ t in Ioi (0 : ℝ), C * ε * Real.exp (-(1 / 4 : ℝ) * t)) = 4 * C * ε := by
  rw [integral_const_mul, integral_exp_mul_Ioi (by norm_num : -(1 / 4 : ℝ) < 0)]
  norm_num
  ring

lemma complexLogTruncation_majorant_integrable (C ε : ℝ) :
    IntegrableOn (fun t : ℝ => C * ε * Real.exp (-(1 / 4 : ℝ) * t)) (Ioi 0) := by
  exact (integrableOn_exp_mul_Ioi (by norm_num : -(1 / 4 : ℝ) < 0) 0).const_mul _

/-- A Hölder small-ball estimate gives both integrability and a quantitative
bound for the error caused by truncating a logarithmic singularity. -/
theorem complexLogTruncationLoss_integrable_and_integral_le
    (μ : Measure ℝ) {C ε : ℝ} {v : ℂ} (hC : 0 ≤ C) (hε : 0 < ε)
    (hsmall : ∀ ρ : ℝ, 0 < ρ →
      μ {w : ℝ | ‖v - (w : ℂ)‖ < ρ ^ 4} ≤ ENNReal.ofReal (C * ρ)) :
    Integrable (complexLogTruncationLoss (ε ^ 4) v) μ ∧
      (∫ w, complexLogTruncationLoss (ε ^ 4) v w ∂μ) ≤ 4 * C * ε := by
  let f := complexLogTruncationLoss (ε ^ 4) v
  let g : ℝ → ℝ := fun t => C * ε * Real.exp (-(1 / 4 : ℝ) * t)
  have hfnonneg : 0 ≤ᵐ[μ] f := Eventually.of_forall (complexLogTruncationLoss_nonneg _ _)
  have hfmeas : Measurable f := complexLogTruncationLoss_measurable _ _
  have hgnonneg : ∀ t, 0 ≤ g t := fun t => by dsimp [g]; positivity
  have hgint : Integrable g (volume.restrict (Ioi 0)) :=
    complexLogTruncation_majorant_integrable C ε
  have htail : ∀ t ∈ Ioi (0 : ℝ), μ {w | t < f w} ≤ ENNReal.ofReal (g t) := by
    intro t ht
    calc
      μ {w | t < f w} ≤ μ {w : ℝ | ‖v - (w : ℂ)‖ <
          (ε * Real.exp (-(1 / 4 : ℝ) * t)) ^ 4} :=
        measure_mono (complexLogTruncationLoss_tail_subset hε ht)
      _ ≤ ENNReal.ofReal (C * (ε * Real.exp (-(1 / 4 : ℝ) * t))) :=
        hsmall _ (mul_pos hε (Real.exp_pos _))
      _ = ENNReal.ofReal (g t) := by congr 1; dsimp [g]; ring
  have hle : (∫⁻ w, ENNReal.ofReal (f w) ∂μ) ≤
      ∫⁻ t in Ioi (0 : ℝ), ENNReal.ofReal (g t) := by
    rw [lintegral_eq_lintegral_meas_lt μ hfnonneg hfmeas.aemeasurable]
    exact lintegral_mono_ae (ae_restrict_of_forall_mem measurableSet_Ioi htail)
  have hfinite : (∫⁻ w, ENNReal.ofReal (f w) ∂μ) ≠ ⊤ :=
    ne_top_of_le_ne_top hgint.lintegral_lt_top.ne hle
  have hfint : Integrable f μ :=
    (lintegral_ofReal_ne_top_iff_integrable hfmeas.aestronglyMeasurable hfnonneg).mp hfinite
  refine ⟨hfint, ?_⟩
  have hreal := ENNReal.toReal_mono hgint.lintegral_lt_top.ne hle
  rw [← integral_eq_lintegral_of_nonneg_ae hfnonneg hfmeas.aestronglyMeasurable,
    ← integral_eq_lintegral_of_nonneg_ae (Eventually.of_forall hgnonneg)
      hgint.aestronglyMeasurable] at hreal
  dsimp only [g] at hreal
  rw [integral_complexLogTruncation_majorant] at hreal
  exact hreal

end Zeta3.Analysis

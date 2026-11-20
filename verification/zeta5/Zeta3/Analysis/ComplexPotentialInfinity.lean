import Zeta3.Analysis.ComplexPotentialContinuity
import Mathlib.Analysis.Polynomial.Basic

/-!
# Decay at infinity for a polynomial below the measure's scaled mass

Compact support gives a direct lower bound on the genuine potential.
A polynomial of strictly smaller degree then tends to zero after weighting.
The strict inequality is precisely what the codimension trial space supplies.
-/

noncomputable section
namespace Zeta3.Analysis
open MeasureTheory Set Filter Metric Bornology Asymptotics Topology

theorem complexLogPotential_ge_mass_log (μ : Measure ℝ) [IsFiniteMeasure μ]
    {B : ℝ} (hB : 0 ≤ B) (hsupport : ∀ᵐ w ∂μ, w ∈ Icc 0 B)
    (z : ℂ) (hz : 2*(B+1) ≤ ‖z‖)
    (hlog : Integrable (fun w : ℝ => Real.log ‖z-(w:ℂ)‖) μ) :
    μ.real univ * (Real.log ‖z‖ - Real.log 2) ≤ complexLogPotential μ z := by
  have hnorm : 0 < ‖z‖ := by linarith
  have hb : (∫ _ : ℝ, Real.log (‖z‖/2) ∂μ) ≤ complexLogPotential μ z := by
    apply integral_mono_ae (integrable_const _) hlog
    filter_upwards [hsupport] with w hw
    apply Real.log_le_log (by positivity)
    have ht := norm_sub_norm_le z (w:ℂ)
    have hwabs : ‖(w:ℂ)‖ = w := by simp [abs_of_nonneg hw.1]
    rw [hwabs] at ht
    linarith [hw.2]
  simpa only [integral_const, smul_eq_mul, Real.log_div hnorm.ne' (by norm_num : (2:ℝ) ≠ 0)] using hb

theorem weighted_polynomial_tendsto_zero (μ : Measure ℝ) [IsFiniteMeasure μ]
    {B N : ℝ} (hB : 0 ≤ B) (hN : 0 ≤ N)
    (hsupport : ∀ᵐ w ∂μ, w ∈ Icc 0 B)
    (hlog : ∀ z : ℂ, Integrable (fun w : ℝ => Real.log ‖z-(w:ℂ)‖) μ)
    (m : ℕ) (hmass : N * μ.real univ = m)
    (p : Polynomial ℂ) (hdeg : p.natDegree < m) :
    Tendsto (fun z => ‖p.eval z‖ * Real.exp (-N * complexLogPotential μ z))
      (cobounded ℂ) (𝓝 0) := by
  have hdegree : p.degree < (Polynomial.X ^ m : Polynomial ℂ).degree := by
    rw [Polynomial.degree_X_pow]
    exact p.degree_le_natDegree.trans_lt (by exact_mod_cast hdeg)
  have ho : p.eval =o[cobounded ℂ] (fun z : ℂ => z^m) := by
    simpa only [Polynomial.eval_pow, Polynomial.eval_X] using
      Polynomial.isLittleO_cobounded_of_degree_lt hdegree
  have hlim : Tendsto (fun z : ℂ => ‖p.eval z‖ / ‖z‖^m * (2:ℝ)^m)
      (cobounded ℂ) (𝓝 0) := by
    simpa only [norm_pow, zero_mul] using ho.norm_norm.tendsto_div_nhds_zero.mul_const ((2:ℝ)^m)
  apply squeeze_zero' (Eventually.of_forall (fun z => by positivity)) ?_ hlim
  filter_upwards [tendsto_norm_cobounded_atTop.eventually_ge_atTop (2*(B+1))] with z hz
  have hnorm : 0 < ‖z‖ := by linarith
  have hp := mul_le_mul_of_nonneg_left (complexLogPotential_ge_mass_log μ hB hsupport z hz (hlog z)) hN
  rw [← mul_assoc, hmass] at hp
  have he : Real.exp (-N * complexLogPotential μ z) ≤ (2:ℝ)^m / ‖z‖^m := by
    calc
      _ ≤ Real.exp (-((m:ℝ)*(Real.log ‖z‖-Real.log 2))) := by
        apply Real.exp_le_exp.2
        nlinarith
      _ = (2:ℝ)^m / ‖z‖^m := by
        rw [show -((m:ℝ)*(Real.log ‖z‖-Real.log 2)) =
          (m:ℝ)*Real.log 2-(m:ℝ)*Real.log ‖z‖ by ring]
        rw [Real.exp_sub, Real.exp_nat_mul, Real.exp_nat_mul,
          Real.exp_log (by norm_num : (0:ℝ)<2), Real.exp_log hnorm]
  calc
    _ ≤ ‖p.eval z‖ * ((2:ℝ)^m / ‖z‖^m) := mul_le_mul_of_nonneg_left he (norm_nonneg _)
    _ = _ := by ring

end Zeta3.Analysis

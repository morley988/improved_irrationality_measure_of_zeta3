import Zeta5.Analysis.ArcsinePotential

/-!
# The arcsine logarithmic potential at complex points

This extends the existing real circle-factorization proof to complex
evaluation points. The imaginary-axis formula supplies the actual contour
potential at its maximum point, independently of the finite interval checker.
-/

noncomputable section
namespace Zeta3.Analysis
open MeasureTheory Set Filter Metric Complex Real
open scoped ComplexConjugate

def complexArcsinePotential (b : ℝ) (w : ℂ) : ℝ :=
  Real.circleAverage (fun z : ℂ => Real.log ‖w - (b * z.re : ℝ)‖) 0 1

theorem complex_circle_quadratic_factor {b : ℝ} (hb : b ≠ 0) {w r₁ r₂ z : ℂ}
    (hprod : r₁ * r₂ = 1) (hsum : r₁ + r₂ = 2 * w / b) (hz : ‖z‖ = 1) :
    (b / 2 : ℝ) * ((z - r₁) * (z - r₂)) = ((b * z.re : ℝ) - w) * z := by
  have hzconj : z * conj z = 1 := by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, hz]
    norm_num
  have hzre : (z.re : ℂ) * 2 = z + conj z := by
    apply Complex.ext <;> simp <;> ring
  calc
    _ = (b : ℂ) / 2 * (z ^ 2 - (r₁ + r₂) * z + r₁ * r₂) := by push_cast; ring
    _ = (b : ℂ) / 2 * (z ^ 2 - (2 * w / b) * z + 1) := by rw [hprod, hsum]
    _ = ((b : ℂ) * (z + conj z) / 2 - w) * z := by
      rw [← hzconj]
      field_simp [Complex.ofReal_ne_zero.mpr hb]
      ring
    _ = _ := by rw [← hzre]; push_cast; ring

theorem complex_circle_log_factor {b : ℝ} (hb : 0 < b) {w r₁ r₂ z : ℂ}
    (hprod : r₁ * r₂ = 1) (hsum : r₁ + r₂ = 2 * w / b)
    (hz : ‖z‖ = 1) (hz₁ : z ≠ r₁) (hz₂ : z ≠ r₂) :
    Real.log ‖w - (b * z.re : ℝ)‖ =
      Real.log (b / 2) + Real.log ‖z - r₁‖ + Real.log ‖z - r₂‖ := by
  have hid := congrArg norm (complex_circle_quadratic_factor hb.ne' hprod hsum hz)
  simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs, hz, mul_one] at hid
  rw [abs_of_pos (div_pos hb (by norm_num))] at hid
  have hn₁ : ‖z - r₁‖ ≠ 0 := norm_ne_zero_iff.mpr (sub_ne_zero.mpr hz₁)
  have hn₂ : ‖z - r₂‖ ≠ 0 := norm_ne_zero_iff.mpr (sub_ne_zero.mpr hz₂)
  rw [norm_sub_rev w, ← hid, Real.log_mul (by positivity : b / 2 ≠ 0) (mul_ne_zero hn₁ hn₂),
    Real.log_mul hn₁ hn₂]
  ring

theorem complexArcsinePotential_factorization {b : ℝ} (hb : 0 < b) {w r₁ r₂ : ℂ}
    (hprod : r₁ * r₂ = 1) (hsum : r₁ + r₂ = 2 * w / b) :
    CircleIntegrable (fun z : ℂ => Real.log ‖w - (b * z.re : ℝ)‖) 0 1 ∧
      complexArcsinePotential b w = Real.log (b / 2) + Real.posLog ‖r₁‖ + Real.posLog ‖r₂‖ := by
  let g : ℂ → ℝ := fun z => Real.log (b / 2) + Real.log ‖z - r₁‖ + Real.log ‖z - r₂‖
  have hg1 : CircleIntegrable (fun z : ℂ => Real.log (b / 2) + Real.log ‖z - r₁‖) 0 1 :=
    (circleIntegrable_const _ _ _).add (circleIntegrable_log_norm_sub_const 1)
  have hg : CircleIntegrable g 0 1 := hg1.add (circleIntegrable_log_norm_sub_const 1)
  have heq : (fun z : ℂ => Real.log ‖w - (b * z.re : ℝ)‖) =ᶠ[
      codiscreteWithin (sphere (0 : ℂ) |(1 : ℝ)|)] g := by
    filter_upwards [self_mem_codiscreteWithin (sphere (0 : ℂ) |(1 : ℝ)|),
      compl_singleton_mem_codiscreteWithin r₁, compl_singleton_mem_codiscreteWithin r₂]
      with z hz hz₁ hz₂
    have hzn : ‖z‖ = 1 := by simpa only [abs_one, mem_sphere_iff_norm, sub_zero] using hz
    exact complex_circle_log_factor hb hprod hsum hzn hz₁ hz₂
  refine ⟨hg.congr_codiscreteWithin heq.symm, ?_⟩
  unfold complexArcsinePotential
  rw [circleAverage_congr_codiscreteWithin heq (by norm_num)]
  dsimp only [g]
  rw [circleAverage_fun_add hg1 (circleIntegrable_log_norm_sub_const 1),
    circleAverage_fun_add (circleIntegrable_const _ _ _) (circleIntegrable_log_norm_sub_const 1),
    circleAverage_const, circleAverage_log_norm_sub_const_eq_posLog,
    circleAverage_log_norm_sub_const_eq_posLog]

theorem complexArcsinePotential_imaginary {b u : ℝ} (hb : 0 < b) (hu : 0 < u) :
    CircleIntegrable (fun z : ℂ => Real.log ‖(u : ℂ) * I - (b * z.re : ℝ)‖) 0 1 ∧
      complexArcsinePotential b ((u : ℂ) * I) =
        Real.log ((u + Real.sqrt (u ^ 2 + b ^ 2)) / 2) := by
  let s : ℝ := Real.sqrt (u ^ 2 + b ^ 2)
  let R : ℝ := (u + s) / b
  have hs : 0 < s := by dsimp [s]; positivity
  have hsq : s ^ 2 = u ^ 2 + b ^ 2 := Real.sq_sqrt (by positivity)
  have hbs : b ≤ s := by nlinarith
  have hR : 1 ≤ R := (le_div_iff₀ hb).2 (by linarith)
  have hRp : 0 < R := lt_of_lt_of_le zero_lt_one hR
  have hdiff : R - R⁻¹ = 2 * u / b := by
    dsimp [R]
    field_simp
    nlinarith
  have hprod : ((R : ℂ) * I) * (((R : ℂ) * I)⁻¹) = 1 := by
    apply mul_inv_cancel₀
    exact mul_ne_zero (Complex.ofReal_ne_zero.mpr hRp.ne') I_ne_zero
  have hsum : (R : ℂ) * I + ((R : ℂ) * I)⁻¹ = 2 * ((u : ℂ) * I) / b := by
    rw [mul_inv_rev, Complex.inv_I]
    have hd : (R : ℂ) - (R : ℂ)⁻¹ = 2 * (u : ℂ) / b := by exact_mod_cast hdiff
    linear_combination I * hd
  obtain ⟨hi, hv⟩ := complexArcsinePotential_factorization hb hprod hsum
  refine ⟨hi, ?_⟩
  have hnorm : ‖(R : ℂ) * I‖ = R := by simp [norm_mul, abs_of_pos hRp]
  have hpinv : Real.posLog ‖((R : ℂ) * I)⁻¹‖ = 0 := by
    apply (Real.posLog_eq_zero_iff _).mpr
    rw [abs_of_nonneg (norm_nonneg _), norm_inv, hnorm]
    exact inv_le_one_of_one_le₀ hR
  rw [hnorm, Real.posLog_eq_log (by simpa [abs_of_pos hRp] using hR), hpinv, add_zero] at hv
  rw [hv, ← Real.log_mul (by positivity : b / 2 ≠ 0) hRp.ne']
  congr 1
  dsimp [R, s]
  field_simp

end Zeta3.Analysis

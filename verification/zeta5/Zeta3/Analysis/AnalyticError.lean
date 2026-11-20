import Zeta5.Analysis.AnalyticError

/-! # The explicit cubic analytic remainder is negligible at quadratic scale -/

namespace Zeta3.Analysis
open Filter
open scoped Topology
noncomputable section

def windowScale (n : ℕ) : ℝ := (50 * (n : ℝ)) ^ 2

def analyticError (C d : ℝ) (n : ℕ) : ℝ :=
  Real.log (Nat.factorial (51 * n) : ℝ) + (51 * (n : ℝ)) *
    (C + 20 * Real.log (50 * (n : ℝ)) + Real.log (50 * (n : ℝ) + 1) + 2) +
      (50 * (n : ℝ)) * d

theorem factorial_over_windowScale_limit :
    Tendsto (fun n : ℕ => Real.log (Nat.factorial (51 * n) : ℝ) / windowScale n)
      atTop (𝓝 0) := by
  have hu := (Zeta5.Analysis.tendsto_log_mul_nat_div_nat 51 (by norm_num)).const_mul (51 / 2500 : ℝ)
  simp only [mul_zero] at hu
  apply squeeze_zero' _ _ hu
  · filter_upwards [] with n
    exact div_nonneg (Zeta5.Analysis.log_factorial_nonneg _) (sq_nonneg _)
  · filter_upwards [eventually_gt_atTop (0 : ℕ)] with n hn
    have hnpos : 0 < (n : ℝ) := by exact_mod_cast hn
    have h := div_le_div_of_nonneg_right (Zeta5.Analysis.log_factorial_le_mul_log (51 * n))
      (sq_nonneg (50 * (n : ℝ)))
    simp only [Nat.cast_mul, Nat.cast_ofNat] at h
    convert! h using 1
    field_simp
    ring

theorem analyticError_over_windowScale_limit (C d : ℝ) :
    Tendsto (fun n : ℕ => analyticError C d n / windowScale n) atTop (𝓝 0) := by
  have hnat : Tendsto (fun n : ℕ => ((n : ℝ))⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop
  have hc := hnat.const_mul ((51 * (C + 2) + 50 * d) / 2500)
  have hl := (Zeta5.Analysis.tendsto_log_mul_nat_div_nat 50 (by norm_num)).const_mul (1020 / 2500 : ℝ)
  have hl1 := (Zeta5.Analysis.tendsto_log_mul_nat_add_one_div_nat 50 (by norm_num)).const_mul (51 / 2500 : ℝ)
  have h := ((factorial_over_windowScale_limit.add hc).add hl).add hl1
  simp only [mul_zero, add_zero] at h
  apply h.congr'
  filter_upwards [eventually_gt_atTop (0 : ℕ)] with n hn
  have hnpos : 0 < (n : ℝ) := by exact_mod_cast hn
  unfold analyticError windowScale
  field_simp
  ring

end
end Zeta3.Analysis

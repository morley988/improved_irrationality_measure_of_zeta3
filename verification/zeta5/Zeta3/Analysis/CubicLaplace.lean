import Zeta3.Analysis.CubicDensity
import Zeta5.Analysis.PhysicalMeasureLaplace

/-! # Two rigorous Laplace integrations by parts for the cubic density -/

noncomputable section
namespace Zeta3.Analysis.PhysicalMeasure
open Real Set MeasureTheory Filter Polynomial
open scoped Topology BigOperators

def laplaceNumerator (y : ℝ) : ℕ → ℝ[X]
  | 0 => X ^ 3
  | k + 1 => (laplaceNumerator y k).derivative * (X ^ 2 + C (y ^ 2)) -
      C (2 * ((k + 1 : ℕ) : ℝ)) * X * laplaceNumerator y k

def laplaceKernel (k : ℕ) (y x : ℝ) : ℝ :=
  (laplaceNumerator y k).eval x / (x ^ 2 + y ^ 2) ^ (k + 1)

theorem laplaceKernel_hasDerivAt (k : ℕ) {y : ℝ} (hy : 0 < y) (x : ℝ) :
    HasDerivAt (laplaceKernel k y) (laplaceKernel (k + 1) y x) x :=
  Zeta5.Analysis.PhysicalMeasure.hasDerivAt_polynomial_div_quadratic
    (laplaceNumerator y k) k hy x

theorem laplaceKernel_exp_integrable (k : ℕ) {y r : ℝ} (hy : 0 < y) (hr : 0 < r) :
    IntegrableOn (fun x : ℝ => laplaceKernel k y x * Real.exp (-(r * x))) (Ioi 0) :=
  Zeta5.Analysis.PhysicalMeasure.polynomial_div_quadratic_exp_integrable _ k hy hr

theorem laplaceKernel_exp_tendsto_zero (k : ℕ) {y r : ℝ} (hr : 0 < r) :
    Tendsto (fun x : ℝ => laplaceKernel k y x * Real.exp (-(r * x))) atTop (𝓝 0) :=
  Zeta5.Analysis.PhysicalMeasure.polynomial_div_quadratic_exp_tendsto_zero _ k hr

theorem laplaceKernel_zero (k : ℕ) (hk : k < 2) (y : ℝ) : laplaceKernel k y 0 = 0 := by
  have hcases : k = 0 ∨ k = 1 := by omega
  rcases hcases with rfl | rfl <;>
    norm_num [laplaceKernel, laplaceNumerator, derivative_mul, derivative_pow,
      derivative_sub, derivative_add, map_mul, map_pow]

theorem laplaceKernel_two_integral {y r : ℝ} (hy : 0 < y) (hr : 0 < r) :
    (∫ x : ℝ in Ioi 0, laplaceKernel 2 y x * Real.exp (-(r * x))) =
      r ^ 2 * ∫ x : ℝ in Ioi 0, x ^ 3 / (x ^ 2 + y ^ 2) * Real.exp (-(r * x)) := by
  have hstep (k : ℕ) (hk : k < 2) :
      (∫ x : ℝ in Ioi 0, laplaceKernel (k + 1) y x * Real.exp (-(r * x))) =
        r * ∫ x : ℝ in Ioi 0, laplaceKernel k y x * Real.exp (-(r * x)) :=
    Zeta5.Analysis.PhysicalMeasure.laplace_integral_derivative
      (laplaceKernel_hasDerivAt k hy) (laplaceKernel_zero k hk y)
      (laplaceKernel_exp_integrable k hy hr) (laplaceKernel_exp_integrable (k + 1) hy hr)
      (laplaceKernel_exp_tendsto_zero k hr)
  rw [hstep 1 (by omega), hstep 0 (by omega)]
  simp only [laplaceKernel, laplaceNumerator, eval_pow, eval_X, zero_add, pow_one]
  ring

theorem laplaceKernel_two (y x : ℝ) :
    laplaceKernel 2 y x = 2 * x * y ^ 2 * (3 * y ^ 2 - x ^ 2) / (x ^ 2 + y ^ 2) ^ 3 := by
  unfold laplaceKernel
  congr 1
  norm_num [laplaceNumerator, derivative_mul, derivative_pow, derivative_sub, derivative_add,
    map_mul, map_pow, eval_sub, eval_add, eval_mul, eval_pow]
  <;> ring

theorem laplaceKernel_two_abs_le {y x : ℝ} (hy : 0 < y) (hx : 0 ≤ x) :
    |laplaceKernel 2 y x| ≤ (6 / y ^ 2) * x := by
  have hd : 0 < x ^ 2 + y ^ 2 := by positivity
  have hp : |3 * y ^ 2 - x ^ 2| ≤ 3 * (x ^ 2 + y ^ 2) := by
    apply abs_le.mpr
    constructor <;> nlinarith [sq_nonneg x, sq_nonneg y]
  have hden : y ^ 2 / (x ^ 2 + y ^ 2) ^ 2 ≤ 1 / y ^ 2 := by
    apply (div_le_div_iff₀ (pow_pos hd 2) (sq_pos_of_pos hy)).mpr
    have h := pow_le_pow_left₀ (sq_nonneg y)
      (by nlinarith [sq_nonneg x] : y ^ 2 ≤ x ^ 2 + y ^ 2) 2
    nlinarith
  rw [laplaceKernel_two, abs_div, abs_mul, abs_mul, abs_mul,
    abs_of_pos (by norm_num : (0 : ℝ) < 2), abs_of_nonneg hx,
    abs_of_nonneg (sq_nonneg y), abs_of_pos (pow_pos hd 3)]
  calc
    _ ≤ 2 * x * y ^ 2 * (3 * (x ^ 2 + y ^ 2)) / (x ^ 2 + y ^ 2) ^ 3 := by gcongr
    _ = (6 * x) * (y ^ 2 / (x ^ 2 + y ^ 2) ^ 2) := by field_simp; ring
    _ ≤ (6 * x) * (1 / y ^ 2) := mul_le_mul_of_nonneg_left hden (by positivity)
    _ = _ := by ring

end Zeta3.Analysis.PhysicalMeasure

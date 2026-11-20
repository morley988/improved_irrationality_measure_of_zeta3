import Zeta3.Analysis.AngularZeros
import Zeta3.Analysis.ContourNormIntegral

/-! # Physical norm gain from the actual angular polynomial factor -/

noncomputable section
namespace Zeta3.Analysis
open MeasureTheory Set Polynomial

theorem angularZeroProduct_normalized_norm_lower {m : ℕ} (a : ℝ) (h : Fin m → ℝ)
    (ha : 0 ≤ a) (hh : ∀ j, h j ≤ 1) (N m₁ m₂ : ℕ) (hN : 0 < N) (p : ℝ[X]) :
    a^(4*m)*normalizedPhysicalNorm N m₁ m₂ p ≤
      normalizedPhysicalNorm N m₁ m₂ (angularZeroProduct a h*p) := by
  rw [normalizedPhysicalNorm_integral N m₁ m₂ hN,
    normalizedPhysicalNorm_integral N m₁ m₂ hN, ← integral_const_mul]
  apply integral_mono_ae
    ((physicalScaledDensity_polynomial_integrable N m₁ m₂ hN p).const_mul _)
    (physicalScaledDensity_polynomial_integrable N m₁ m₂ hN _)
  filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with x hx
  rw [Polynomial.eval_mul, mul_pow]
  have hb := angularZeroProduct_physical_square_lower a h x ha hh hx.le
  have hm := mul_le_mul_of_nonneg_right hb
    (mul_nonneg (sq_nonneg (p.eval x)) (physicalScaledDensity_nonneg N m₁ m₂ hN hx.le))
  nlinarith only [hm]

end Zeta3.Analysis

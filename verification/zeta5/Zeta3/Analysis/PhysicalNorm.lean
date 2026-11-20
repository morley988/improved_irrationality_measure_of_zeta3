import Zeta3.Analysis.CubicPositivity
import Zeta3.Analysis.CubicDensityBound
import Zeta3.Analysis.PhysicalTrial
import Zeta5.Analysis.RiemannWeight

/-! # Exact scaled-weight bounds for the actual unequal-window cubic norm -/

noncomputable section
namespace Zeta3.Analysis
open Real Set MeasureTheory Filter Polynomial
open scoped Topology BigOperators

def physicalCommonWeight (N m₁ m₂ : ℕ) (x : ℝ) : ℝ :=
  (PhysicalMeasure.realPositiveFactor m₁).eval (x ^ 2) *
    (PhysicalMeasure.realPositiveFactor m₂).eval (x ^ 2) * PhysicalMeasure.weightedDensity N x

def physicalWeightScale (N m₁ m₂ : ℕ) : ℝ :=
  (N : ℝ) ^ (2 * (m₁ + m₂)) / (N : ℝ) ^ (2 * N)

def windowSquaredNorm (N m₁ m₂ : ℕ) (P : ℝ[X]) : ℝ :=
  PhysicalMeasure.windowMomentFunctional N m₁ m₂ (P ^ 2)

theorem windowSquaredNorm_integral (N m₁ m₂ : ℕ) (P : ℝ[X]) :
    windowSquaredNorm N m₁ m₂ P = ∫ x : ℝ in Ioi 0,
      P.eval (x ^ 2) ^ 2 * physicalCommonWeight N m₁ m₂ x := by
  simp only [windowSquaredNorm, PhysicalMeasure.windowMomentFunctional,
    LinearMap.comp_apply, LinearMap.mulLeft_apply, PhysicalMeasure.momentFunctional_apply,
    eval_mul, eval_pow, physicalCommonWeight]
  congr 1
  funext x
  ring

theorem windowSquaredNorm_integrable (N m₁ m₂ : ℕ) (P : ℝ[X]) :
    IntegrableOn (fun x : ℝ => P.eval (x ^ 2) ^ 2 * physicalCommonWeight N m₁ m₂ x) (Ioi 0) := by
  have h := PhysicalMeasure.weighted_polynomial_integrable N
    (PhysicalMeasure.realPositiveFactor m₁ * PhysicalMeasure.realPositiveFactor m₂ * P ^ 2)
  simpa only [eval_mul, eval_pow, physicalCommonWeight, mul_assoc, mul_comm, mul_left_comm] using h

theorem windowSquaredNorm_pos_of_monic (N m₁ m₂ : ℕ) {P : ℝ[X]} (hP : P.Monic) :
    0 < windowSquaredNorm N m₁ m₂ P :=
  PhysicalMeasure.windowMomentFunctional_square_pos N m₁ m₂ P hP.ne_zero

theorem physicalWeightScale_pos {N : ℕ} (hN : 0 < N) (m₁ m₂ : ℕ) :
    0 < physicalWeightScale N m₁ m₂ := by unfold physicalWeightScale; positivity

theorem realPositiveFactor_riemann_upper (N m : ℕ) (hN : 0 < N) {y : ℝ} (hy : 0 < y) :
    (PhysicalMeasure.realPositiveFactor m).eval ((N : ℝ) ^ 2 * y ^ 2) ≤
      (N : ℝ) ^ (2 * m) * Real.exp ((N : ℝ) * Zeta5.Analysis.externalIntegral ((m : ℝ) / N) y) := by
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have hgrid := (Zeta5.Analysis.logarithmic_grid_bounds hy hNr m).1
  simp only [PhysicalMeasure.realPositiveFactor, Zeta3.Construction.positiveFactor,
    Polynomial.map_prod, Polynomial.map_add, Polynomial.map_X, Polynomial.map_C,
    eval_prod, eval_add, eval_X, eval_C, Rat.coe_castHom, Rat.cast_pow, Rat.cast_natCast]
  have hscale := Zeta5.Analysis.shifted_square_product_scale hNr m y 0
  simp only [Nat.add_zero] at hscale
  rw [hscale]
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  have h := Real.exp_le_exp.mpr hgrid
  rw [Real.exp_sum] at h
  have he (i : ℕ) : Real.exp (Real.log (y ^ 2 + ((i : ℝ) / N) ^ 2)) =
      y ^ 2 + ((i : ℝ) / N) ^ 2 := Real.exp_log (by positivity)
  simpa only [he] using h

theorem physicalCommonWeight_scaled_bound {C : ℝ} (hC : 0 < C)
    (hdensity : ∀ x : ℝ, 0 < x → PhysicalMeasure.density x ≤
      C * (1 + x ^ 3) * Real.exp (-(2 * Real.pi * x)))
    (N m₁ m₂ : ℕ) (hN : 0 < N) {y : ℝ} (hy : 0 < y) :
    physicalCommonWeight N m₁ m₂ ((N : ℝ) * y) ≤
      C * (N : ℝ) ^ 3 * physicalWeightScale N m₁ m₂ * (1 + y ^ 3) *
        Real.exp (-(N : ℝ) * physicalField ((m₁ : ℝ) / N) ((m₂ : ℝ) / N) y) := by
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hB₁ := realPositiveFactor_riemann_upper N m₁ hN hy
  have hB₂ := realPositiveFactor_riemann_upper N m₂ hN hy
  have hD := Zeta5.Analysis.realDenominator_riemann_lower N hN hy
  have hd := hdensity ((N : ℝ) * y) (mul_pos hNr hy)
  have hpoly : 1 + ((N : ℝ) * y) ^ 3 ≤ (N : ℝ) ^ 3 * (1 + y ^ 3) := by
    have h : (1 : ℝ) ≤ (N : ℝ) ^ 3 := one_le_pow₀ hN1
    rw [mul_pow]
    nlinarith
  have hd' : PhysicalMeasure.density ((N : ℝ) * y) ≤
      C * (N : ℝ) ^ 3 * (1 + y ^ 3) * Real.exp (-(2 * Real.pi * ((N : ℝ) * y))) := by
    apply hd.trans
    simpa only [mul_assoc] using mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hpoly hC.le) (Real.exp_nonneg _)
  have hB : (PhysicalMeasure.realPositiveFactor m₁).eval ((N : ℝ) ^ 2 * y ^ 2) *
      (PhysicalMeasure.realPositiveFactor m₂).eval ((N : ℝ) ^ 2 * y ^ 2) ≤
      (N : ℝ) ^ (2 * (m₁ + m₂)) * Real.exp ((N : ℝ) *
        (Zeta5.Analysis.externalIntegral ((m₁ : ℝ) / N) y +
          Zeta5.Analysis.externalIntegral ((m₂ : ℝ) / N) y)) := by
    have h := mul_le_mul hB₁ hB₂
      (PhysicalMeasure.realPositiveFactor_eval_pos m₂ (by positivity)).le (by positivity)
    apply h.trans_eq
    rw [show 2 * (m₁ + m₂) = 2 * m₁ + 2 * m₂ by omega, pow_add,
      mul_add, Real.exp_add]
    ring
  have hDpos : 0 < (N : ℝ) ^ (2 * N) * Real.exp ((N : ℝ) * Zeta5.Analysis.externalIntegral 1 y) :=
    by positivity
  unfold physicalCommonWeight PhysicalMeasure.weightedDensity
  rw [mul_pow]
  calc
    _ ≤ ((N : ℝ) ^ (2 * (m₁ + m₂)) * Real.exp ((N : ℝ) *
        (Zeta5.Analysis.externalIntegral ((m₁ : ℝ) / N) y +
          Zeta5.Analysis.externalIntegral ((m₂ : ℝ) / N) y))) *
      ((C * (N : ℝ) ^ 3 * (1 + y ^ 3) * Real.exp (-(2 * Real.pi * ((N : ℝ) * y)))) /
        ((N : ℝ) ^ (2 * N) * Real.exp ((N : ℝ) * Zeta5.Analysis.externalIntegral 1 y))) := by
      apply mul_le_mul hB _
        (div_nonneg (PhysicalMeasure.density_pos (mul_pos hNr hy)).le
          (PhysicalMeasure.realDenominator_eval_pos N (by positivity)).le) (by positivity)
      exact div_le_div₀ (by positivity) hd' hDpos hD
    _ = _ := by
      have hexp : Real.exp ((N : ℝ) * (Zeta5.Analysis.externalIntegral ((m₁ : ℝ) / N) y +
          Zeta5.Analysis.externalIntegral ((m₂ : ℝ) / N) y)) *
          Real.exp (-(2 * Real.pi * ((N : ℝ) * y))) /
          Real.exp ((N : ℝ) * Zeta5.Analysis.externalIntegral 1 y) =
          Real.exp (-(N : ℝ) * physicalField ((m₁ : ℝ) / N) ((m₂ : ℝ) / N) y) := by
        rw [← Real.exp_add, ← Real.exp_sub]
        congr 1
        unfold physicalField
        ring
      unfold physicalWeightScale
      calc
        _ = (C * (N : ℝ) ^ 3 * ((N : ℝ) ^ (2 * (m₁ + m₂)) / (N : ℝ) ^ (2 * N)) *
            (1 + y ^ 3)) * (Real.exp ((N : ℝ) * (Zeta5.Analysis.externalIntegral ((m₁ : ℝ) / N) y +
              Zeta5.Analysis.externalIntegral ((m₂ : ℝ) / N) y)) *
            Real.exp (-(2 * Real.pi * ((N : ℝ) * y))) /
              Real.exp ((N : ℝ) * Zeta5.Analysis.externalIntegral 1 y)) := by ring
        _ = _ := by rw [hexp]

end Zeta3.Analysis

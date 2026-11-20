import Zeta3.Analysis.ContourDensity
import Zeta3.Analysis.ContourWeightedNorm
import Zeta3.Analysis.PhysicalNormTrial

/-!
# Exact normalization and the actual physical norm comparison

This file identifies the scaled `z`-density with the original cubic Gram
integral by the substitutions `x = Ny` and `z = y²`.  The finite weighted
comparison is therefore an estimate for the actual physical quadratic form,
not for a separately postulated proxy weight.
-/

noncomputable section
open Real Set MeasureTheory Filter Polynomial

namespace Zeta3.Analysis

def physicalRescalePolynomial (N : ℕ) (q : ℝ[X]) : ℝ[X] :=
  q.comp (C (((N:ℝ)^2)⁻¹)*X)

def normalizedPhysicalNorm (N m₁ m₂ : ℕ) (q : ℝ[X]) : ℝ :=
  windowSquaredNorm N m₁ m₂ (physicalRescalePolynomial N q)/physicalWeightScale N m₁ m₂

theorem physicalRescalePolynomial_eval (N : ℕ) (hN : 0 < N) (q : ℝ[X]) (y : ℝ) :
    (physicalRescalePolynomial N q).eval ((N:ℝ)^2*y^2) = q.eval (y^2) := by
  have hNr : (N:ℝ) ≠ 0 := by exact_mod_cast hN.ne'
  simp only [physicalRescalePolynomial, eval_comp, eval_mul, eval_C, eval_X]
  congr 1
  field_simp

private theorem physical_square_jacobian (N m₁ m₂ : ℕ) (q : ℝ[X])
    {y : ℝ} (hy : 0 < y) :
    (2*y)*(q.eval (y^2)^2*physicalScaledDensity N m₁ m₂ (y^2)) =
      ((N:ℝ)/physicalWeightScale N m₁ m₂)*
        (q.eval (y^2)^2*physicalCommonWeight N m₁ m₂ ((N:ℝ)*y)) := by
  rw [physicalScaledDensity, Real.sqrt_sq hy.le]
  field_simp

theorem scaled_polynomial_physical_integrable (N m₁ m₂ : ℕ) (hN : 0 < N) (q : ℝ[X]) :
    IntegrableOn (fun y => q.eval (y^2)^2*physicalCommonWeight N m₁ m₂ ((N:ℝ)*y)) (Ioi 0) := by
  have hNr : (0:ℝ)<N := by exact_mod_cast hN
  have hi := (integrableOn_Ioi_comp_mul_left_iff
    (fun x => (physicalRescalePolynomial N q).eval (x^2)^2*physicalCommonWeight N m₁ m₂ x)
    0 hNr).mpr (by simpa only [mul_zero] using
      windowSquaredNorm_integrable N m₁ m₂ (physicalRescalePolynomial N q))
  simpa only [mul_pow, physicalRescalePolynomial_eval N hN q] using hi

theorem physicalScaledDensity_polynomial_integrable (N m₁ m₂ : ℕ) (hN : 0 < N) (q : ℝ[X]) :
    IntegrableOn (fun z => q.eval z^2*physicalScaledDensity N m₁ m₂ z) (Ioi 0) := by
  have hi := (scaled_polynomial_physical_integrable N m₁ m₂ hN q).const_mul
    ((N:ℝ)/physicalWeightScale N m₁ m₂)
  have hj : IntegrableOn (fun y => (2*y)*(q.eval (y^2)^2*physicalScaledDensity N m₁ m₂ (y^2)))
      (Ioi 0) := by
    apply hi.congr
    filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with y hy
    exact (physical_square_jacobian N m₁ m₂ q hy).symm
  have hr := integrableOn_Ioi_comp_rpow_iff
    (fun z => q.eval z^2*physicalScaledDensity N m₁ m₂ z) (p := 2) (by norm_num : (2:ℝ)≠0)
  norm_num only [show |(2:ℝ)|=2 by norm_num, show (2:ℝ)-1=1 by norm_num, Real.rpow_one,
    Real.rpow_two, smul_eq_mul] at hr
  exact hr.mp hj

theorem normalizedPhysicalNorm_integral (N m₁ m₂ : ℕ) (hN : 0 < N) (q : ℝ[X]) :
    normalizedPhysicalNorm N m₁ m₂ q =
      ∫ z : ℝ in Ioi 0, q.eval z^2*physicalScaledDensity N m₁ m₂ z := by
  have hJ := integral_comp_rpow_Ioi
    (fun z => q.eval z^2*physicalScaledDensity N m₁ m₂ z) (p := 2) (by norm_num : (2:ℝ)≠0)
  norm_num only [show |(2:ℝ)|=2 by norm_num, show (2:ℝ)-1=1 by norm_num, Real.rpow_one,
    Real.rpow_two, smul_eq_mul] at hJ
  have hJac : (∫ y : ℝ in Ioi 0,
      (2*y)*(q.eval (y^2)^2*physicalScaledDensity N m₁ m₂ (y^2))) =
      ((N:ℝ)/physicalWeightScale N m₁ m₂)*
        (∫ y : ℝ in Ioi 0, q.eval (y^2)^2*physicalCommonWeight N m₁ m₂ ((N:ℝ)*y)) := by
    rw [← integral_const_mul]
    exact setIntegral_congr_fun measurableSet_Ioi (fun y hy => physical_square_jacobian N m₁ m₂ q hy)
  rw [← hJ, hJac]
  unfold normalizedPhysicalNorm
  rw [windowSquaredNorm_scaled N m₁ m₂ hN]
  simp only [physicalRescalePolynomial_eval N hN q]
  ring

theorem physicalScaledDensity_intervalIntegrable (N m₁ m₂ : ℕ) (hN : 0 < N) (q : ℝ[X])
    {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) :
    IntervalIntegrable (fun z => physicalScaledDensity N m₁ m₂ z*q.eval z^2) volume a b := by
  apply (intervalIntegrable_iff_integrableOn_Ioc_of_le hab).mpr
  have hi := (physicalScaledDensity_polynomial_integrable N m₁ m₂ hN q).mono_set
    (show Ioc a b ⊆ Ioi 0 from fun z hz => lt_of_le_of_lt ha hz.1)
  simpa only [mul_comm] using hi

theorem physicalScaledDensity_interval_le_norm (N m₁ m₂ : ℕ) (hN : 0 < N) (q : ℝ[X])
    {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) :
    (∫ z in a..b, physicalScaledDensity N m₁ m₂ z*q.eval z^2) ≤
      normalizedPhysicalNorm N m₁ m₂ q := by
  rw [normalizedPhysicalNorm_integral N m₁ m₂ hN, intervalIntegral.integral_of_le hab]
  have hi := physicalScaledDensity_polynomial_integrable N m₁ m₂ hN q
  have hnonneg : 0 ≤ᵐ[volume.restrict (Ioi (0:ℝ))]
      (fun z => q.eval z^2*physicalScaledDensity N m₁ m₂ z) := by
    filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with z hz
    exact mul_nonneg (sq_nonneg _) (physicalScaledDensity_nonneg N m₁ m₂ hN hz.le)
  have hm := setIntegral_mono_set hi hnonneg
    (show Ioc a b ⊆ Ioi 0 from fun z hz => lt_of_le_of_lt ha hz.1).eventuallyLE
  simpa only [mul_comm] using hm

/-- The finite real-axis norm comparison for the actual cubic weight.
Every factor in its right-hand side is independent of the polynomial. -/
theorem actual_physical_weighted_value_sq_le_norm
    (q : ℝ[X]) (n N m₁ m₂ : ℕ) (a b x R : ℝ)
    (hd : q.natDegree ≤ n) (hN : 0 < N) (hm₁ : 0 < m₁) (hm₂ : 0 < m₂)
    (ha : 0 ≤ a) (hab : a < b) (hbR : b ≤ R) (hx : x ∈ Icc a b)
    (hQ : 0 < |q.eval x|)
    (hmax : ∀ y ∈ Icc a b,
      |q.eval y| * Real.exp (-(N:ℝ)*physicalField ((m₁:ℝ)/N) ((m₂:ℝ)/N) (Real.sqrt y)/2) ≤
        |q.eval x| * Real.exp (-(N:ℝ)*physicalField ((m₁:ℝ)/N) ((m₂:ℝ)/N) (Real.sqrt x)/2)) :
    q.eval x^2*Real.exp (-(N:ℝ)*physicalField ((m₁:ℝ)/N) ((m₂:ℝ)/N) (Real.sqrt x)) ≤
      (8/(physicalPersistenceRadius n N a b*
        physicalDensityCompactConstant ((m₁:ℝ)/N) ((m₂:ℝ)/N) R*
          (physicalPersistenceRadius n N a b/2)^4))*
        Real.exp ((N:ℝ)*physicalFieldOscillation a b)*normalizedPhysicalNorm N m₁ m₂ q := by
  have hNr : (0:ℝ)<N := by exact_mod_cast hN
  have hR : 0 < R := lt_of_lt_of_le (lt_of_le_of_lt ha hab) hbR
  have hκ := physicalDensityCompactConstant_pos ((m₁:ℝ)/N) ((m₂:ℝ)/N) R hR
  have h := physical_weighted_value_sq_le_integral q n 4 ((m₁:ℝ)/N) ((m₂:ℝ)/N) N a b x
    (physicalDensityCompactConstant ((m₁:ℝ)/N) ((m₂:ℝ)/N) R)
    (physicalScaledDensity N m₁ m₂) hd (by positivity) (by positivity)
    hNr.le ha hab hx hκ hQ hmax
    (fun y hy => physicalScaledDensity_nonneg N m₁ m₂ hN (ha.trans hy.1))
    (fun y hy => physicalScaledDensity_compact_lower N m₁ m₂ hN R hR ⟨ha.trans hy.1,hy.2.trans hbR⟩)
    (physicalScaledDensity_intervalIntegrable N m₁ m₂ hN q ha hab.le)
  exact h.trans (mul_le_mul_of_nonneg_left
    (physicalScaledDensity_interval_le_norm N m₁ m₂ hN q ha hab.le)
      (by positivity [physicalPersistenceRadius_pos n N a b hab]))

end Zeta3.Analysis

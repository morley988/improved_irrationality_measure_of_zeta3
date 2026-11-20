import Zeta3.Analysis.PhysicalNorm

/-!
# Lower bounds for the actual physical weight

The first positive exponential summand already gives a sufficient density
lower bound.  Exact endpoint corrections to the monotone logarithmic sums
then give lower bounds for both numerator windows and an upper bound for
the denominator.  After squaring the variable this yields a fixed fourth
power at the origin, which is sufficient for the uniform local norm bound.
-/

noncomputable section
open Real Set MeasureTheory Filter Polynomial Finset
open scoped BigOperators

namespace Zeta3.Analysis

theorem cubic_density_first_term_lower {x : ℝ} (hx : 0 < x) :
    (2*Real.pi)^2*x^3*Real.exp (-(2*Real.pi*x)) ≤ PhysicalMeasure.density x := by
  have h := (PhysicalMeasure.expTerm_summable hx).le_tsum 0
    (fun n _ => (PhysicalMeasure.expTerm_pos n x).le)
  have h' := mul_le_mul_of_nonneg_left h (by positivity : 0 ≤ (2*Real.pi)^2*x^3)
  simpa [PhysicalMeasure.expTerm, PhysicalMeasure.density] using h'

private theorem sum_shift_identity (f : ℕ → ℝ) (m : ℕ) :
    (∑ i ∈ range m, f (i+1)) = (∑ i ∈ range m, f i)+f m-f 0 := by
  have h := Finset.sum_range_sub f m
  rw [Finset.sum_sub_distrib] at h
  linarith

theorem logarithmic_grid_bounds_with_correction {y N : ℝ} (hy : 0 < y) (hN : 0 < N) (m : ℕ) :
    N*Zeta5.Analysis.externalIntegral ((m:ℝ)/N) y + Real.log (y^2) -
      Real.log (y^2+((m:ℝ)/N)^2) ≤
        ∑ i ∈ range m, Real.log (y^2+((i:ℝ)/N)^2) ∧
    (∑ i ∈ range m, Real.log (y^2+(((i+1:ℕ):ℝ)/N)^2)) ≤
      N*Zeta5.Analysis.externalIntegral ((m:ℝ)/N) y +
        Real.log (y^2+((m:ℝ)/N)^2)-Real.log (y^2) := by
  have hb := Zeta5.Analysis.logarithmic_grid_bounds hy hN m
  have he := sum_shift_identity (fun i => Real.log (y^2+((i:ℝ)/N)^2)) m
  simp only [Nat.cast_zero, zero_div, zero_pow (by decide : 2 ≠ 0), add_zero] at he
  constructor <;> linarith [hb.1,hb.2]

theorem realPositiveFactor_riemann_lower (N m : ℕ) (hN : 0 < N) {y : ℝ} (hy : 0 < y) :
    (N:ℝ)^(2*m)*Real.exp ((N:ℝ)*Zeta5.Analysis.externalIntegral ((m:ℝ)/N) y)*
        (y^2/(y^2+((m:ℝ)/N)^2)) ≤
      (PhysicalMeasure.realPositiveFactor m).eval ((N:ℝ)^2*y^2) := by
  have hNr : (0:ℝ)<N := by exact_mod_cast hN
  have hgrid := (logarithmic_grid_bounds_with_correction hy hNr m).1
  simp only [PhysicalMeasure.realPositiveFactor, Zeta3.Construction.positiveFactor,
    Polynomial.map_prod, Polynomial.map_add, Polynomial.map_X, Polynomial.map_C,
    eval_prod, eval_add, eval_X, eval_C, Rat.coe_castHom, Rat.cast_pow, Rat.cast_natCast]
  have hscale := Zeta5.Analysis.shifted_square_product_scale hNr m y 0
  simp only [Nat.add_zero] at hscale
  rw [hscale, mul_assoc]
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  have h := Real.exp_le_exp.mpr hgrid
  rw [Real.exp_sub, Real.exp_add, Real.exp_log (by positivity : 0 < y^2),
    Real.exp_log (by positivity : 0 < y^2+((m:ℝ)/N)^2), Real.exp_sum] at h
  have he (i : ℕ) : Real.exp (Real.log (y^2+((i:ℝ)/N)^2)) =
      y^2+((i:ℝ)/N)^2 := Real.exp_log (by positivity)
  simpa only [he, mul_div_assoc] using h

theorem realDenominator_riemann_upper (N : ℕ) (hN : 0 < N) {y : ℝ} (hy : 0 < y) :
    (PhysicalMeasure.realDenominator N).eval ((N:ℝ)^2*y^2) ≤
      (N:ℝ)^(2*N)*Real.exp ((N:ℝ)*Zeta5.Analysis.externalIntegral 1 y)*
        ((y^2+1)/y^2) := by
  have hNr : (0:ℝ)<N := by exact_mod_cast hN
  have hgrid := (logarithmic_grid_bounds_with_correction hy hNr N).2
  rw [div_self hNr.ne', one_pow] at hgrid
  change (Zeta5.Analysis.PhysicalMeasure.realDenominator N).eval _ ≤ _
  rw [Zeta5.Analysis.realDenominator_scaled N hN, mul_assoc]
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  have h := Real.exp_le_exp.mpr hgrid
  rw [Real.exp_sub, Real.exp_add, Real.exp_log (by positivity : 0 < y^2+1),
    Real.exp_log (by positivity : 0 < y^2), Real.exp_sum] at h
  have he (i : ℕ) : Real.exp (Real.log (y^2+(((i+1:ℕ):ℝ)/N)^2)) =
      y^2+(((i+1:ℕ):ℝ)/N)^2 := Real.exp_log (by positivity)
  simpa only [he, mul_div_assoc] using h

/-- Exact lower bound before the square change of variable. -/
theorem physicalCommonWeight_scaled_lower (N m₁ m₂ : ℕ) (hN : 0 < N)
    {y : ℝ} (hy : 0 < y) :
    (2*Real.pi)^2*(N:ℝ)^3*physicalWeightScale N m₁ m₂ *
      (y^9/((y^2+((m₁:ℝ)/N)^2)*(y^2+((m₂:ℝ)/N)^2)*(y^2+1)))*
        Real.exp (-(N:ℝ)*physicalField ((m₁:ℝ)/N) ((m₂:ℝ)/N) y) ≤
      physicalCommonWeight N m₁ m₂ ((N:ℝ)*y) := by
  have hNr : (0:ℝ)<N := by exact_mod_cast hN
  have h1 := realPositiveFactor_riemann_lower N m₁ hN hy
  have h2 := realPositiveFactor_riemann_lower N m₂ hN hy
  have hD := realDenominator_riemann_upper N hN hy
  have hd := cubic_density_first_term_lower (mul_pos hNr hy)
  have hDpos : 0 < (PhysicalMeasure.realDenominator N).eval ((N:ℝ)^2*y^2) :=
    PhysicalMeasure.realDenominator_eval_pos N (by positivity)
  have hDupperpos : 0 < (N:ℝ)^(2*N)*Real.exp ((N:ℝ)*Zeta5.Analysis.externalIntegral 1 y)*
      ((y^2+1)/y^2) := by positivity
  have hnum := mul_le_mul h1 h2 (by positivity)
    (PhysicalMeasure.realPositiveFactor_eval_pos m₁ (by positivity)).le
  have hquot := div_le_div₀ (PhysicalMeasure.density_pos (mul_pos hNr hy)).le hd hDpos hD
  have hprod := mul_le_mul hnum hquot (by positivity)
    (mul_nonneg (PhysicalMeasure.realPositiveFactor_eval_pos m₁ (by positivity)).le
      (PhysicalMeasure.realPositiveFactor_eval_pos m₂ (by positivity)).le)
  have hexp : Real.exp ((N:ℝ)*Zeta5.Analysis.externalIntegral ((m₁:ℝ)/N) y)*
      Real.exp ((N:ℝ)*Zeta5.Analysis.externalIntegral ((m₂:ℝ)/N) y)*
      Real.exp (-(2*Real.pi*((N:ℝ)*y)))/Real.exp ((N:ℝ)*Zeta5.Analysis.externalIntegral 1 y) =
      Real.exp (-(N:ℝ)*physicalField ((m₁:ℝ)/N) ((m₂:ℝ)/N) y) := by
    rw [← Real.exp_add, ← Real.exp_add, ← Real.exp_sub]
    congr 1
    unfold physicalField
    ring
  change _ ≤ physicalCommonWeight N m₁ m₂ ((N:ℝ)*y)
  have hright :
      (PhysicalMeasure.realPositiveFactor m₁).eval ((N:ℝ)^2*y^2)*
      (PhysicalMeasure.realPositiveFactor m₂).eval ((N:ℝ)^2*y^2)*
      (PhysicalMeasure.density ((N:ℝ)*y)/(PhysicalMeasure.realDenominator N).eval ((N:ℝ)^2*y^2)) =
      physicalCommonWeight N m₁ m₂ ((N:ℝ)*y) := by
    simp only [physicalCommonWeight, PhysicalMeasure.weightedDensity, mul_pow]
  rw [hright] at hprod
  refine (le_of_eq ?_).trans hprod
  rw [← hexp]
  unfold physicalWeightScale
  rw [show 2*(m₁+m₂)=2*m₁+2*m₂ by omega, pow_add]
  field_simp
  <;> ring

/-- The normalized density in the polynomial variable `z = (x/N)²`. -/
def physicalScaledDensity (N m₁ m₂ : ℕ) (z : ℝ) : ℝ :=
  ((N:ℝ)/(2*Real.sqrt z))*physicalCommonWeight N m₁ m₂ ((N:ℝ)*Real.sqrt z)/
    physicalWeightScale N m₁ m₂

theorem physicalScaledDensity_lower (N m₁ m₂ : ℕ) (hN : 0 < N)
    {z : ℝ} (hz : 0 < z) :
    2*Real.pi^2*(N:ℝ)^4 *
      (z^4/((z+((m₁:ℝ)/N)^2)*(z+((m₂:ℝ)/N)^2)*(z+1)))*
        Real.exp (-(N:ℝ)*physicalField ((m₁:ℝ)/N) ((m₂:ℝ)/N) (Real.sqrt z)) ≤
      physicalScaledDensity N m₁ m₂ z := by
  have hs : 0 < Real.sqrt z := Real.sqrt_pos.mpr hz
  have hNr : (0:ℝ)<N := by exact_mod_cast hN
  have hW := physicalWeightScale_pos hN m₁ m₂
  have h := div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_left (physicalCommonWeight_scaled_lower N m₁ m₂ hN hs)
      (by positivity : 0 ≤ (N:ℝ)/(2*Real.sqrt z))) hW.le
  change _ ≤ physicalScaledDensity N m₁ m₂ z at h
  refine (le_of_eq ?_).trans h
  rw [show (Real.sqrt z)^9 = ((Real.sqrt z)^2)^4*Real.sqrt z by ring,
    Real.sq_sqrt hz.le]
  field_simp [hs.ne', hW.ne']
  <;> ring

@[simp] theorem physicalScaledDensity_zero (N m₁ m₂ : ℕ) :
    physicalScaledDensity N m₁ m₂ 0 = 0 := by
  simp [physicalScaledDensity]

theorem physicalScaledDensity_nonneg (N m₁ m₂ : ℕ) (hN : 0 < N)
    {z : ℝ} (hz : 0 ≤ z) : 0 ≤ physicalScaledDensity N m₁ m₂ z := by
  rcases eq_or_lt_of_le hz with rfl | hz
  · simp
  · exact le_trans (by positivity) (physicalScaledDensity_lower N m₁ m₂ hN hz)

def physicalDensityCompactConstant (s₁ s₂ R : ℝ) : ℝ :=
  2*Real.pi^2/((R+s₁^2)*(R+s₂^2)*(R+1))

theorem physicalDensityCompactConstant_pos (s₁ s₂ R : ℝ) (hR : 0 < R) :
    0 < physicalDensityCompactConstant s₁ s₂ R := by
  unfold physicalDensityCompactConstant
  positivity

/-- A fixed positive constant works on any fixed compact interval,
uniformly in the scaling parameter `N ≥ 1`. -/
theorem physicalScaledDensity_compact_lower (N m₁ m₂ : ℕ) (hN : 0 < N)
    (R : ℝ) (hR : 0 < R) {z : ℝ} (hz : z ∈ Icc 0 R) :
    physicalDensityCompactConstant ((m₁:ℝ)/N) ((m₂:ℝ)/N) R * z^4 *
      Real.exp (-(N:ℝ)*physicalField ((m₁:ℝ)/N) ((m₂:ℝ)/N) (Real.sqrt z)) ≤
      physicalScaledDensity N m₁ m₂ z := by
  rcases eq_or_lt_of_le hz.1 with hz0 | hzpos
  · subst z
    simp
  have hN1 : (1:ℝ)≤N := by exact_mod_cast hN
  have hN4 : (1:ℝ)≤(N:ℝ)^4 := one_le_pow₀ hN1
  have hD : (z+((m₁:ℝ)/N)^2)*(z+((m₂:ℝ)/N)^2)*(z+1) ≤
      (R+((m₁:ℝ)/N)^2)*(R+((m₂:ℝ)/N)^2)*(R+1) := by
    gcongr <;> exact hz.2
  have hDpos : 0 < (z+((m₁:ℝ)/N)^2)*(z+((m₂:ℝ)/N)^2)*(z+1) := by positivity
  have hf := div_le_div_of_nonneg_left (pow_nonneg hz.1 4) hDpos hD
  have hcoef : physicalDensityCompactConstant ((m₁:ℝ)/N) ((m₂:ℝ)/N) R*z^4 ≤
      2*Real.pi^2*(N:ℝ)^4*(z^4/((z+((m₁:ℝ)/N)^2)*(z+((m₂:ℝ)/N)^2)*(z+1))) := by
    calc
      _ = 2*Real.pi^2*(z^4/((R+((m₁:ℝ)/N)^2)*(R+((m₂:ℝ)/N)^2)*(R+1))) := by
        unfold physicalDensityCompactConstant
        ring
      _ ≤ 2*Real.pi^2*(z^4/((z+((m₁:ℝ)/N)^2)*(z+((m₂:ℝ)/N)^2)*(z+1))) :=
        mul_le_mul_of_nonneg_left hf (by positivity)
      _ ≤ _ := mul_le_mul_of_nonneg_right
        (le_mul_of_one_le_right (by positivity : 0 ≤ 2*Real.pi^2) hN4) (by positivity)
  exact (mul_le_mul_of_nonneg_right hcoef (Real.exp_pos _).le).trans
    (physicalScaledDensity_lower N m₁ m₂ hN hzpos)

end Zeta3.Analysis

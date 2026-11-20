import Zeta3.Analysis.CubicDensity
import Zeta5.Analysis.PhysicalWeight

/-! # A uniform exponential-polynomial bound for the actual cubic density -/

noncomputable section
namespace Zeta3.Analysis.PhysicalMeasure
open Real Set MeasureTheory Filter
open Zeta5.Analysis.PhysicalMeasure (bose boseTerm boseTerm_hasSum)
open scoped Topology

theorem expTerm_le_boseTerm {x : ℝ} (hx : 0 < x) (n : ℕ) :
    expTerm n x ≤ (2 / (Real.pi * x) ^ 2) * boseTerm n (x / 2) := by
  let u : ℝ := Real.pi * ((n + 1 : ℕ) : ℝ) * x
  have hu : 0 ≤ u := by dsimp [u]; positivity
  have h := Zeta5.Analysis.PhysicalMeasure.pow_mul_exp_neg_le_factorial hu 2
  norm_num only [Nat.factorial] at h
  have he : expTerm n x = ((u ^ 2 * Real.exp (-u)) / (Real.pi * x) ^ 2) *
      boseTerm n (x / 2) := by
    unfold expTerm boseTerm
    have harg : -(2 * Real.pi * ((n + 1 : ℕ) : ℝ) * (x / 2)) = -u := by dsimp [u]; ring
    rw [harg, div_mul_eq_mul_div, mul_assoc (u ^ 2), ← Real.exp_add]
    dsimp [u]
    have hexp : -(Real.pi * ((n + 1 : ℕ) : ℝ) * x) +
        -(Real.pi * ((n + 1 : ℕ) : ℝ) * x) = -(2 * Real.pi * ((n + 1 : ℕ) : ℝ) * x) := by ring
    rw [hexp]
    field_simp [Real.pi_ne_zero, hx.ne']
  rw [he]
  apply mul_le_mul_of_nonneg_right (div_le_div_of_nonneg_right h (by positivity))
  unfold boseTerm
  positivity

/-- A bound at the origin, obtained directly from the exponential series. -/
theorem density_uniform_bound {x : ℝ} (hx : 0 < x) :
    density x ≤ 8 / Real.pi := by
  have hs := (boseTerm_hasSum (div_pos hx (by norm_num : (0 : ℝ) < 2))).summable
  have hsum := Summable.tsum_le_tsum (fun n => expTerm_le_boseTerm hx n)
    (expTerm_summable hx) (hs.mul_left (2 / (Real.pi * x) ^ 2))
  rw [tsum_mul_left, (boseTerm_hasSum (div_pos hx (by norm_num : (0 : ℝ) < 2))).tsum_eq] at hsum
  have hbose : bose (x / 2) ≤ 1 / (Real.pi * x) := by
    unfold bose
    have harg : 2 * Real.pi * (x / 2) = Real.pi * x := by ring
    rw [harg]
    exact one_div_le_one_div_of_le (by positivity) (by linarith [Real.add_one_le_exp (Real.pi * x)])
  unfold density
  calc
    _ ≤ (2 * Real.pi) ^ 2 * x ^ 3 * ((2 / (Real.pi * x) ^ 2) * bose (x / 2)) :=
      mul_le_mul_of_nonneg_left hsum (by positivity)
    _ ≤ (2 * Real.pi) ^ 2 * x ^ 3 * ((2 / (Real.pi * x) ^ 2) * (1 / (Real.pi * x))) := by
      gcongr
    _ = _ := by field_simp [Real.pi_ne_zero, hx.ne']; ring

def densityTailConstant : ℝ :=
  (2 * Real.pi) ^ 2 * (Real.exp (2 * Real.pi) * ∑' n : ℕ, expTerm n 1)

theorem densityTailConstant_nonneg : 0 ≤ densityTailConstant := by
  unfold densityTailConstant
  exact mul_nonneg (by positivity) (mul_nonneg (Real.exp_nonneg _)
    (tsum_nonneg (fun n => (expTerm_pos n 1).le)))

theorem density_tail_bound {x : ℝ} (hx : 1 ≤ x) :
    density x ≤ densityTailConstant * x ^ 3 * Real.exp (-(2 * Real.pi * x)) := by
  have hxpos : 0 < x := lt_of_lt_of_le zero_lt_one hx
  have hterm (n : ℕ) : expTerm n x ≤
      (Real.exp (2 * Real.pi) * expTerm n 1) * Real.exp (-(2 * Real.pi * x)) := by
    unfold expTerm
    have harg : -(2 * Real.pi * ((n + 1 : ℕ) : ℝ) * x) ≤
        2 * Real.pi - (2 * Real.pi * ((n + 1 : ℕ) : ℝ) * 1) - 2 * Real.pi * x := by
      have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
      have ht : 0 ≤ (2 * Real.pi * (n : ℝ)) * (x - 1) := mul_nonneg (by positivity) (by linarith)
      push_cast
      nlinarith
    have h := mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr harg)
      (by positivity : 0 ≤ ((n + 1 : ℕ) : ℝ) ^ 2)
    simpa only [Real.exp_sub, Real.exp_add, Real.exp_neg, mul_one, div_eq_mul_inv,
      mul_assoc, mul_left_comm, mul_comm] using h
  have hs := Summable.tsum_le_tsum hterm (expTerm_summable hxpos)
    (((expTerm_summable (by norm_num : (0 : ℝ) < 1)).mul_left
      (Real.exp (2 * Real.pi))).mul_right (Real.exp (-(2 * Real.pi * x))))
  rw [tsum_mul_right, tsum_mul_left] at hs
  have h := mul_le_mul_of_nonneg_left hs
    (by positivity : 0 ≤ (2 * Real.pi) ^ 2 * x ^ 3)
  simpa only [density, densityTailConstant, mul_assoc, mul_left_comm, mul_comm] using h

/-- One constant works simultaneously near zero and on the infinite tail. -/
theorem exists_density_exponential_bound : ∃ C : ℝ, 0 < C ∧ ∀ x : ℝ, 0 < x →
    density x ≤ C * (1 + x ^ 3) * Real.exp (-(2 * Real.pi * x)) := by
  let C : ℝ := 8 / Real.pi * Real.exp (2 * Real.pi) + densityTailConstant + 1
  have hC : 0 < C := by dsimp [C]; positivity [densityTailConstant_nonneg]
  refine ⟨C, hC, ?_⟩
  intro x hx
  by_cases hx1 : 1 ≤ x
  · apply (density_tail_bound hx1).trans
    apply mul_le_mul_of_nonneg_right _ (Real.exp_nonneg _)
    have hconst : densityTailConstant ≤ C := by
      dsimp [C]
      have : 0 ≤ 8 / Real.pi * Real.exp (2 * Real.pi) := by positivity
      linarith
    nlinarith [pow_nonneg hx.le 3, densityTailConstant_nonneg]
  · have hbound := density_uniform_bound hx
    have hExp : 1 ≤ Real.exp (2 * Real.pi) * Real.exp (-(2 * Real.pi * x)) := by
      rw [← Real.exp_add]
      exact Real.one_le_exp (by nlinarith [Real.pi_pos])
    have hconst : 8 / Real.pi * Real.exp (2 * Real.pi) ≤ C := by
      dsimp [C]
      linarith [densityTailConstant_nonneg]
    calc
      density x ≤ 8 / Real.pi := hbound
      _ ≤ (8 / Real.pi * Real.exp (2 * Real.pi)) * Real.exp (-(2 * Real.pi * x)) := by
        have h := mul_le_mul_of_nonneg_left hExp (by positivity : 0 ≤ 8 / Real.pi)
        simpa only [mul_one, mul_assoc] using h
      _ ≤ C * (1 + x ^ 3) * Real.exp (-(2 * Real.pi * x)) := by
        apply mul_le_mul_of_nonneg_right _ (Real.exp_nonneg _)
        exact hconst.trans (by nlinarith [pow_nonneg hx.le 3])

end Zeta3.Analysis.PhysicalMeasure

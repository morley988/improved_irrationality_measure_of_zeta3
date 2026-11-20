import Zeta5.Analysis.GramBound
import Zeta3.Analysis.AnalyticError
import Mathlib.Analysis.Complex.Basic

/-!
# A sufficient determinant response majorant

Leibniz's formula and entrywise Cauchy--Schwarz give a factorial-loss bound.
The loss has zero quadratic logarithmic rate, so this replaces the manuscript's
stronger principal-minor/Andreief assertion without changing the exponent.
The hypotheses here are mathematical matrix bounds, never numerical evidence.
-/

noncomputable section
namespace Zeta3.Analysis
open Matrix
open scoped BigOperators

theorem norm_det_le_factorial_prod_of_entry_bound {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℂ) (d : ι → ℝ) (hd : ∀ i, 0 ≤ d i)
    (hA : ∀ i j, ‖A i j‖ ≤ d i * d j) :
    ‖A.det‖ ≤ (Nat.factorial (Fintype.card ι) : ℝ) * ∏ i, (d i) ^ 2 := by
  classical
  rw [Matrix.det_apply']
  calc
    _ ≤ ∑ σ : Equiv.Perm ι, ‖(Equiv.Perm.sign σ : ℂ) * ∏ i, A (σ i) i‖ :=
      norm_sum_le _ _
    _ = ∑ σ : Equiv.Perm ι, ∏ i, ‖A (σ i) i‖ := by
      apply Finset.sum_congr rfl
      intro σ _
      have hsign : ‖(Equiv.Perm.sign σ : ℂ)‖ = 1 := by
        rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with h | h <;> simp [h]
      rw [norm_mul, hsign, one_mul, norm_prod]
    _ ≤ ∑ _σ : Equiv.Perm ι, ∏ i, (d i) ^ 2 := by
      apply Finset.sum_le_sum
      intro σ _
      calc
        _ ≤ ∏ i, d (σ i) * d i :=
          Finset.prod_le_prod (fun i _ => norm_nonneg _) (fun i _ => hA (σ i) i)
        _ = ∏ i, (d i) ^ 2 := by
          rw [Finset.prod_mul_distrib, Equiv.prod_comp σ]
          simp only [pow_two, Finset.prod_mul_distrib]
    _ = _ := by simp [Fintype.card_perm]

theorem scaled_sqrt_mul_le {r x y : ℝ} (hr : 0 ≤ r) (hx : 0 ≤ x) (hy : 0 ≤ y) :
    r * (Real.sqrt x * Real.sqrt y) ≤
      Real.sqrt (1 + r * x) * Real.sqrt (1 + r * y) := by
  have hX : 0 ≤ 1 + r * x := by positivity
  have hY : 0 ≤ 1 + r * y := by positivity
  apply (sq_le_sq₀ (by positivity) (by positivity)).mp
  rw [mul_pow, mul_pow, mul_pow, Real.sq_sqrt hx, Real.sq_sqrt hy,
    Real.sq_sqrt hX, Real.sq_sqrt hY]
  nlinarith [mul_nonneg hr hx, mul_nonneg hr hy]

theorem identity_perturbation_entry_bound {ι : Type*} [Fintype ι] [DecidableEq ι]
    (T : Matrix ι ι ℂ) (eigenvalue : ι → ℝ) (hEigen : ∀ i, 0 ≤ eigenvalue i)
    (hT : ∀ i j, ‖T i j‖ ≤ Real.sqrt (eigenvalue i) * Real.sqrt (eigenvalue j))
    (h : ℂ) (i j : ι) :
    ‖(1 + h • T) i j‖ ≤
      Real.sqrt (1 + ‖h‖ * eigenvalue i) * Real.sqrt (1 + ‖h‖ * eigenvalue j) := by
  by_cases hij : i = j
  · subst j
    have hii : ‖T i i‖ ≤ eigenvalue i := by
      simpa only [Real.mul_self_sqrt (hEigen i)] using hT i i
    simp only [Matrix.add_apply, Matrix.one_apply_eq, Matrix.smul_apply, smul_eq_mul]
    calc
      ‖1 + h * T i i‖ ≤ ‖(1 : ℂ)‖ + ‖h * T i i‖ := norm_add_le _ _
      _ = 1 + ‖h‖ * ‖T i i‖ := by rw [norm_one, norm_mul]
      _ ≤ 1 + ‖h‖ * eigenvalue i := by
        linarith [mul_le_mul_of_nonneg_left hii (norm_nonneg h)]
      _ = _ := (Real.mul_self_sqrt (add_nonneg (by norm_num) (mul_nonneg (norm_nonneg h) (hEigen i)))).symm
  · simp only [Matrix.add_apply, Matrix.one_apply_ne hij, zero_add, Matrix.smul_apply,
      smul_eq_mul, norm_mul]
    exact (mul_le_mul_of_nonneg_left (hT i j) (norm_nonneg h)).trans
      (scaled_sqrt_mul_le (norm_nonneg h) (hEigen i) (hEigen j))

theorem determinant_response_majorant {ι : Type*} [Fintype ι] [DecidableEq ι]
    (T : Matrix ι ι ℂ) (eigenvalue : ι → ℝ) (hEigen : ∀ i, 0 ≤ eigenvalue i)
    (hT : ∀ i j, ‖T i j‖ ≤ Real.sqrt (eigenvalue i) * Real.sqrt (eigenvalue j)) (h : ℂ) :
    ‖(1 + h • T).det‖ ≤ (Nat.factorial (Fintype.card ι) : ℝ) *
      ∏ i, (1 + ‖h‖ * eigenvalue i) := by
  have hbound := norm_det_le_factorial_prod_of_entry_bound (1 + h • T)
    (fun i => Real.sqrt (1 + ‖h‖ * eigenvalue i)) (fun _ => Real.sqrt_nonneg _)
    (identity_perturbation_entry_bound T eigenvalue hEigen hT h)
  have hsqrt (i : ι) : Real.sqrt (1 + ‖h‖ * eigenvalue i) ^ 2 = 1 + ‖h‖ * eigenvalue i := by
    apply Real.sq_sqrt
    have hi := hEigen i
    positivity
  simpa only [hsqrt] using hbound

end Zeta3.Analysis

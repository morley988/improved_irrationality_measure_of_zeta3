import Zeta3.Analysis.PhysicalNormTrial
import Zeta3.Analysis.PhysicalProfile
import Zeta5.Reuse.FactorialRow

/-! # Exact asymmetric factorial normalization and each row's saving -/

noncomputable section
namespace Zeta3.Analysis
open Real Polynomial OddZeta.FourValue
open scoped BigOperators

def gramNormFactor (N m₁ m₂ k : ℕ) : ℝ :=
  (Nat.factorial N : ℝ) ^ 2 /
    ((Nat.factorial (2 * (m₁ + k)) : ℝ) * (Nat.factorial (2 * (m₂ + k)) : ℝ))

theorem gramNormFactor_pos (N m₁ m₂ k : ℕ) : 0 < gramNormFactor N m₁ m₂ k := by
  unfold gramNormFactor
  positivity

def rowNormUpper (K s₁ s₂ : ℝ) (h₁ : 0 < s₁) (h₂ : 0 < s₂) (N m₁ m₂ k : ℕ) : ℝ :=
  gramNormFactor N m₁ m₂ k *
    (K * physicalWeightScale N m₁ m₂ * (N : ℝ) ^ (4 * k + 20) *
      Real.exp ((N : ℝ) * physicalEquilibrium s₁ s₂ h₁ h₂ ((k : ℝ) / N)))

theorem rowNormUpper_pos {K s₁ s₂ : ℝ} (hK : 0 < K) (h₁ : 0 < s₁) (h₂ : 0 < s₂)
    {N : ℕ} (hN : 0 < N) (m₁ m₂ k : ℕ) : 0 < rowNormUpper K s₁ s₂ h₁ h₂ N m₁ m₂ k := by
  unfold rowNormUpper
  exact mul_pos (gramNormFactor_pos _ _ _ _)
    (mul_pos (mul_pos (mul_pos hK (physicalWeightScale_pos hN _ _)) (by positivity)) (Real.exp_pos _))

theorem rowNormUpper_cancel {K s₁ s₂ : ℝ} (h₁ : 0 < s₁) (h₂ : 0 < s₂)
    (N m₁ m₂ k : ℕ) :
    rowNormUpper K s₁ s₂ h₁ h₂ N m₁ m₂ k =
      K * ((Nat.factorial N : ℝ) ^ 2 /
        ((Nat.factorial (2 * (m₁ + k)) : ℝ) * (Nat.factorial (2 * (m₂ + k)) : ℝ))) *
        ((N : ℝ) ^ (2 * (m₁ + m₂) + 4 * k + 20) / (N : ℝ) ^ (2 * N)) *
        Real.exp ((N : ℝ) * physicalEquilibrium s₁ s₂ h₁ h₂ ((k : ℝ) / N)) := by
  unfold rowNormUpper gramNormFactor physicalWeightScale
  rw [show 2 * (m₁ + m₂) + 4 * k + 20 = 2 * (m₁ + m₂) + (4 * k + 20) by omega, pow_add]
  ring

theorem log_rowNormUpper {K s₁ s₂ : ℝ} (hK : 0 < K) (h₁ : 0 < s₁) (h₂ : 0 < s₂)
    {N : ℕ} (hN : 0 < N) (m₁ m₂ k : ℕ) :
    Real.log (rowNormUpper K s₁ s₂ h₁ h₂ N m₁ m₂ k) =
      Real.log K + 2 * Real.log (Nat.factorial N : ℝ) -
        Real.log (Nat.factorial (2 * (m₁ + k)) : ℝ) -
        Real.log (Nat.factorial (2 * (m₂ + k)) : ℝ) +
        (2 * ((m₁ : ℝ) + m₂) + 4 * (k : ℝ) + 20 - 2 * (N : ℝ)) * Real.log (N : ℝ) +
        (N : ℝ) * physicalEquilibrium s₁ s₂ h₁ h₂ ((k : ℝ) / N) := by
  rw [rowNormUpper_cancel h₁ h₂]
  rw [Real.log_mul (by positivity) (Real.exp_ne_zero _), Real.log_exp,
    Real.log_mul (by positivity) (by positivity), Real.log_mul hK.ne' (by positivity),
    Real.log_div (by positivity) (by positivity),
    Real.log_mul (by positivity) (by positivity),
    Real.log_div (by positivity) (by positivity)]
  simp only [Real.log_pow]
  push_cast
  ring

theorem log_rowNormUpper_le_profile {K s₁ s₂ : ℝ} (hK : 0 < K)
    (h₁ : 0 < s₁) (h₂ : 0 < s₂) {N m₁ m₂ : ℕ} (hN : 0 < N)
    (hms₁ : (m₁ : ℝ) / N = s₁) (hms₂ : (m₂ : ℝ) / N = s₂) (k : ℕ) :
    Real.log (rowNormUpper K s₁ s₂ h₁ h₂ N m₁ m₂ k) ≤
      -(N : ℝ) * physicalSaving s₁ s₂ h₁ h₂ ((k : ℝ) / N) +
        (Real.log K + 20 * Real.log (N : ℝ) + Real.log ((N : ℝ) + 1) + 2) := by
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have hfac := (abs_le.mp (log_factorial_main_error N)).2
  have hrow₁ := factorial_row_main_upper (m₁ + k) (N : ℝ) hNr
  have hrow₂ := factorial_row_main_upper (m₂ + k) (N : ℝ) hNr
  have hnorm : (N : ℝ) * physicalEquilibrium s₁ s₂ h₁ h₂ ((k : ℝ) / N) - 2 * (N : ℝ) +
      (N : ℝ) * (factorialRowRate (((m₁ + k : ℕ) : ℝ) / N) +
        factorialRowRate (((m₂ + k : ℕ) : ℝ) / N)) / 2 =
      -(N : ℝ) * physicalSaving s₁ s₂ h₁ h₂ ((k : ℝ) / N) := by
    simp only [Nat.cast_add, add_div, hms₁, hms₂, physicalSaving, factorialRowRate]
    ring
  rw [log_rowNormUpper hK h₁ h₂ hN]
  push_cast at hrow₁ hrow₂ hnorm
  linarith

end Zeta3.Analysis

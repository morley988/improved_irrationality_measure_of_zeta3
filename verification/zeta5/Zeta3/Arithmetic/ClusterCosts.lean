import Zeta5.Arithmetic.ClusterCosts
import Mathlib.Tactic.Linarith

/-! Cubic reflected-cluster costs. A common factor in either unequal
window supplies one unit of gain. The two-window gain is used only above
N/2, where there are at most two high nodes in a class. -/
namespace Zeta3.Arithmetic

def clusterCost (h l : ℕ) : ℤ :=
  3 * (min l h : ℕ) + (l : ℤ) * ((h : ℤ) + 2 - l)

def gainedClusterCost (h gain l : ℕ) : ℤ :=
  3 * (min l h : ℕ) + (l : ℤ) * ((h : ℤ) + 2 - gain - l)

theorem clusterCost_le_with_deficit (h l : ℕ)
    (hh : 1 ≤ h) (hh4 : h ≤ 4) (hl : l ≤ h + 2) :
    clusterCost h l ≤ 5 * (h : ℤ) - (h - l : ℕ) := by
  interval_cases h <;> interval_cases l <;> norm_num [clusterCost] at *

theorem clusterCost_le_with_deficit_all (h l : ℕ) (hh : 1 ≤ h) (hh4 : h ≤ 4) :
    clusterCost h l ≤ 5 * (h : ℤ) - (h - l : ℕ) := by
  by_cases hl : l ≤ h + 2
  · exact clusterCost_le_with_deficit h l hh hh4 hl
  have hhl : h ≤ l := by omega
  rw [clusterCost, min_eq_right hhl, Nat.sub_eq_zero_of_le hhl, Nat.cast_zero, sub_zero]
  have hprod : (l : ℤ) * ((h : ℤ) + 2 - l) ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos (Int.natCast_nonneg _) (by omega)
  omega

theorem gainedClusterCost_le_with_deficit (h gain l : ℕ)
    (hh : 1 ≤ h) (hh2 : h ≤ 2) (ha : gain ≤ 2) (hl : l ≤ h + 2) :
    gainedClusterCost h gain l ≤ (5 - (gain : ℤ)) * h - (h - l : ℕ) := by
  interval_cases gain <;> interval_cases h <;> interval_cases l <;>
    norm_num [gainedClusterCost] at *

theorem gainedClusterCost_le_with_deficit_all (h gain l : ℕ)
    (hh : 1 ≤ h) (hh2 : h ≤ 2) (ha : gain ≤ 2) :
    gainedClusterCost h gain l ≤ (5 - (gain : ℤ)) * h - (h - l : ℕ) := by
  by_cases hl : l ≤ h + 2
  · exact gainedClusterCost_le_with_deficit h gain l hh hh2 ha hl
  have hhl : h ≤ l := by omega
  rw [gainedClusterCost, min_eq_right hhl, Nat.sub_eq_zero_of_le hhl,
    Nat.cast_zero, sub_zero]
  have hprod : (l : ℤ) * ((h : ℤ) + 2 - gain - l) ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos (Int.natCast_nonneg _) (by omega)
  have hgain : (gain : ℤ) ≤ 2 := by exact_mod_cast ha
  nlinarith

theorem clusterCost_at_all_high (h : ℕ) : clusterCost h h = 5 * (h : ℤ) := by
  simp only [clusterCost, min_self]
  ring

theorem gainedClusterCost_at_all_high (h gain : ℕ) :
    gainedClusterCost h gain h = (5 - (gain : ℤ)) * h := by
  simp only [gainedClusterCost, min_self]
  ring

end Zeta3.Arithmetic

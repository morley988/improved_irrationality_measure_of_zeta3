import Zeta5.Endpoint.ZetaBridge
import Zeta3.Construction.Functional
import Mathlib.Analysis.PSeries

/-! # The ordinary zeta tail at positive integers -/

noncomputable section
namespace Zeta3.Analysis.PhysicalMeasure
open Polynomial Real
open scoped BigOperators

def hurwitzThree (y : ℝ) : ℝ := ∑' n : ℕ, 1 / ((n : ℝ) + y) ^ 3

theorem hurwitzThree_summable {y : ℝ} (hy : 0 < y) :
    Summable (fun n : ℕ => 1 / ((n : ℝ) + y) ^ 3) := by
  have h := (Real.summable_one_div_nat_add_rpow y 3).mpr (by norm_num)
  apply h.congr
  intro n
  rw [abs_of_pos (by positivity : 0 < (n : ℝ) + y)]
  norm_cast

theorem hurwitzThree_shift {y : ℝ} (hy : 0 < y) :
    hurwitzThree y = 1 / y ^ 3 + ∑' n : ℕ, 1 / (((n + 1 : ℕ) : ℝ) + y) ^ 3 := by
  simpa only [hurwitzThree, Nat.cast_zero, zero_add] using (hurwitzThree_summable hy).tsum_eq_zero_add

theorem harmonicThree_real_range (m : ℕ) :
    (∑ k ∈ Finset.range (m + 1), 1 / (k : ℝ) ^ 3) =
      (Zeta3.Construction.harmonicThree m : ℝ) := by
  rw [Finset.sum_range_succ']
  simp only [Nat.cast_zero, zero_pow (by decide : 3 ≠ 0), div_zero, add_zero,
    Zeta3.Construction.harmonicThree, Rat.cast_sum, Rat.cast_div, Rat.cast_one, Rat.cast_pow,
    Rat.cast_natCast]

theorem hurwitzThree_nat {i : ℕ} (hi : 0 < i) :
    hurwitzThree (i : ℝ) = Zeta5.Endpoint.realZeta 3 -
      (Zeta3.Construction.harmonicThree (i - 1) : ℝ) := by
  have hs : Summable (fun n : ℕ => 1 / (n : ℝ) ^ 3) :=
    summable_one_div_nat_pow.mpr (by norm_num)
  have ht := hs.sum_add_tsum_nat_add i
  have hm : (∑ k ∈ Finset.range i, 1 / (k : ℝ) ^ 3) =
      (Zeta3.Construction.harmonicThree (i - 1) : ℝ) := by
    simpa only [Nat.sub_add_cancel (show 1 ≤ i by omega)] using harmonicThree_real_range (i - 1)
  rw [hm] at ht
  simp only [Nat.cast_add] at ht
  change _ + hurwitzThree (i : ℝ) = Zeta5.Endpoint.realZeta 3 at ht
  linarith

end Zeta3.Analysis.PhysicalMeasure

import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

/-!
# Finite monotone sums bound actual integrals

No smoothness or numerical oracle is needed: monotonicity on the compact
interval already proves integrability. These lemmas separate finite sampled
inequalities (the hybrid numerical interface) from their analytic use.
-/

open MeasureTheory Set Finset
open scoped BigOperators

namespace Zeta3.Analysis
noncomputable section

theorem left_sum_le_integral_of_monotoneOn (f : ℝ → ℝ) {h : ℝ} (hh : 0 ≤ h)
    (n : ℕ) (hm : MonotoneOn f (Icc 0 (h * (n : ℝ)))) :
    h * (∑ i ∈ range n, f (h * (i : ℝ))) ≤ ∫ t in 0..h * (n : ℝ), f t := by
  have hstep (i : ℕ) : h * (i : ℝ) ≤ h * ((i + 1 : ℕ) : ℝ) := by
    apply mul_le_mul_of_nonneg_left _ hh
    exact_mod_cast Nat.le_succ i
  have hsub (i : ℕ) (hi : i < n) :
      Icc (h * (i : ℝ)) (h * ((i + 1 : ℕ) : ℝ)) ⊆ Icc 0 (h * (n : ℝ)) := by
    apply Set.Icc_subset_Icc
    · positivity
    · apply mul_le_mul_of_nonneg_left _ hh
      exact_mod_cast hi
  have hint (i : ℕ) (hi : i < n) :
      IntervalIntegrable f volume (h * (i : ℝ)) (h * ((i + 1 : ℕ) : ℝ)) := by
    apply MonotoneOn.intervalIntegrable
    rw [uIcc_of_le (hstep i)]
    exact hm.mono (hsub i hi)
  have hlocal (i : ℕ) (hi : i < n) :
      h * f (h * (i : ℝ)) ≤ ∫ t in h * (i : ℝ)..h * ((i + 1 : ℕ) : ℝ), f t := by
    have hf := intervalIntegral.integral_mono_on (hstep i) intervalIntegrable_const (hint i hi)
      (fun t ht => hm (hsub i hi ⟨le_rfl, hstep i⟩) (hsub i hi ht) ht.1)
    have hlen : h * ((i + 1 : ℕ) : ℝ) - h * (i : ℝ) = h := by push_cast; ring
    simpa only [intervalIntegral.integral_const, smul_eq_mul, hlen] using hf
  have hs := Finset.sum_le_sum (fun i hi => hlocal i (mem_range.mp hi))
  rw [← Finset.mul_sum,
    intervalIntegral.sum_integral_adjacent_intervals (a := fun i : ℕ => h * (i : ℝ)) hint] at hs
  simpa only [Nat.cast_zero, mul_zero] using hs

theorem integral_le_left_sum_of_antitoneOn (f : ℝ → ℝ) {h : ℝ} (hh : 0 ≤ h)
    (n : ℕ) (hm : AntitoneOn f (Icc 0 (h * (n : ℝ)))) :
    (∫ t in 0..h * (n : ℝ), f t) ≤ h * (∑ i ∈ range n, f (h * (i : ℝ))) := by
  have hn : MonotoneOn (fun t => -f t) (Icc 0 (h * (n : ℝ))) := by
    intro a ha b hb hab
    exact neg_le_neg (hm ha hb hab)
  have hs := left_sum_le_integral_of_monotoneOn (fun t => -f t) hh n hn
  simpa only [Finset.sum_neg_distrib, mul_neg, intervalIntegral.integral_neg, neg_le_neg_iff] using hs

theorem lower_samples_le_integral (f samples : ℝ → ℝ) {h : ℝ} (hh : 0 ≤ h)
    (n : ℕ) (hm : MonotoneOn f (Icc 0 (h * (n : ℝ))))
    (hs : ∀ i < n, samples (h * (i : ℝ)) ≤ f (h * (i : ℝ))) :
    h * (∑ i ∈ range n, samples (h * (i : ℝ))) ≤ ∫ t in 0..h * (n : ℝ), f t := by
  exact (mul_le_mul_of_nonneg_left
    (Finset.sum_le_sum (fun i hi => hs i (mem_range.mp hi))) hh).trans
      (left_sum_le_integral_of_monotoneOn f hh n hm)

theorem integral_le_upper_samples (f samples : ℝ → ℝ) {h : ℝ} (hh : 0 ≤ h)
    (n : ℕ) (hm : AntitoneOn f (Icc 0 (h * (n : ℝ))))
    (hs : ∀ i < n, f (h * (i : ℝ)) ≤ samples (h * (i : ℝ))) :
    (∫ t in 0..h * (n : ℝ), f t) ≤ h * (∑ i ∈ range n, samples (h * (i : ℝ))) := by
  exact (integral_le_left_sum_of_antitoneOn f hh n hm).trans
    (mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun i hi => hs i (mem_range.mp hi))) hh)

end
end Zeta3.Analysis

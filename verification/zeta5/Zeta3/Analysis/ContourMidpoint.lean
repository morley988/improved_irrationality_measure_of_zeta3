import Zeta3.Analysis.FiniteGrid
import Mathlib.Analysis.Convex.Function

/-!
# Convex midpoint quadrature on an exact finite partition

The lower quadrature bound is proved by reflection and the defining convex
inequality.  Every panel is handled uniformly; no sampled second derivative
or external convexity premise is used.
-/

noncomputable section
open Set MeasureTheory Finset
open scoped BigOperators
namespace Zeta3.Analysis

theorem midpoint_mul_length_le_integral {f : ℝ → ℝ} {a b : ℝ}
    (hab : a ≤ b) (hf : ContinuousOn f (Icc a b)) (hc : ConvexOn ℝ (Icc a b) f) :
    (b-a)*f ((a+b)/2) ≤ ∫ x in a..b, f x := by
  have hi : IntervalIntegrable f volume a b := hf.intervalIntegrable_of_Icc hab
  have hr : IntervalIntegrable (fun x => f (a+b-x)) volume a b := by
    convert! (hi.comp_sub_left (a+b)).symm using 1 <;> ring
  have hpt (x : ℝ) (hx : x ∈ Icc a b) :
      2*f ((a+b)/2) ≤ f x+f (a+b-x) := by
    have hy : a+b-x ∈ Icc a b := ⟨by linarith [hx.2], by linarith [hx.1]⟩
    have h := hc.2 hx hy (show (0:ℝ) ≤ 1/2 by norm_num)
      (show (0:ℝ) ≤ 1/2 by norm_num) (by norm_num)
    simp only [smul_eq_mul] at h
    have he : (1:ℝ)/2*x+(1/2)*(a+b-x)=(a+b)/2 := by ring
    rw [he] at h
    linarith
  have hm := intervalIntegral.integral_mono_on hab intervalIntegrable_const (hi.add hr) hpt
  rw [intervalIntegral.integral_const, intervalIntegral.integral_add hi hr,
    intervalIntegral.integral_comp_sub_left] at hm
  simp only [smul_eq_mul] at hm
  have he1 : a+b-b=a := by ring
  have he2 : a+b-a=b := by ring
  rw [he1,he2] at hm
  linarith

theorem midpoint_sum_le_integral {f : ℝ → ℝ} (a h : ℝ) (hh : 0 ≤ h) (n : ℕ)
    (hf : ContinuousOn f (Icc a (a+h*(n:ℝ))))
    (hc : ConvexOn ℝ (Icc a (a+h*(n:ℝ))) f) :
    h*(∑ i ∈ range n, f (a+h*((i:ℝ)+1/2))) ≤ ∫ x in a..a+h*(n:ℝ), f x := by
  have hstep (i : ℕ) : a+h*(i:ℝ) ≤ a+h*((i+1:ℕ):ℝ) := by
    have hi : (i:ℝ) ≤ ((i+1:ℕ):ℝ) := by exact_mod_cast Nat.le_succ i
    exact add_le_add (le_refl a) (mul_le_mul_of_nonneg_left hi hh)
  have hsub (i : ℕ) (hi : i<n) :
      Icc (a+h*(i:ℝ)) (a+h*((i+1:ℕ):ℝ)) ⊆ Icc a (a+h*(n:ℝ)) := by
    apply Set.Icc_subset_Icc
    · have hp : 0 ≤ h*(i:ℝ) := by positivity
      linarith
    · apply add_le_add (le_refl a)
      apply mul_le_mul_of_nonneg_left _ hh
      exact_mod_cast hi
  have hint (i : ℕ) (hi : i<n) :
      IntervalIntegrable f volume (a+h*(i:ℝ)) (a+h*((i+1:ℕ):ℝ)) :=
    (hf.mono (hsub i hi)).intervalIntegrable_of_Icc (hstep i)
  have hlocal (i : ℕ) (hi : i<n) :
      h*f (a+h*((i:ℝ)+1/2)) ≤ ∫ x in a+h*(i:ℝ)..a+h*((i+1:ℕ):ℝ), f x := by
    have hmid := midpoint_mul_length_le_integral (hstep i) (hf.mono (hsub i hi))
      (hc.subset (hsub i hi) (convex_Icc _ _))
    have hlen : (a+h*((i+1:ℕ):ℝ))-(a+h*(i:ℝ))=h := by push_cast; ring
    have hnode : ((a+h*(i:ℝ))+(a+h*((i+1:ℕ):ℝ)))/2=a+h*((i:ℝ)+1/2) := by
      push_cast
      ring
    simpa only [hlen,hnode] using hmid
  have hs := Finset.sum_le_sum (fun i hi => hlocal i (mem_range.mp hi))
  rw [← Finset.mul_sum,
    intervalIntegral.sum_integral_adjacent_intervals (a := fun i:ℕ => a+h*(i:ℝ)) hint] at hs
  simpa only [Nat.cast_zero,mul_zero,add_zero] using hs

end Zeta3.Analysis

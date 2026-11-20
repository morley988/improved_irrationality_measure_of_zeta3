import Zeta3.Analysis.ContourRational

/-!
# Uniform finite Riemann bounds for the contour density

The circle logarithm is the sum of a decreasing radial logarithm and an
increasing angular correction.  This gives exact endpoint errors, uniform
in the angle, rather than an external asymptotic Riemann-sum premise.
-/

noncomputable section
open Set MeasureTheory
open scoped BigOperators
namespace Zeta3.Analysis

theorem integral_le_right_sum_of_monotoneOn (f : ℝ → ℝ) {h : ℝ} (hh : 0 ≤ h)
    (n : ℕ) (hm : MonotoneOn f (Icc 0 (h*(n:ℝ)))) :
    (∫ x in 0..h*(n:ℝ), f x) ≤ h*(∑ i ∈ Finset.range n, f (h*((i+1:ℕ):ℝ))) := by
  have hstep (i : ℕ) : h*(i:ℝ) ≤ h*((i+1:ℕ):ℝ) := by
    apply mul_le_mul_of_nonneg_left _ hh
    exact_mod_cast Nat.le_succ i
  have hsub (i : ℕ) (hi : i<n) :
      Icc (h*(i:ℝ)) (h*((i+1:ℕ):ℝ)) ⊆ Icc 0 (h*(n:ℝ)) := by
    apply Set.Icc_subset_Icc
    · positivity
    · apply mul_le_mul_of_nonneg_left _ hh
      exact_mod_cast hi
  have hint (i : ℕ) (hi : i<n) :
      IntervalIntegrable f volume (h*(i:ℝ)) (h*((i+1:ℕ):ℝ)) := by
    apply MonotoneOn.intervalIntegrable
    rw [uIcc_of_le (hstep i)]
    exact hm.mono (hsub i hi)
  have hlocal (i : ℕ) (hi : i<n) :
      (∫ x in h*(i:ℝ)..h*((i+1:ℕ):ℝ), f x) ≤ h*f (h*((i+1:ℕ):ℝ)) := by
    have hs := intervalIntegral.integral_mono_on (hstep i) (hint i hi) intervalIntegrable_const
      (fun x hx => hm (hsub i hi hx) (hsub i hi ⟨hstep i,le_rfl⟩) hx.2)
    have hlen : h*((i+1:ℕ):ℝ)-h*(i:ℝ)=h := by push_cast; ring
    simpa only [intervalIntegral.integral_const,smul_eq_mul,hlen] using hs
  have hs := Finset.sum_le_sum (fun i hi => hlocal i (Finset.mem_range.mp hi))
  rw [← Finset.mul_sum,
    intervalIntegral.sum_integral_adjacent_intervals (a := fun i:ℕ => h*(i:ℝ)) hint] at hs
  simpa only [Nat.cast_zero,mul_zero] using hs

theorem right_sum_le_integral_of_antitoneOn (f : ℝ → ℝ) {h : ℝ} (hh : 0 ≤ h)
    (n : ℕ) (hm : AntitoneOn f (Icc 0 (h*(n:ℝ)))) :
    h*(∑ i ∈ Finset.range n, f (h*((i+1:ℕ):ℝ))) ≤ ∫ x in 0..h*(n:ℝ), f x := by
  have hn : MonotoneOn (fun x => -f x) (Icc 0 (h*(n:ℝ))) :=
    fun a ha b hb hab => neg_le_neg (hm ha hb hab)
  have hs := integral_le_right_sum_of_monotoneOn (fun x => -f x) hh n hn
  simpa only [Finset.sum_neg_distrib,mul_neg,intervalIntegral.integral_neg,neg_le_neg_iff] using hs

private theorem contour_sum_shift (f : ℕ → ℝ) (m : ℕ) :
    (∑ i ∈ Finset.range m, f (i+1))=(∑ i ∈ Finset.range m, f i)+f m-f 0 := by
  have hs := Finset.sum_range_sub f m
  rw [Finset.sum_sub_distrib] at hs
  linarith

/-- A decreasing term plus an increasing term has a one-sided endpoint error. -/
theorem left_sum_add_le_integral {g k : ℝ → ℝ} {h : ℝ} (hh : 0 ≤ h) (n : ℕ)
    (hg : AntitoneOn g (Icc 0 (h*(n:ℝ)))) (hk : MonotoneOn k (Icc 0 (h*(n:ℝ)))) :
    h*(∑ i ∈ Finset.range n, (g (h*(i:ℝ))+k (h*(i:ℝ)))) ≤
      (∫ x in 0..h*(n:ℝ), g x+k x)+h*(g 0-g (h*(n:ℝ))) := by
  have hgr := right_sum_le_integral_of_antitoneOn g hh n hg
  have hkl := left_sum_le_integral_of_monotoneOn k hh n hk
  have hshift := contour_sum_shift (fun i => g (h*(i:ℝ))) n
  simp only [Nat.cast_zero,mul_zero] at hshift
  have hgn : IntervalIntegrable g volume 0 (h*(n:ℝ)) := by
    apply AntitoneOn.intervalIntegrable
    rw [uIcc_of_le (by positivity : 0 ≤ h*(n:ℝ))]
    exact hg
  have hkn : IntervalIntegrable k volume 0 (h*(n:ℝ)) := by
    apply MonotoneOn.intervalIntegrable
    rw [uIcc_of_le (by positivity : 0 ≤ h*(n:ℝ))]
    exact hk
  rw [intervalIntegral.integral_add hgn hkn,Finset.sum_add_distrib]
  rw [hshift] at hgr
  linarith

theorem integral_le_right_sum_add {g k : ℝ → ℝ} {h : ℝ} (hh : 0 ≤ h) (n : ℕ)
    (hg : AntitoneOn g (Icc 0 (h*(n:ℝ)))) (hk : MonotoneOn k (Icc 0 (h*(n:ℝ)))) :
    (∫ x in 0..h*(n:ℝ), g x+k x)+h*(g (h*(n:ℝ))-g 0) ≤
      h*(∑ i ∈ Finset.range n, (g (h*((i+1:ℕ):ℝ))+k (h*((i+1:ℕ):ℝ)))) := by
  have hgl := integral_le_left_sum_of_antitoneOn g hh n hg
  have hkr := integral_le_right_sum_of_monotoneOn k hh n hk
  have hshift := contour_sum_shift (fun i => g (h*(i:ℝ))) n
  simp only [Nat.cast_zero,mul_zero] at hshift
  have hgn : IntervalIntegrable g volume 0 (h*(n:ℝ)) := by
    apply AntitoneOn.intervalIntegrable
    rw [uIcc_of_le (by positivity : 0 ≤ h*(n:ℝ))]
    exact hg
  have hkn : IntervalIntegrable k volume 0 (h*(n:ℝ)) := by
    apply MonotoneOn.intervalIntegrable
    rw [uIcc_of_le (by positivity : 0 ≤ h*(n:ℝ))]
    exact hk
  rw [intervalIntegral.integral_add hgn hkn,Finset.sum_add_distrib,hshift]
  linarith

theorem contour_radialLog_antitoneOn {u : ℝ} (hu : 1 < u) :
    AntitoneOn (fun x:ℝ => Real.log (u^2-x^2)) (Icc 0 1) := by
  intro x hx y hy hxy
  apply Real.log_le_log (contour_gap_pos hu hy)
  nlinarith [mul_nonneg (sub_nonneg.mpr hxy) (add_nonneg hx.1 hy.1)]

theorem contour_log_decomposition {u x : ℝ} {z : ℂ} (hu : 1 < u)
    (hz : Complex.normSq z=u^4) (hx : x ∈ Icc 0 1) :
    Real.log ‖z+(x^2:ℝ)‖ = Real.log (u^2-x^2)+
      (1/2)*scaledRationalAngularKernel u (contourAngularCoordinate u z) x := by
  have h := contour_log_difference hu hz hx
  rw [contour_negative_log hu hx] at h
  linarith

theorem contour_logarithmic_grid_bounds {u : ℝ} {z : ℂ} (hu : 1 < u)
    (hz : Complex.normSq z=u^4) (N m : ℕ) (hN : 0 < N) (hm : m ≤ N) :
    (∑ i ∈ Finset.range m, Real.log ‖z+(((i:ℝ)/N)^2:ℝ)‖) ≤
      (N:ℝ)*rationalContourIntegral ((m:ℝ)/N) z+Real.log (u^2)-Real.log (u^2-((m:ℝ)/N)^2) ∧
    (N:ℝ)*rationalContourIntegral ((m:ℝ)/N) z+Real.log (u^2-((m:ℝ)/N)^2)-Real.log (u^2) ≤
      (∑ i ∈ Finset.range m, Real.log ‖z+((((i+1:ℕ):ℝ)/N)^2:ℝ)‖) := by
  have hNr : (0:ℝ)<N := by exact_mod_cast hN
  have hmr : (m:ℝ)≤N := by exact_mod_cast hm
  have hs : (m:ℝ)/N ∈ Icc (0:ℝ) 1 := ⟨by positivity,(div_le_one hNr).2 hmr⟩
  have he : (1/(N:ℝ))*(m:ℝ)=(m:ℝ)/N := by ring
  let g := fun x:ℝ => Real.log (u^2-x^2)
  let k := fun x:ℝ => (1/2)*scaledRationalAngularKernel u (contourAngularCoordinate u z) x
  have hsub : Icc (0:ℝ) ((1/(N:ℝ))*(m:ℝ)) ⊆ Icc (0:ℝ) 1 := by
    rw [he]
    exact Set.Icc_subset_Icc (le_refl _) hs.2
  have hg : AntitoneOn g (Icc (0:ℝ) ((1/(N:ℝ))*(m:ℝ))) :=
    (contour_radialLog_antitoneOn hu).mono hsub
  have hy := contourAngularCoordinate_mem (by linarith : 0<u) hz
  have hk : MonotoneOn k (Icc (0:ℝ) ((1/(N:ℝ))*(m:ℝ))) := by
    intro a ha b hb hab
    exact mul_le_mul_of_nonneg_left
      (scaledRationalAngularKernel_monotoneOn hu hy.1 (hsub ha) (hsub hb) hab) (by norm_num)
  have hl := left_sum_add_le_integral (by positivity : 0 ≤ 1/(N:ℝ)) m hg hk
  have hr := integral_le_right_sum_add (by positivity : 0 ≤ 1/(N:ℝ)) m hg hk
  have hint : (∫ x in 0..(1/(N:ℝ))*(m:ℝ),g x+k x)=rationalContourIntegral ((m:ℝ)/N) z := by
    rw [he]
    unfold rationalContourIntegral
    apply intervalIntegral.integral_congr
    intro x hx
    exact (contour_log_decomposition hu hz
      ((Set.Icc_subset_Icc (le_refl _) hs.2) (by simpa only [uIcc_of_le hs.1] using hx))).symm
  have hnode (i:ℕ) (hi:i≤m) : ((i:ℝ)/N) ∈ Icc (0:ℝ) 1 := by
    refine ⟨by positivity,(div_le_one hNr).2 ?_⟩
    exact_mod_cast hi.trans hm
  have hleft : (∑ i ∈ Finset.range m,(g ((1/(N:ℝ))*(i:ℝ))+k ((1/(N:ℝ))*(i:ℝ))))=
      ∑ i ∈ Finset.range m,Real.log ‖z+(((i:ℝ)/N)^2:ℝ)‖ := by
    apply Finset.sum_congr rfl
    intro i hi
    rw [show (1/(N:ℝ))*(i:ℝ)=(i:ℝ)/N by ring]
    exact (contour_log_decomposition hu hz (hnode i (Finset.mem_range.mp hi).le)).symm
  have hright : (∑ i ∈ Finset.range m,(g ((1/(N:ℝ))*((i+1:ℕ):ℝ))+k ((1/(N:ℝ))*((i+1:ℕ):ℝ))))=
      ∑ i ∈ Finset.range m,Real.log ‖z+((((i+1:ℕ):ℝ)/N)^2:ℝ)‖ := by
    apply Finset.sum_congr rfl
    intro i hi
    rw [show (1/(N:ℝ))*((i+1:ℕ):ℝ)=((i+1:ℕ):ℝ)/N by ring]
    exact (contour_log_decomposition hu hz (hnode (i+1) (Finset.mem_range.mp hi))).symm
  rw [hint,hleft,he] at hl
  rw [hint,hright,he] at hr
  dsimp [g] at hl hr
  norm_num only [zero_pow (by decide : 2≠0),sub_zero] at hl hr
  constructor
  · have h := mul_le_mul_of_nonneg_left hl hNr.le
    have hcancel : (N:ℝ)*(1/(N:ℝ))=1 := by field_simp
    simpa only [mul_add,← mul_assoc,hcancel,one_mul,add_sub_assoc] using h
  · have h := mul_le_mul_of_nonneg_left hr hNr.le
    have hcancel : (N:ℝ)*(1/(N:ℝ))=1 := by field_simp
    simpa only [mul_add,← mul_assoc,hcancel,one_mul,add_sub_assoc] using h

end Zeta3.Analysis

import Zeta3.Analysis.ContourRationalKernel
import Zeta3.Analysis.ContourMidpoint
import Zeta3.Analysis.AngularMass

/-!
# The exact 128-charge rational deficit

The logarithmic kernel is scaled to the actual contour radius.  Monotonicity
combines the two short numerator windows, and convex midpoint quadrature
produces precisely the 128 rational poles used by the Arb certificate.
-/

noncomputable section
open Set MeasureTheory
open scoped BigOperators
namespace Zeta3.Analysis

def scaledRationalAngularKernel (u y x : ℝ) : ℝ := rationalAngularKernel y (x/u)

private theorem scaledRational_mem {u x : ℝ} (hu : 1 < u) (hx : x ∈ Icc 0 1) :
    x/u ∈ Icc 0 (1/u) := by
  have hu0 : 0 < u := by linarith
  exact ⟨div_nonneg hx.1 hu0.le, div_le_div_of_nonneg_right hx.2 hu0.le⟩

private theorem scaledRational_right_lt_one {u : ℝ} (hu : 1 < u) : 1/u < 1 := by
  have hu0 : 0 < u := by linarith
  exact (div_lt_one hu0).2 hu

theorem scaledRationalAngularKernel_formula {u y x : ℝ} (hu : 1 < u)
    (hy : 0 ≤ y) (hx : x ∈ Icc 0 1) :
    scaledRationalAngularKernel u y x = Real.log (1+2*u^2*x^2*y/(u^2-x^2)^2) := by
  have hu0 : 0 < u := by linarith
  have hm := scaledRational_mem hu hx
  rw [scaledRationalAngularKernel, rationalAngularKernel_formula hy hm.1
    (hm.2.trans_lt (scaledRational_right_lt_one hu))]
  congr 1
  field_simp
  <;> ring

theorem scaledRationalAngularKernel_continuousOn {u y : ℝ} (hu : 1 < u) (hy : 0 ≤ y) :
    ContinuousOn (scaledRationalAngularKernel u y) (Icc 0 1) := by
  exact (rationalAngularKernel_continuousOn hy (scaledRational_right_lt_one hu)).comp
    (continuous_id.div_const u).continuousOn (fun _ hx => scaledRational_mem hu hx)

theorem scaledRationalAngularKernel_monotoneOn {u y : ℝ} (hu : 1 < u) (hy : 0 ≤ y) :
    MonotoneOn (scaledRationalAngularKernel u y) (Icc 0 1) := by
  intro a ha b hb hab
  have hu0 : 0 ≤ u := by linarith
  exact rationalAngularKernel_monotoneOn hy (scaledRational_right_lt_one hu)
    (scaledRational_mem hu ha) (scaledRational_mem hu hb) (div_le_div_of_nonneg_right hab hu0)

theorem scaledRationalAngularKernel_convexOn {u y : ℝ}
    (hu : 1 < u) (hy : 0 ≤ y) (hy2 : y ≤ 2) :
    ConvexOn ℝ (Icc 0 1) (scaledRationalAngularKernel u y) := by
  have hc := rationalAngularKernel_convexOn hy hy2 (scaledRational_right_lt_one hu)
  refine ⟨convex_Icc 0 1, ?_⟩
  intro x hx z hz a b ha hb hab
  have h := hc.2 (scaledRational_mem hu hx) (scaledRational_mem hu hz) ha hb hab
  simpa only [smul_eq_mul, scaledRationalAngularKernel, add_div, mul_div_assoc] using h

theorem scaledRationalAngularKernel_nonneg {u y x : ℝ}
    (hu : 1 < u) (hy : 0 ≤ y) (hx : x ∈ Icc 0 1) :
    0 ≤ scaledRationalAngularKernel u y x := by
  have hm := scaledRationalAngularKernel_monotoneOn hu hy (by norm_num : (0:ℝ) ∈ Icc 0 1) hx hx.1
  simpa [scaledRationalAngularKernel,rationalAngularKernel,rationalAngularDen] using hm

/-- Increasing kernels permit the two initial windows to be combined. -/
theorem two_initial_integrals_le_combined {f : ℝ → ℝ} {s₁ s₂ : ℝ}
    (h₁ : 0 ≤ s₁) (h₂ : 0 ≤ s₂)
    (hf : ContinuousOn f (Icc 0 (s₁+s₂))) (hm : MonotoneOn f (Icc 0 (s₁+s₂))) :
    (∫ x in 0..s₁, f x)+(∫ x in 0..s₂, f x) ≤ ∫ x in 0..s₁+s₂, f x := by
  have hs : 0 ≤ s₁+s₂ := by positivity
  have hi : IntervalIntegrable f volume 0 (s₁+s₂) := hf.intervalIntegrable_of_Icc hs
  have hi1 : IntervalIntegrable f volume 0 s₁ := hi.mono_set (by
    simp only [uIcc_of_le hs, uIcc_of_le h₁]
    exact Set.Icc_subset_Icc (le_refl _) (by linarith))
  have hi2 : IntervalIntegrable f volume 0 s₂ := hi.mono_set (by
    simp only [uIcc_of_le hs, uIcc_of_le h₂]
    exact Set.Icc_subset_Icc (le_refl _) (by linarith))
  have hi3 : IntervalIntegrable f volume s₁ (s₁+s₂) := hi.mono_set (by
    rw [uIcc_of_le hs, uIcc_of_le (by linarith : s₁ ≤ s₁+s₂)]
    exact Set.Icc_subset_Icc h₁ (le_refl _))
  have hshift : IntervalIntegrable (fun x => f (x+s₁)) volume 0 s₂ := by
    convert! hi3.comp_add_right s₁ using 1 <;> ring
  have hmInt := intervalIntegral.integral_mono_on h₂ hi2 hshift (fun x hx =>
    hm ⟨hx.1, by linarith [hx.2]⟩ ⟨by linarith [hx.1], by linarith [hx.2]⟩ (by linarith))
  rw [intervalIntegral.integral_comp_add_right, zero_add] at hmInt
  have hadd := intervalIntegral.integral_add_adjacent_intervals hi1 hi3
  rw [add_comm s₂ s₁] at hmInt
  linarith

namespace CertificateAngular

theorem scaled_kernel_at_node {y : ℝ} (hy : 0 ≤ y) (j : Fin 128) :
    scaledRationalAngularKernel contour y (node j) = Real.log (1+y/pole j) := by
  have hn := node_bounds j
  have hx : node j ∈ Icc (0:ℝ) 1 := ⟨by linarith, hn.2.le⟩
  rw [scaledRationalAngularKernel_formula (by norm_num [contour]) hy hx]
  unfold pole
  congr 1
  field_simp
  <;> ring

/-- The concrete charges lie below the genuine rational-deficit integral. -/
theorem charge_sum_le_half_integral {y : ℝ} (hy : 0 ≤ y) (hy2 : y ≤ 2) :
    (∑ j : Fin 128, weight j*Real.log (1+y/pole j)) ≤
      (1/2)*(∫ x in (2:ℝ)/5..1, scaledRationalAngularKernel contour y x) := by
  have hu : 1 < contour := by norm_num [contour]
  have hc := scaledRationalAngularKernel_continuousOn hu hy
  have hv := scaledRationalAngularKernel_convexOn hu hy hy2
  have hsub : Icc ((2:ℝ)/5) 1 ⊆ Icc (0:ℝ) 1 := Set.Icc_subset_Icc (by norm_num) (le_refl _)
  have hs := midpoint_sum_le_integral ((2:ℝ)/5) (3/640) (by norm_num) 128
    (by convert hc.mono hsub using 1 <;> norm_num)
    (by convert hv.subset hsub (convex_Icc _ _) using 1 <;> norm_num)
  norm_num only [Nat.cast_ofNat] at hs
  have hend : (2:ℝ)/5+(3/640)*128=1 := by norm_num
  rw [← Fin.sum_univ_eq_sum_range] at hs
  have heq : (3/640)*(∑ j : Fin 128,
      scaledRationalAngularKernel contour y ((2:ℝ)/5+(3/640)*((j:ℝ)+1/2))) =
      2*(∑ j : Fin 128, weight j*Real.log (1+y/pole j)) := by
    rw [Finset.mul_sum, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    have hnode : (2:ℝ)/5+(3/640)*((j:ℝ)+1/2)=node j := by unfold node; ring
    rw [hnode, scaled_kernel_at_node hy j]
    unfold weight
    ring
  rw [heq] at hs
  linarith

end CertificateAngular
end Zeta3.Analysis

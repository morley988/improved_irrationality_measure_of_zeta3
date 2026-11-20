import Zeta3.Analysis.ContourRationalScaled
import Mathlib.Analysis.Complex.Basic

/-!
# The actual rational contour potential and its angular deficit

This file relates the real convex kernel to the logarithmic norms in the
original contour density.  The resulting 128-charge deficit holds at every
point of the circle, with no contour or asymptotic hypothesis in the numerical
certificate layer.
-/

noncomputable section
open Set MeasureTheory
open scoped BigOperators
namespace Zeta3.Analysis

def contourAngularCoordinate (u : ℝ) (z : ℂ) : ℝ := 1+z.re/u^2

def rationalContourIntegral (s : ℝ) (z : ℂ) : ℝ :=
  ∫ x in 0..s, Real.log ‖z+(x^2:ℝ)‖

def rationalContourPotential (s₁ s₂ : ℝ) (z : ℂ) : ℝ :=
  rationalContourIntegral s₁ z+rationalContourIntegral s₂ z-rationalContourIntegral 1 z

theorem contour_norm_eq {u : ℝ} {z : ℂ} (hz : Complex.normSq z=u^4) : ‖z‖=u^2 := by
  apply (sq_eq_sq₀ (norm_nonneg _) (sq_nonneg _)).mp
  rw [Complex.sq_norm,hz]
  ring

theorem contourAngularCoordinate_mem {u : ℝ} {z : ℂ} (hu : 0 < u)
    (hz : Complex.normSq z=u^4) : contourAngularCoordinate u z ∈ Icc 0 2 := by
  have hn := Complex.abs_re_le_norm z
  rw [contour_norm_eq hz] at hn
  have hr := abs_le.mp hn
  have hp : 0 < u^2 := sq_pos_of_pos hu
  have hl : -1 ≤ z.re/u^2 := (le_div_iff₀ hp).2 (by nlinarith [hr.1])
  have hh : z.re/u^2 ≤ 1 := (div_le_iff₀ hp).2 (by nlinarith [hr.2])
  unfold contourAngularCoordinate
  constructor <;> linarith

theorem contour_shift_norm_sq {u x : ℝ} {z : ℂ} (hu : 0 < u)
    (hz : Complex.normSq z=u^4) :
    ‖z+(x^2:ℝ)‖^2=(u^2-x^2)^2+2*u^2*x^2*contourAngularCoordinate u z := by
  have hr : z.re^2+z.im^2=u^4 := by simpa only [Complex.normSq_apply,← sq] using hz
  rw [Complex.sq_norm,Complex.normSq_apply,Complex.add_re,Complex.add_im]
  simp only [Complex.ofReal_re,Complex.ofReal_im,add_zero]
  unfold contourAngularCoordinate
  field_simp
  nlinarith [hr]

theorem contour_gap_pos {u x : ℝ} (hu : 1 < u) (hx : x ∈ Icc 0 1) :
    0 < u^2-x^2 := by
  have hh : x < u := hx.2.trans_lt hu
  nlinarith [mul_pos (sub_pos.mpr hh) (by linarith [hx.1] : 0 < u+x)]

theorem contour_shift_norm_pos {u x : ℝ} {z : ℂ} (hu : 1 < u)
    (hz : Complex.normSq z=u^4) (hx : x ∈ Icc 0 1) : 0 < ‖z+(x^2:ℝ)‖ := by
  have hu0 : 0 < u := by linarith
  have hg := contour_gap_pos hu hx
  have hy := contourAngularCoordinate_mem hu0 hz
  have hs := contour_shift_norm_sq (x := x) hu0 hz
  have hn : 0 ≤ 2*u^2*x^2*contourAngularCoordinate u z :=
    mul_nonneg (by positivity) hy.1
  nlinarith [norm_nonneg (z+(x^2:ℝ)),sq_pos_of_pos hg]

theorem contour_negative_log {u x : ℝ} (hu : 1 < u) (hx : x ∈ Icc 0 1) :
    Real.log ‖(-(u^2:ℝ):ℂ)+(x^2:ℝ)‖ = Real.log (u^2-x^2) := by
  have hg := contour_gap_pos hu hx
  have he : (-(u^2:ℝ):ℂ)+(x^2:ℝ)=((x^2-u^2:ℝ):ℂ) := by push_cast; ring
  rw [he,Complex.norm_real,Real.norm_eq_abs,abs_of_neg (by linarith : x^2-u^2<0)]
  congr 1
  ring

theorem contour_log_difference {u x : ℝ} {z : ℂ} (hu : 1 < u)
    (hz : Complex.normSq z=u^4) (hx : x ∈ Icc 0 1) :
    Real.log ‖z+(x^2:ℝ)‖-Real.log ‖(-(u^2:ℝ):ℂ)+(x^2:ℝ)‖ =
      (1/2)*scaledRationalAngularKernel u (contourAngularCoordinate u z) x := by
  have hu0 : 0 < u := by linarith
  have hy := contourAngularCoordinate_mem hu0 hz
  have hg := contour_gap_pos hu hx
  have hn := contour_shift_norm_pos hu hz hx
  have hs := contour_shift_norm_sq (x := x) hu0 hz
  rw [contour_negative_log hu hx,scaledRationalAngularKernel_formula hu hy.1 hx]
  have he : 1+2*u^2*x^2*contourAngularCoordinate u z/(u^2-x^2)^2 =
      ‖z+(x^2:ℝ)‖^2/(u^2-x^2)^2 := by
    field_simp
    nlinarith [hs]
  rw [he,Real.log_div (pow_ne_zero 2 hn.ne') (pow_ne_zero 2 hg.ne'),Real.log_pow,Real.log_pow]
  ring

theorem contour_log_continuousOn {u : ℝ} {z : ℂ} (hu : 1 < u)
    (hz : Complex.normSq z=u^4) :
    ContinuousOn (fun x:ℝ => Real.log ‖z+(x^2:ℝ)‖) (Icc 0 1) := by
  apply ContinuousOn.log (by fun_prop)
  intro x hx
  exact (contour_shift_norm_pos hu hz hx).ne'

theorem rationalContourIntegral_difference {u s : ℝ} {z : ℂ} (hu : 1 < u)
    (hz : Complex.normSq z=u^4) (hs : s ∈ Icc 0 1) :
    rationalContourIntegral s z-rationalContourIntegral s (-(u^2:ℝ):ℂ) =
      (1/2)*(∫ x in 0..s, scaledRationalAngularKernel u (contourAngularCoordinate u z) x) := by
  have hn : Complex.normSq (-(u^2:ℝ):ℂ)=u^4 := by simp [Complex.normSq_ofReal]; ring
  have hsub : Icc (0:ℝ) s ⊆ Icc (0:ℝ) 1 := Set.Icc_subset_Icc (le_refl _) hs.2
  have hi : IntervalIntegrable (fun x:ℝ => Real.log ‖z+(x^2:ℝ)‖) volume 0 s :=
    ((contour_log_continuousOn hu hz).mono hsub).intervalIntegrable_of_Icc hs.1
  have hi0 : IntervalIntegrable (fun x:ℝ => Real.log ‖(-(u^2:ℝ):ℂ)+(x^2:ℝ)‖) volume 0 s :=
    ((contour_log_continuousOn hu hn).mono hsub).intervalIntegrable_of_Icc hs.1
  unfold rationalContourIntegral
  rw [← intervalIntegral.integral_sub hi hi0,← intervalIntegral.integral_const_mul]
  apply intervalIntegral.integral_congr
  intro x hx
  exact contour_log_difference hu hz (hsub (by simpa only [uIcc_of_le hs.1] using hx))

theorem rationalContourPotential_deficit {s₁ s₂ u : ℝ} {z : ℂ}
    (h₁ : 0 ≤ s₁) (h₂ : 0 ≤ s₂) (hs : s₁+s₂ ≤ 1)
    (hu : 1 < u) (hz : Complex.normSq z=u^4) :
    (1/2)*(∫ x in s₁+s₂..1, scaledRationalAngularKernel u (contourAngularCoordinate u z) x) ≤
      rationalContourPotential s₁ s₂ (-(u^2:ℝ):ℂ)-rationalContourPotential s₁ s₂ z := by
  have hu0 : 0 < u := by linarith
  have hy := contourAngularCoordinate_mem hu0 hz
  let f := scaledRationalAngularKernel u (contourAngularCoordinate u z)
  have hc := scaledRationalAngularKernel_continuousOn hu hy.1
  have hm := scaledRationalAngularKernel_monotoneOn hu hy.1
  have hsub : Icc (0:ℝ) (s₁+s₂) ⊆ Icc (0:ℝ) 1 := Set.Icc_subset_Icc (le_refl _) hs
  have hcombine := two_initial_integrals_le_combined h₁ h₂ (hc.mono hsub) (hm.mono hsub)
  have hi : IntervalIntegrable f volume 0 1 := hc.intervalIntegrable_of_Icc (by norm_num)
  have hi1 : IntervalIntegrable f volume 0 (s₁+s₂) :=
    (hc.mono hsub).intervalIntegrable_of_Icc (by positivity)
  have hi2 : IntervalIntegrable f volume (s₁+s₂) 1 := hi.mono_set (by
    rw [uIcc_of_le (by norm_num : (0:ℝ)≤1),uIcc_of_le hs]
    exact Set.Icc_subset_Icc (by positivity) (le_refl _))
  have hadd := intervalIntegral.integral_add_adjacent_intervals hi1 hi2
  have hd1 := rationalContourIntegral_difference hu hz ⟨h₁,by linarith⟩
  have hd2 := rationalContourIntegral_difference hu hz ⟨h₂,by linarith⟩
  have hd3 := rationalContourIntegral_difference hu hz (by norm_num : (1:ℝ) ∈ Icc 0 1)
  unfold rationalContourPotential
  dsimp only [f] at hadd
  linarith

namespace CertificateAngular

theorem charge_sum_le_rationalContour_deficit {z : ℂ}
    (hz : Complex.normSq z=contour^4) :
    (∑ j : Fin 128, weight j*Real.log (1+contourAngularCoordinate contour z/pole j)) ≤
      rationalContourPotential (2/25) (8/25) (-(contour^2:ℝ):ℂ)-
      rationalContourPotential (2/25) (8/25) z := by
  have hu : 1 < contour := by norm_num [contour]
  have hy := contourAngularCoordinate_mem (by norm_num [contour] : 0 < contour) hz
  apply (charge_sum_le_half_integral hy.1 hy.2).trans
  convert! rationalContourPotential_deficit (by norm_num : (0:ℝ)≤2/25)
    (by norm_num : (0:ℝ)≤8/25) (by norm_num) hu hz using 1 <;> norm_num

end CertificateAngular
end Zeta3.Analysis

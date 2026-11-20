import Zeta3.Analysis.ContourRational
import Zeta3.Analysis.GammaPotentialBridge

/-! # Exact evaluation at the negative real point of the contour -/

noncomputable section
open Set MeasureTheory
namespace Zeta3.Analysis

theorem gammaNegativeIntegral_hasDerivAt {u x : ℝ}
    (hu : 0 < u) (hx : 0 ≤ x) (hxu : x < u) :
    HasDerivAt (gammaNegativeIntegral u) (Real.log (u^2-x^2)) x := by
  have hp : 0 < u+x := by linarith
  have hm : 0 < u-x := by linarith
  have hg : 0 < u^2-x^2 := by nlinarith [mul_pos hp hm]
  have hfirst := (hasDerivAt_id x).mul
    ((((hasDerivAt_id x).pow 2).const_sub (u^2)).log hg.ne')
  have hquot := ((hasDerivAt_id x).const_add u).div
    ((hasDerivAt_id x).const_sub u) hm.ne'
  have hlog := (hquot.log (div_ne_zero hp.ne' hm.ne')).const_mul u
  have h := (hfirst.add hlog).sub ((hasDerivAt_id x).const_mul 2)
  convert! h using 1
  simp only [Pi.pow_apply,Pi.mul_apply,Pi.add_apply,Pi.sub_apply,Pi.div_apply,
    id_eq,Nat.cast_ofNat,Nat.reduceSub,pow_one,mul_one,one_mul]
  field_simp
  <;> ring

theorem gammaNegativeIntegral_eq_integral {u s : ℝ}
    (hu : 0 < u) (hs : 0 ≤ s) (hsu : s < u) :
    gammaNegativeIntegral u s = ∫ x in 0..s, Real.log (u^2-x^2) := by
  have hd (x : ℝ) (hx : x ∈ Icc 0 s) := gammaNegativeIntegral_hasDerivAt hu hx.1 (hx.2.trans_lt hsu)
  have hc : ContinuousOn (gammaNegativeIntegral u) (Icc 0 s) := fun x hx =>
    (hd x hx).continuousAt.continuousWithinAt
  have hg (x : ℝ) (hx : x ∈ Icc 0 s) : u^2-x^2 ≠ 0 := by
    have ha : 0 < u+x := by linarith [hx.1]
    have hb : 0 < u-x := by linarith [hx.2]
    have hp : 0 < u^2-x^2 := by nlinarith [mul_pos ha hb]
    exact hp.ne'
  have hlog : ContinuousOn (fun x : ℝ => Real.log (u^2-x^2)) (Icc 0 s) :=
    (by fun_prop : Continuous (fun x:ℝ => u^2-x^2)).continuousOn.log hg
  have hi : IntervalIntegrable (fun x : ℝ => Real.log (u^2-x^2)) volume 0 s :=
    hlog.intervalIntegrable_of_Icc hs
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hs hc
    (fun x hx => hd x (Ioo_subset_Icc_self hx)) hi
  have hzero : gammaNegativeIntegral u 0=0 := by simp [gammaNegativeIntegral, hu.ne']
  rw [hzero,sub_zero] at h
  exact h.symm

theorem rationalContourIntegral_negative {u s : ℝ} (hu : 1 < u) (hs : s ∈ Icc 0 1) :
    rationalContourIntegral s (-(u^2:ℝ):ℂ) = gammaNegativeIntegral u s := by
  rw [gammaNegativeIntegral_eq_integral (by linarith) hs.1 (hs.2.trans_lt hu)]
  unfold rationalContourIntegral
  apply intervalIntegral.integral_congr
  intro x hx
  have hx' : x ∈ Icc (0:ℝ) s := by simpa only [uIcc_of_le hs.1] using hx
  exact contour_negative_log hu ⟨hx'.1,hx'.2.trans hs.2⟩

theorem rationalContourPotential_negative {s₁ s₂ u : ℝ}
    (hu : 1 < u) (h₁ : s₁ ∈ Icc 0 1) (h₂ : s₂ ∈ Icc 0 1) :
    rationalContourPotential s₁ s₂ (-(u^2:ℝ):ℂ) =
      gammaNegativeIntegral u s₁+gammaNegativeIntegral u s₂-gammaNegativeIntegral u 1 := by
  unfold rationalContourPotential
  rw [rationalContourIntegral_negative hu h₁,rationalContourIntegral_negative hu h₂,
    rationalContourIntegral_negative hu (by norm_num : (1:ℝ) ∈ Icc 0 1)]

theorem physicalGammaAtEndpoint_eq_contour_potential (s₁ s₂ u : ℝ)
    (h₁ : 0 < s₁) (h₁one : s₁ ≤ 1) (h₂ : 0 < s₂) (h₂one : s₂ ≤ 1)
    (hu : 1 < u) {b : ℝ} (hb : 0 ≤ b) :
    physicalGammaAtEndpoint s₁ s₂ u b =
      rationalContourPotential s₁ s₂ (-(u^2:ℝ):ℂ)+
      4*physicalImaginaryPotential s₁ s₂ h₁ h₂ b u-
      physicalEquilibriumAtEndpoint s₁ s₂ h₁ h₂ b := by
  rw [rationalContourPotential_negative hu ⟨h₁.le,h₁one⟩ ⟨h₂.le,h₂one⟩]
  exact physicalGammaAtEndpoint_eq_potential s₁ s₂ u h₁ h₂ (by linarith) hb

end Zeta3.Analysis

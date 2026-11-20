import Zeta3.Analysis.ContourRiemann
import Zeta3.Analysis.PhysicalNorm

/-!
# An exact uniform bound for the finite contour rational product

The original polynomial products are rescaled exactly.  The finite sum
bounds give a constant loss `(u²/(u²-1))³`, independent of N and of the
angle.  Thus no external Riemann-limit assumption enters the response bound.
-/

noncomputable section
open Set MeasureTheory Polynomial
open scoped BigOperators
namespace Zeta3.Analysis

def contourNormProduct (N m d : ℕ) (z : ℂ) : ℝ :=
  ∏ i ∈ Finset.range m, ‖z+((((i+d:ℕ):ℝ)/N)^2:ℝ)‖

def contourProductConstant (u : ℝ) : ℝ := (u^2/(u^2-1))^3

def rationalContourWeight (N m₁ m₂ : ℕ) (z : ℂ) : ℂ :=
  (Zeta3.Construction.positiveFactor m₁).eval₂ (Rat.castHom ℂ) ((N:ℂ)^2*z)*
  (Zeta3.Construction.positiveFactor m₂).eval₂ (Rat.castHom ℂ) ((N:ℂ)^2*z)/
  (Zeta5.Construction.denominator N).eval₂ (Rat.castHom ℂ) ((N:ℂ)^2*z)

theorem contourProductConstant_pos {u : ℝ} (hu : 1 < u) : 0 < contourProductConstant u := by
  have hg : 0 < u^2-1 := by nlinarith
  unfold contourProductConstant
  positivity

theorem contourNormProduct_nonneg (N m d : ℕ) (z : ℂ) : 0 ≤ contourNormProduct N m d z := by
  unfold contourNormProduct
  exact Finset.prod_nonneg (fun _ _ => norm_nonneg _)

theorem contourNormProduct_left_upper {u : ℝ} {z : ℂ} (hu : 1 < u)
    (hz : Complex.normSq z=u^4) (N m : ℕ) (hN : 0 < N) (hm : m ≤ N) :
    contourNormProduct N m 0 z ≤
      Real.exp ((N:ℝ)*rationalContourIntegral ((m:ℝ)/N) z)*(u^2/(u^2-1)) := by
  have hNr : (0:ℝ)<N := by exact_mod_cast hN
  have hs : (m:ℝ)/N ∈ Icc (0:ℝ) 1 := ⟨by positivity,(div_le_one hNr).2 (by exact_mod_cast hm)⟩
  have hg : 0 < u^2-1 := by nlinarith
  have hu0 : 0 < u^2 := by nlinarith
  have hlog := contour_radialLog_antitoneOn hu hs (by norm_num : (1:ℝ)∈Icc 0 1) hs.2
  norm_num only [one_pow] at hlog
  have hb := (contour_logarithmic_grid_bounds hu hz N m hN hm).1
  have hb' : (∑ i ∈ Finset.range m, Real.log ‖z+(((i:ℝ)/N)^2:ℝ)‖) ≤
      (N:ℝ)*rationalContourIntegral ((m:ℝ)/N) z+Real.log (u^2)-Real.log (u^2-1) := by
    linarith
  have he := Real.exp_le_exp.mpr hb'
  rw [Real.exp_sub,Real.exp_add,Real.exp_log hu0,Real.exp_log hg,Real.exp_sum] at he
  have hprod : (∏ i ∈ Finset.range m, Real.exp (Real.log ‖z+(((i:ℝ)/N)^2:ℝ)‖))=
      contourNormProduct N m 0 z := by
    unfold contourNormProduct
    apply Finset.prod_congr rfl
    intro i hi
    simp only [Nat.add_zero]
    apply Real.exp_log
    apply contour_shift_norm_pos hu hz
    refine ⟨by positivity,(div_le_one hNr).2 ?_⟩
    exact_mod_cast (Finset.mem_range.mp hi).le.trans hm
  rw [hprod] at he
  simpa only [mul_div_assoc] using he

theorem contourNormProduct_right_lower {u : ℝ} {z : ℂ} (hu : 1 < u)
    (hz : Complex.normSq z=u^4) (N : ℕ) (hN : 0 < N) :
    Real.exp ((N:ℝ)*rationalContourIntegral 1 z)*((u^2-1)/u^2) ≤
      contourNormProduct N N 1 z := by
  have hNr : (0:ℝ)<N := by exact_mod_cast hN
  have hg : 0 < u^2-1 := by nlinarith
  have hu0 : 0 < u^2 := by nlinarith
  have hb := (contour_logarithmic_grid_bounds hu hz N N hN (le_refl _)).2
  rw [div_self hNr.ne',one_pow] at hb
  have he := Real.exp_le_exp.mpr hb
  rw [Real.exp_sub,Real.exp_add,Real.exp_log hg,Real.exp_log hu0,Real.exp_sum] at he
  have hprod : (∏ i ∈ Finset.range N, Real.exp (Real.log ‖z+((((i+1:ℕ):ℝ)/N)^2:ℝ)‖))=
      contourNormProduct N N 1 z := by
    unfold contourNormProduct
    apply Finset.prod_congr rfl
    intro i hi
    apply Real.exp_log
    apply contour_shift_norm_pos hu hz
    refine ⟨by positivity,(div_le_one hNr).2 ?_⟩
    exact_mod_cast Finset.mem_range.mp hi
  rw [hprod] at he
  simpa only [mul_div_assoc] using he

theorem contourNormProduct_ratio_upper {u : ℝ} {z : ℂ} (hu : 1 < u)
    (hz : Complex.normSq z=u^4) (N m₁ m₂ : ℕ) (hN : 0 < N)
    (h₁ : m₁ ≤ N) (h₂ : m₂ ≤ N) :
    contourNormProduct N m₁ 0 z*contourNormProduct N m₂ 0 z/contourNormProduct N N 1 z ≤
      contourProductConstant u*Real.exp ((N:ℝ)*rationalContourPotential ((m₁:ℝ)/N) ((m₂:ℝ)/N) z) := by
  have hg : 0 < u^2-1 := by nlinarith
  have hu0 : 0 < u^2 := by nlinarith
  have hl := contourNormProduct_left_upper hu hz N m₁ hN h₁
  have hr := contourNormProduct_left_upper hu hz N m₂ hN h₂
  have hd := contourNormProduct_right_lower hu hz N hN
  have hn := mul_le_mul hl hr (contourNormProduct_nonneg _ _ _ _) (by positivity)
  have hq := div_le_div₀ (by positivity) hn (by positivity) hd
  refine hq.trans_eq ?_
  unfold contourProductConstant rationalContourPotential
  rw [mul_sub,mul_add,Real.exp_sub,Real.exp_add]
  field_simp
  <;> ring

theorem complex_shifted_product_scale_norm (N m d : ℕ) (hN : 0 < N) (z : ℂ) :
    ‖∏ i ∈ Finset.range m, ((N:ℂ)^2*z+((i+d:ℕ):ℂ)^2)‖ =
      (N:ℝ)^(2*m)*contourNormProduct N m d z := by
  have hNc : (N:ℂ)≠0 := by exact_mod_cast hN.ne'
  have hf (i:ℕ) : (N:ℂ)^2*z+((i+d:ℕ):ℂ)^2=
      (N:ℂ)^2*(z+((((i+d:ℕ):ℝ)/N)^2:ℝ)) := by
    push_cast
    field_simp
  rw [show (∏ i ∈ Finset.range m, ((N:ℂ)^2*z+((i+d:ℕ):ℂ)^2))=
      ∏ i ∈ Finset.range m, (N:ℂ)^2*(z+((((i+d:ℕ):ℝ)/N)^2:ℝ)) by
        exact Finset.prod_congr rfl (fun i _ => hf i)]
  rw [Finset.prod_mul_distrib]
  simp only [Finset.prod_const,Finset.card_range,norm_mul,norm_pow,norm_natCast,norm_prod,
    ← pow_mul,contourNormProduct]

theorem positiveFactor_scaled_norm (N m : ℕ) (hN : 0 < N) (z : ℂ) :
    ‖(Zeta3.Construction.positiveFactor m).eval₂ (Rat.castHom ℂ) ((N:ℂ)^2*z)‖=
      (N:ℝ)^(2*m)*contourNormProduct N m 0 z := by
  simp only [Zeta3.Construction.positiveFactor,eval₂_finset_prod,eval₂_add,eval₂_X,eval₂_C,
    Rat.coe_castHom,Rat.cast_pow,Rat.cast_natCast]
  simpa only [Nat.add_zero] using complex_shifted_product_scale_norm N m 0 hN z

theorem denominator_scaled_norm (N : ℕ) (hN : 0 < N) (z : ℂ) :
    ‖(Zeta5.Construction.denominator N).eval₂ (Rat.castHom ℂ) ((N:ℂ)^2*z)‖=
      (N:ℝ)^(2*N)*contourNormProduct N N 1 z := by
  simp only [Zeta5.Construction.denominator,eval₂_finset_prod,eval₂_add,eval₂_X,eval₂_C,
    Rat.coe_castHom,Rat.cast_pow,Rat.cast_natCast]
  exact complex_shifted_product_scale_norm N N 1 hN z

theorem rationalContourWeight_norm_eq (N m₁ m₂ : ℕ) (hN : 0 < N) (z : ℂ) :
    ‖rationalContourWeight N m₁ m₂ z‖=physicalWeightScale N m₁ m₂*
      (contourNormProduct N m₁ 0 z*contourNormProduct N m₂ 0 z/contourNormProduct N N 1 z) := by
  unfold rationalContourWeight
  rw [norm_div,norm_mul,positiveFactor_scaled_norm N m₁ hN z,
    positiveFactor_scaled_norm N m₂ hN z,denominator_scaled_norm N hN z]
  unfold physicalWeightScale
  rw [Nat.mul_add,pow_add]
  ring

/-- Actual finite rational weight on the scaled contour, with a uniform constant loss. -/
theorem rationalContourWeight_norm_upper {u : ℝ} {z : ℂ} (hu : 1 < u)
    (hz : Complex.normSq z=u^4) (N m₁ m₂ : ℕ) (hN : 0 < N)
    (h₁ : m₁ ≤ N) (h₂ : m₂ ≤ N) :
    ‖rationalContourWeight N m₁ m₂ z‖ ≤ physicalWeightScale N m₁ m₂*contourProductConstant u*
      Real.exp ((N:ℝ)*rationalContourPotential ((m₁:ℝ)/N) ((m₂:ℝ)/N) z) := by
  rw [rationalContourWeight_norm_eq N m₁ m₂ hN z,mul_assoc]
  exact mul_le_mul_of_nonneg_left (contourNormProduct_ratio_upper hu hz N m₁ m₂ hN h₁ h₂)
    (physicalWeightScale_pos hN m₁ m₂).le

end Zeta3.Analysis

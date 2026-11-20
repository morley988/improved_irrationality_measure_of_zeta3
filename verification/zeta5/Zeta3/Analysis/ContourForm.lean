import Zeta3.Analysis.ContourCoefficient

/-!
# The genuine window coefficient as an angular bilinear integral

The numerator includes the two actual factorial windows and the exact
physical rescaling.  All powers of N, the contour variable and the Jacobian
are retained in the density.
-/

noncomputable section
open Set MeasureTheory Polynomial
open scoped BigOperators
namespace Zeta3.Analysis

def complexRescalePolynomial (N : ℕ) (p : ℂ[X]) : ℂ[X] :=
  p.comp (C (((N:ℂ)^2)⁻¹)*X)

def complexWindowCoefficient (N m₁ m₂ : ℕ) (p q : ℂ[X]) : ℂ :=
  complexNumeratorLinear N
    ((Zeta3.Construction.positiveFactor m₁).map (Rat.castHom ℂ)*
      (Zeta3.Construction.positiveFactor m₂).map (Rat.castHom ℂ)*
      complexRescalePolynomial N p*complexRescalePolynomial N q)

def contourComplexDensity (N m₁ m₂ : ℕ) (u θ : ℝ) : ℂ :=
  -(N:ℂ)^4/(2*Real.pi)*(circleMap 0 (u^2) θ)^2*
    rationalContourWeight N m₁ m₂ (circleMap 0 (u^2) θ)

def contourPositiveDensity (N m₁ m₂ : ℕ) (u θ : ℝ) : ℝ :=
  (N:ℝ)^4/(2*Real.pi)*u^4*‖rationalContourWeight N m₁ m₂ (circleMap 0 (u^2) θ)‖

theorem complexRescalePolynomial_eval (N : ℕ) (hN : 0 < N) (p : ℂ[X]) (z : ℂ) :
    (complexRescalePolynomial N p).eval ((N:ℂ)^2*z)=p.eval z := by
  have hNc : (N:ℂ)≠0 := by exact_mod_cast hN.ne'
  simp [complexRescalePolynomial,eval_comp,eval_mul,eval_C,eval_X,hNc]

theorem complexWindowCoefficient_circle (N m₁ m₂ : ℕ) (p q : ℂ[X])
    (u : ℝ) (hN : 0 < N) (hu : 1 < u) :
    complexWindowCoefficient N m₁ m₂ p q=-(N:ℂ)^4*(2*Real.pi*Complex.I)⁻¹*
      (∮ z in C(0,u^2),z*rationalContourWeight N m₁ m₂ z*p.eval z*q.eval z) := by
  unfold complexWindowCoefficient
  rw [complexNumeratorLinear_eq_scaled_circleIntegral N _ u hN hu]
  congr 1
  apply circleIntegral.integral_congr (sq_nonneg _)
  intro z hz
  dsimp only
  simp only [eval_mul,eval_map,complexRescalePolynomial_eval N hN]
  unfold rationalContourWeight complexDenominator
  rw [eval_map]
  ring

theorem complexWindowCoefficient_angular (N m₁ m₂ : ℕ) (p q : ℂ[X])
    (u : ℝ) (hN : 0 < N) (hu : 1 < u) :
    complexWindowCoefficient N m₁ m₂ p q=
      ∫ θ in 0..2*Real.pi, contourComplexDensity N m₁ m₂ u θ*
        p.eval (circleMap 0 (u^2) θ)*q.eval (circleMap 0 (u^2) θ) := by
  rw [complexWindowCoefficient_circle N m₁ m₂ p q u hN hu]
  unfold circleIntegral
  rw [← intervalIntegral.integral_const_mul]
  apply intervalIntegral.integral_congr
  intro θ hθ
  simp only [deriv_circleMap,smul_eq_mul]
  unfold contourComplexDensity
  have hpi : (Real.pi:ℂ)≠0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  have hI : Complex.I≠0 := Complex.I_ne_zero
  field_simp
  <;> ring

theorem circleMap_normSq_square_radius (u θ : ℝ) :
    Complex.normSq (circleMap 0 (u^2) θ)=u^4 := by
  rw [Complex.normSq_eq_norm_sq,norm_circleMap_zero,abs_of_nonneg (sq_nonneg _)]
  ring

theorem contourPositiveDensity_nonneg (N m₁ m₂ : ℕ) (u θ : ℝ) :
    0 ≤ contourPositiveDensity N m₁ m₂ u θ := by
  unfold contourPositiveDensity
  positivity

theorem contourComplexDensity_norm (N m₁ m₂ : ℕ) (u θ : ℝ) :
    ‖contourComplexDensity N m₁ m₂ u θ‖=contourPositiveDensity N m₁ m₂ u θ := by
  unfold contourComplexDensity contourPositiveDensity
  simp only [norm_mul,norm_div,norm_neg,norm_pow,norm_natCast,show ‖(2:ℂ)‖=(2:ℝ) by norm_num,
    Complex.norm_real,Real.norm_eq_abs,abs_of_pos Real.pi_pos,norm_circleMap_zero,
    abs_of_nonneg (sq_nonneg u)]
  ring

theorem contourPositiveDensity_upper {u : ℝ} (hu : 1 < u)
    (N m₁ m₂ : ℕ) (hN : 0 < N) (h₁ : m₁ ≤ N) (h₂ : m₂ ≤ N) (θ : ℝ) :
    contourPositiveDensity N m₁ m₂ u θ ≤
      (N:ℝ)^4/(2*Real.pi)*u^4*physicalWeightScale N m₁ m₂*contourProductConstant u*
      Real.exp ((N:ℝ)*rationalContourPotential ((m₁:ℝ)/N) ((m₂:ℝ)/N) (circleMap 0 (u^2) θ)) := by
  have h := rationalContourWeight_norm_upper hu (circleMap_normSq_square_radius u θ)
    N m₁ m₂ hN h₁ h₂
  unfold contourPositiveDensity
  convert! mul_le_mul_of_nonneg_left h
    (by positivity : 0 ≤ (N:ℝ)^4/(2*Real.pi)*u^4) using 1 <;> ring

end Zeta3.Analysis

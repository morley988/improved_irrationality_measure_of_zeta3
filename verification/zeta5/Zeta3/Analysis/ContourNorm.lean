import Zeta3.Analysis.ContourPhase

/-!
# The normalized positive contour quadratic form

This is the concrete positive norm used in the spectral comparison.  It is
normalized by exactly the same physical weight scale as the real-axis norm.
A pointwise exponential contour bound integrates with only the explicit
factor N^4 u^4 (u²/(u²-1))³.
-/

noncomputable section
open Set MeasureTheory Polynomial
open scoped BigOperators
namespace Zeta3.Analysis

def normalizedContourPositiveDensity (N m₁ m₂ : ℕ) (u θ : ℝ) : ℝ :=
  contourPositiveDensity N m₁ m₂ u θ/physicalWeightScale N m₁ m₂

def normalizedContourSquaredNorm (N m₁ m₂ : ℕ) (u : ℝ) (p : ℂ[X]) : ℝ :=
  contourSquaredNorm N m₁ m₂ u p/physicalWeightScale N m₁ m₂

/-- The real polynomial form used by the self-adjoint comparison operator. -/
def positiveContourNorm (N m₁ m₂ : ℕ) (u : ℝ) (p : ℝ[X]) : ℝ :=
  normalizedContourSquaredNorm N m₁ m₂ u (p.map Complex.ofRealHom)

def normalizedComplexWindowCoefficient (N m₁ m₂ : ℕ) (p q : ℂ[X]) : ℂ :=
  complexWindowCoefficient N m₁ m₂ p q/(physicalWeightScale N m₁ m₂:ℂ)

theorem normalizedContourPositiveDensity_nonneg (N m₁ m₂ : ℕ) (hN : 0 < N) (u θ : ℝ) :
    0 ≤ normalizedContourPositiveDensity N m₁ m₂ u θ :=
  div_nonneg (contourPositiveDensity_nonneg N m₁ m₂ u θ) (physicalWeightScale_pos hN m₁ m₂).le

theorem normalizedContourPositiveDensity_continuous (N m₁ m₂ : ℕ) (hN : 0 < N)
    {u : ℝ} (hu : 1 < u) : Continuous (normalizedContourPositiveDensity N m₁ m₂ u) :=
  (contourPositiveDensity_continuous N m₁ m₂ hN hu).div_const _

theorem normalizedContourSquaredNorm_integral (N m₁ m₂ : ℕ) (u : ℝ) (p : ℂ[X]) :
    normalizedContourSquaredNorm N m₁ m₂ u p=
      ∫ θ in 0..2*Real.pi, normalizedContourPositiveDensity N m₁ m₂ u θ*
        ‖p.eval (circleMap 0 (u^2) θ)‖^2 := by
  rw [normalizedContourSquaredNorm,contourSquaredNorm_integral,
    ← intervalIntegral.integral_div]
  apply intervalIntegral.integral_congr
  intro θ hθ
  unfold normalizedContourPositiveDensity
  ring

theorem positiveContourNorm_integral (N m₁ m₂ : ℕ) (u : ℝ) (p : ℝ[X]) :
    positiveContourNorm N m₁ m₂ u p=
      ∫ θ in 0..2*Real.pi, normalizedContourPositiveDensity N m₁ m₂ u θ*
        ‖p.eval₂ Complex.ofRealHom (circleMap 0 (u^2) θ)‖^2 := by
  rw [positiveContourNorm,normalizedContourSquaredNorm_integral]
  simp only [eval_map]

theorem normalizedContourSquaredNorm_nonneg (N m₁ m₂ : ℕ) (hN : 0 < N) (u : ℝ) (p : ℂ[X]) :
    0 ≤ normalizedContourSquaredNorm N m₁ m₂ u p := by
  unfold normalizedContourSquaredNorm contourSquaredNorm
  exact div_nonneg (integral_nonneg (fun _ => sq_nonneg _)) (physicalWeightScale_pos hN m₁ m₂).le

theorem positiveContourNorm_nonneg (N m₁ m₂ : ℕ) (hN : 0 < N) (u : ℝ) (p : ℝ[X]) :
    0 ≤ positiveContourNorm N m₁ m₂ u p :=
  normalizedContourSquaredNorm_nonneg N m₁ m₂ hN u _

theorem normalizedContourPositiveDensity_upper {u : ℝ} (hu : 1 < u)
    (N m₁ m₂ : ℕ) (hN : 0 < N) (h₁ : m₁ ≤ N) (h₂ : m₂ ≤ N) (θ : ℝ) :
    normalizedContourPositiveDensity N m₁ m₂ u θ ≤
      ((N:ℝ)^4/(2*Real.pi)*u^4*contourProductConstant u)*
      Real.exp ((N:ℝ)*rationalContourPotential ((m₁:ℝ)/N) ((m₂:ℝ)/N) (circleMap 0 (u^2) θ)) := by
  unfold normalizedContourPositiveDensity
  apply (div_le_iff₀ (physicalWeightScale_pos hN m₁ m₂)).2
  convert! contourPositiveDensity_upper hu N m₁ m₂ hN h₁ h₂ θ using 1 <;> ring

/-- Turn the proved pointwise contour bound into the actual positive contour norm. -/
theorem positiveContourNorm_le_of_exponential_bound {u A : ℝ}
    (hu : 1 < u) (N m₁ m₂ : ℕ) (hN : 0 < N) (h₁ : m₁ ≤ N) (h₂ : m₂ ≤ N)
    (p : ℝ[X])
    (hbound : ∀ z : ℂ, Complex.normSq z=u^4 →
      Real.exp ((N:ℝ)*rationalContourPotential ((m₁:ℝ)/N) ((m₂:ℝ)/N) z)*
        ‖p.eval₂ Complex.ofRealHom z‖^2 ≤ A) :
    positiveContourNorm N m₁ m₂ u p ≤ (N:ℝ)^4*u^4*contourProductConstant u*A := by
  have hpref : 0 ≤ (N:ℝ)^4/(2*Real.pi)*u^4*contourProductConstant u := by
    positivity [contourProductConstant_pos hu]
  have hpoint (θ:ℝ) : normalizedContourPositiveDensity N m₁ m₂ u θ*
      ‖p.eval₂ Complex.ofRealHom (circleMap 0 (u^2) θ)‖^2 ≤
      ((N:ℝ)^4/(2*Real.pi)*u^4*contourProductConstant u)*A := by
    have hd := mul_le_mul_of_nonneg_right (normalizedContourPositiveDensity_upper hu N m₁ m₂ hN h₁ h₂ θ)
      (sq_nonneg ‖p.eval₂ Complex.ofRealHom (circleMap 0 (u^2) θ)‖)
    have hp := mul_le_mul_of_nonneg_left (hbound _ (circleMap_normSq_square_radius u θ)) hpref
    exact hd.trans (by simpa only [mul_assoc] using hp)
  have hc : Continuous (fun θ => normalizedContourPositiveDensity N m₁ m₂ u θ*
      ‖p.eval₂ Complex.ofRealHom (circleMap 0 (u^2) θ)‖^2) :=
    (normalizedContourPositiveDensity_continuous N m₁ m₂ hN hu).mul
      (((p.continuous_eval₂ Complex.ofRealHom).comp (continuous_circleMap _ _)).norm.pow 2)
  rw [positiveContourNorm_integral]
  have hi := intervalIntegral.integral_mono_on (μ := volume) (by positivity : (0:ℝ)≤2*Real.pi)
    (hc.intervalIntegrable 0 (2*Real.pi)) intervalIntegrable_const (fun θ hθ => hpoint θ)
  rw [intervalIntegral.integral_const] at hi
  simp only [smul_eq_mul,sub_zero] at hi
  convert! hi using 1
  field_simp

/-- Cauchy--Schwarz after the same normalization as the physical Gram form. -/
theorem normalizedComplexWindowCoefficient_norm_le (N m₁ m₂ : ℕ) (p q : ℂ[X])
    (u : ℝ) (hN : 0 < N) (hu : 1 < u) :
    ‖normalizedComplexWindowCoefficient N m₁ m₂ p q‖ ≤
      Real.sqrt (normalizedContourSquaredNorm N m₁ m₂ u p)*
      Real.sqrt (normalizedContourSquaredNorm N m₁ m₂ u q) := by
  have hs := physicalWeightScale_pos hN m₁ m₂
  have hp : 0 ≤ contourSquaredNorm N m₁ m₂ u p := by
    unfold contourSquaredNorm
    exact integral_nonneg (fun _ => sq_nonneg _)
  have hq : 0 ≤ contourSquaredNorm N m₁ m₂ u q := by
    unfold contourSquaredNorm
    exact integral_nonneg (fun _ => sq_nonneg _)
  unfold normalizedComplexWindowCoefficient normalizedContourSquaredNorm
  rw [norm_div,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hs,
    Real.sqrt_div hp,Real.sqrt_div hq]
  have h := div_le_div_of_nonneg_right (complexWindowCoefficient_norm_le N m₁ m₂ p q u hN hu) hs.le
  convert! h using 1
  rw [div_mul_div_comm,← sq,Real.sq_sqrt hs.le]

def normalizedComplexWindowMatrix {ι : Type*} (N m₁ m₂ : ℕ) (p : ι → ℂ[X]) : Matrix ι ι ℂ :=
  fun i j => normalizedComplexWindowCoefficient N m₁ m₂ (p i) (p j)

theorem normalizedComplexWindowCoefficient_response_majorant {ι : Type*} [Fintype ι] [DecidableEq ι]
    (N m₁ m₂ : ℕ) (p : ι → ℂ[X]) (u : ℝ) (hN : 0 < N) (hu : 1 < u) (h : ℂ) :
    ‖(1+h • normalizedComplexWindowMatrix N m₁ m₂ p).det‖≤
      (Nat.factorial (Fintype.card ι):ℝ)*
        ∏ i,(1+‖h‖*normalizedContourSquaredNorm N m₁ m₂ u (p i)) := by
  apply determinant_response_majorant
  · intro i
    exact normalizedContourSquaredNorm_nonneg N m₁ m₂ hN u (p i)
  · intro i j
    exact normalizedComplexWindowCoefficient_norm_le N m₁ m₂ (p i) (p j) u hN hu

end Zeta3.Analysis

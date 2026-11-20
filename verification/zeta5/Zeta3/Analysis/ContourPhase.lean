import Zeta3.Analysis.ContourForm
import Zeta3.Analysis.IntegralGramMajorant

/-!
# Positive density and phase of the actual coefficient contour

The complex window coefficient is exactly a bilinear phase integral.  Its
positive norm form is defined from the modulus of the genuine contour
density.  Integrability and the phase bound are proved from the explicit
finite products, then the general determinant majorant applies.
-/

noncomputable section
open Set MeasureTheory Polynomial
open scoped BigOperators
namespace Zeta3.Analysis

def contourAngularMeasure : Measure ℝ := volume.restrict (Ioc 0 (2*Real.pi))

def contourPhase (N m₁ m₂ : ℕ) (u θ : ℝ) : ℂ :=
  contourComplexDensity N m₁ m₂ u θ/(contourPositiveDensity N m₁ m₂ u θ:ℂ)

def contourFeature (N m₁ m₂ : ℕ) (u : ℝ) (p : ℂ[X]) (θ : ℝ) : ℂ :=
  (Real.sqrt (contourPositiveDensity N m₁ m₂ u θ):ℂ)*p.eval (circleMap 0 (u^2) θ)

def contourSquaredNorm (N m₁ m₂ : ℕ) (u : ℝ) (p : ℂ[X]) : ℝ :=
  ∫ θ, ‖contourFeature N m₁ m₂ u p θ‖^2 ∂contourAngularMeasure

theorem contour_denominator_ne_zero (N : ℕ) (hN : 0 < N) {u : ℝ} (hu : 1 < u) (θ : ℝ) :
    (Zeta5.Construction.denominator N).eval₂ (Rat.castHom ℂ)
      ((N:ℂ)^2*circleMap 0 (u^2) θ)≠0 := by
  have h := contourNormProduct_right_lower hu (circleMap_normSq_square_radius u θ) N hN
  have hg : 0 < u^2-1 := by nlinarith
  have hu2 : 0 < u^2 := by nlinarith
  have hp : 0 < contourNormProduct N N 1 (circleMap 0 (u^2) θ) := lt_of_lt_of_le (by positivity) h
  apply norm_ne_zero_iff.mp
  rw [denominator_scaled_norm N hN]
  exact ne_of_gt (mul_pos (by positivity) hp)

theorem rationalContourWeight_circle_continuous (N m₁ m₂ : ℕ) (hN : 0 < N)
    {u : ℝ} (hu : 1 < u) :
    Continuous (fun θ => rationalContourWeight N m₁ m₂ (circleMap 0 (u^2) θ)) := by
  have harg : Continuous (fun θ => (N:ℂ)^2*circleMap 0 (u^2) θ) := by fun_prop
  unfold rationalContourWeight
  exact (((Zeta3.Construction.positiveFactor m₁).continuous_eval₂ (Rat.castHom ℂ)).comp harg |>.mul
    (((Zeta3.Construction.positiveFactor m₂).continuous_eval₂ (Rat.castHom ℂ)).comp harg)).div
      (((Zeta5.Construction.denominator N).continuous_eval₂ (Rat.castHom ℂ)).comp harg)
      (contour_denominator_ne_zero N hN hu)

theorem contourComplexDensity_continuous (N m₁ m₂ : ℕ) (hN : 0 < N)
    {u : ℝ} (hu : 1 < u) : Continuous (contourComplexDensity N m₁ m₂ u) := by
  unfold contourComplexDensity
  exact (by fun_prop : Continuous (fun θ => -(N:ℂ)^4/(2*Real.pi)*(circleMap 0 (u^2) θ)^2)).mul
    (rationalContourWeight_circle_continuous N m₁ m₂ hN hu)

theorem contourPositiveDensity_continuous (N m₁ m₂ : ℕ) (hN : 0 < N)
    {u : ℝ} (hu : 1 < u) : Continuous (contourPositiveDensity N m₁ m₂ u) := by
  convert! (contourComplexDensity_continuous N m₁ m₂ hN hu).norm using 1
  funext θ
  exact (contourComplexDensity_norm N m₁ m₂ u θ).symm

theorem contourPhase_norm_le_one (N m₁ m₂ : ℕ) (u θ : ℝ) :
    ‖contourPhase N m₁ m₂ u θ‖≤1 := by
  unfold contourPhase
  rw [norm_div,contourComplexDensity_norm,Complex.norm_real,Real.norm_eq_abs,
    abs_of_nonneg (contourPositiveDensity_nonneg N m₁ m₂ u θ)]
  by_cases h:contourPositiveDensity N m₁ m₂ u θ=0
  · simp [h]
  · simp [h]

theorem contourPhase_mul_density (N m₁ m₂ : ℕ) (u θ : ℝ) :
    contourPhase N m₁ m₂ u θ*(contourPositiveDensity N m₁ m₂ u θ:ℂ)=
      contourComplexDensity N m₁ m₂ u θ := by
  unfold contourPhase
  by_cases h:contourPositiveDensity N m₁ m₂ u θ=0
  · have hz : contourComplexDensity N m₁ m₂ u θ=0 := by
      apply norm_eq_zero.mp
      rw [contourComplexDensity_norm,h]
    simp [h,hz]
  · exact div_mul_cancel₀ _ (Complex.ofReal_ne_zero.mpr h)

theorem contourPhase_features (N m₁ m₂ : ℕ) (u θ : ℝ) (p q : ℂ[X]) :
    contourPhase N m₁ m₂ u θ*contourFeature N m₁ m₂ u p θ*contourFeature N m₁ m₂ u q θ=
      contourComplexDensity N m₁ m₂ u θ*p.eval (circleMap 0 (u^2) θ)*q.eval (circleMap 0 (u^2) θ) := by
  have hs : (Real.sqrt (contourPositiveDensity N m₁ m₂ u θ):ℂ)^2=
      (contourPositiveDensity N m₁ m₂ u θ:ℂ) := by
    norm_cast
    exact Real.sq_sqrt (contourPositiveDensity_nonneg N m₁ m₂ u θ)
  unfold contourFeature
  calc
    _ = (contourPhase N m₁ m₂ u θ*(Real.sqrt (contourPositiveDensity N m₁ m₂ u θ):ℂ)^2)*
        p.eval (circleMap 0 (u^2) θ)*q.eval (circleMap 0 (u^2) θ) := by ring
    _ = _ := by rw [hs,contourPhase_mul_density]

theorem contourFeature_continuous (N m₁ m₂ : ℕ) (hN : 0 < N)
    {u : ℝ} (hu : 1 < u) (p : ℂ[X]) : Continuous (contourFeature N m₁ m₂ u p) := by
  unfold contourFeature
  have hd := (contourPositiveDensity_continuous N m₁ m₂ hN hu).sqrt
  exact (Complex.continuous_ofReal.comp hd).mul (p.continuous.comp (continuous_circleMap _ _))

theorem contourPhase_aestronglyMeasurable (N m₁ m₂ : ℕ) (hN : 0 < N)
    {u : ℝ} (hu : 1 < u) :
    AEStronglyMeasurable (contourPhase N m₁ m₂ u) contourAngularMeasure := by
  unfold contourPhase
  exact ((contourComplexDensity_continuous N m₁ m₂ hN hu).measurable.div
    (Complex.continuous_ofReal.comp (contourPositiveDensity_continuous N m₁ m₂ hN hu)).measurable).aestronglyMeasurable

theorem contourFeature_memLp (N m₁ m₂ : ℕ) (hN : 0 < N)
    {u : ℝ} (hu : 1 < u) (p : ℂ[X]) :
    MemLp (contourFeature N m₁ m₂ u p) 2 contourAngularMeasure := by
  have hc := contourFeature_continuous N m₁ m₂ hN hu p
  obtain ⟨C,hC⟩ := isCompact_Icc.exists_bound_of_continuousOn
    (hc.continuousOn : ContinuousOn (contourFeature N m₁ m₂ u p) (Icc 0 (2*Real.pi)))
  haveI : IsFiniteMeasure contourAngularMeasure := by unfold contourAngularMeasure; infer_instance
  apply MemLp.of_bound hc.aestronglyMeasurable C
  filter_upwards [self_mem_ae_restrict measurableSet_Ioc] with θ hθ
  exact hC θ ⟨hθ.1.le,hθ.2⟩

/-- Exact phase-integral representation, already in the measure used by the Gram majorant. -/
theorem complexWindowCoefficient_phase_integral (N m₁ m₂ : ℕ) (p q : ℂ[X])
    (u : ℝ) (hN : 0 < N) (hu : 1 < u) :
    complexWindowCoefficient N m₁ m₂ p q=
      ∫ θ, contourPhase N m₁ m₂ u θ*contourFeature N m₁ m₂ u p θ*
        contourFeature N m₁ m₂ u q θ ∂contourAngularMeasure := by
  rw [complexWindowCoefficient_angular N m₁ m₂ p q u hN hu,
    intervalIntegral.integral_of_le (by positivity : (0:ℝ)≤2*Real.pi)]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall (fun θ => (contourPhase_features N m₁ m₂ u θ p q).symm)

theorem contourFeature_norm_sq (N m₁ m₂ : ℕ) (u θ : ℝ) (p : ℂ[X]) :
    ‖contourFeature N m₁ m₂ u p θ‖^2=contourPositiveDensity N m₁ m₂ u θ*
      ‖p.eval (circleMap 0 (u^2) θ)‖^2 := by
  unfold contourFeature
  rw [norm_mul,mul_pow,Complex.norm_real,Real.norm_eq_abs,
    abs_of_nonneg (Real.sqrt_nonneg _),Real.sq_sqrt (contourPositiveDensity_nonneg N m₁ m₂ u θ)]

theorem contourSquaredNorm_integral (N m₁ m₂ : ℕ) (u : ℝ) (p : ℂ[X]) :
    contourSquaredNorm N m₁ m₂ u p=
      ∫ θ in 0..2*Real.pi, contourPositiveDensity N m₁ m₂ u θ*
        ‖p.eval (circleMap 0 (u^2) θ)‖^2 := by
  unfold contourSquaredNorm contourAngularMeasure
  rw [intervalIntegral.integral_of_le (by positivity : (0:ℝ)≤2*Real.pi)]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall (fun θ => contourFeature_norm_sq N m₁ m₂ u θ p)

theorem complexWindowCoefficient_norm_le (N m₁ m₂ : ℕ) (p q : ℂ[X])
    (u : ℝ) (hN : 0 < N) (hu : 1 < u) :
    ‖complexWindowCoefficient N m₁ m₂ p q‖≤
      Real.sqrt (contourSquaredNorm N m₁ m₂ u p)*Real.sqrt (contourSquaredNorm N m₁ m₂ u q) := by
  rw [complexWindowCoefficient_phase_integral N m₁ m₂ p q u hN hu]
  exact norm_integral_phase_mul_le (contourPhase_aestronglyMeasurable N m₁ m₂ hN hu)
    (Filter.Eventually.of_forall (fun θ => contourPhase_norm_le_one N m₁ m₂ u θ))
    (contourFeature_memLp N m₁ m₂ hN hu p) (contourFeature_memLp N m₁ m₂ hN hu q)

def complexWindowMatrix {ι : Type*} (N m₁ m₂ : ℕ) (p : ι → ℂ[X]) : Matrix ι ι ℂ :=
  fun i j => complexWindowCoefficient N m₁ m₂ (p i) (p j)

theorem complexWindowCoefficient_response_majorant {ι : Type*} [Fintype ι] [DecidableEq ι]
    (N m₁ m₂ : ℕ) (p : ι → ℂ[X]) (u : ℝ) (hN : 0 < N) (hu : 1 < u) (h : ℂ) :
    ‖(1+h • complexWindowMatrix N m₁ m₂ p).det‖≤
      (Nat.factorial (Fintype.card ι):ℝ)*
        ∏ i,(1+‖h‖*contourSquaredNorm N m₁ m₂ u (p i)) := by
  apply determinant_response_majorant
  · intro i
    unfold contourSquaredNorm
    exact integral_nonneg (fun θ => sq_nonneg _)
  · intro i j
    exact complexWindowCoefficient_norm_le N m₁ m₂ (p i) (p j) u hN hu

end Zeta3.Analysis

import Zeta3.Analysis.ContourNorm
import Zeta3.Analysis.ContourNormIntegral
import Mathlib.LinearAlgebra.BilinearForm.Basic

/-! # The actual positive contour and physical bilinear forms -/

noncomputable section
open Set MeasureTheory Polynomial
namespace Zeta3.Analysis

def positiveContourKernel (N m₁ m₂ : ℕ) (u : ℝ) (p q : ℝ[X]) (θ : ℝ) : ℝ :=
  normalizedContourPositiveDensity N m₁ m₂ u θ*
    ((p.eval₂ Complex.ofRealHom (circleMap 0 (u^2) θ)).re*
       (q.eval₂ Complex.ofRealHom (circleMap 0 (u^2) θ)).re+
     (p.eval₂ Complex.ofRealHom (circleMap 0 (u^2) θ)).im*
       (q.eval₂ Complex.ofRealHom (circleMap 0 (u^2) θ)).im)

def positiveContourPair (N m₁ m₂ : ℕ) (u : ℝ) (p q : ℝ[X]) : ℝ :=
  ∫ θ in 0..2*Real.pi, positiveContourKernel N m₁ m₂ u p q θ

theorem positiveContourKernel_continuous (N m₁ m₂ : ℕ) (hN : 0 < N)
    {u : ℝ} (hu : 1 < u) (p q : ℝ[X]) : Continuous (positiveContourKernel N m₁ m₂ u p q) := by
  have hp := (p.continuous_eval₂ Complex.ofRealHom).comp (continuous_circleMap 0 (u^2))
  have hq := (q.continuous_eval₂ Complex.ofRealHom).comp (continuous_circleMap 0 (u^2))
  exact (normalizedContourPositiveDensity_continuous N m₁ m₂ hN hu).mul
    (((Complex.continuous_re.comp hp).mul (Complex.continuous_re.comp hq)).add
      ((Complex.continuous_im.comp hp).mul (Complex.continuous_im.comp hq)))

theorem positiveContourKernel_add_left (N m₁ m₂ : ℕ) (u θ : ℝ) (p q r : ℝ[X]) :
    positiveContourKernel N m₁ m₂ u (p+q) r θ=
      positiveContourKernel N m₁ m₂ u p r θ+positiveContourKernel N m₁ m₂ u q r θ := by
  simp only [positiveContourKernel,eval₂_add,Complex.add_re,Complex.add_im]
  ring

theorem positiveContourKernel_smul_left (N m₁ m₂ : ℕ) (u θ a : ℝ) (p q : ℝ[X]) :
    positiveContourKernel N m₁ m₂ u (a • p) q θ=a*positiveContourKernel N m₁ m₂ u p q θ := by
  simp only [positiveContourKernel,Polynomial.smul_eq_C_mul,eval₂_mul,eval₂_C,
    show Complex.ofRealHom a=(a:ℂ) from rfl,Complex.mul_re,Complex.mul_im,Complex.ofReal_re,Complex.ofReal_im]
  ring

theorem positiveContourPair_symm (N m₁ m₂ : ℕ) (u : ℝ) (p q : ℝ[X]) :
    positiveContourPair N m₁ m₂ u p q=positiveContourPair N m₁ m₂ u q p := by
  unfold positiveContourPair
  congr 1
  funext θ
  unfold positiveContourKernel
  ring

theorem positiveContourPair_add_left (N m₁ m₂ : ℕ) (hN : 0 < N)
    {u : ℝ} (hu : 1 < u) (p q r : ℝ[X]) :
    positiveContourPair N m₁ m₂ u (p+q) r=
      positiveContourPair N m₁ m₂ u p r+positiveContourPair N m₁ m₂ u q r := by
  unfold positiveContourPair
  simp_rw [positiveContourKernel_add_left]
  exact intervalIntegral.integral_add
    ((positiveContourKernel_continuous N m₁ m₂ hN hu p r).intervalIntegrable _ _)
    ((positiveContourKernel_continuous N m₁ m₂ hN hu q r).intervalIntegrable _ _)

theorem positiveContourPair_smul_left (N m₁ m₂ : ℕ) (u a : ℝ) (p q : ℝ[X]) :
    positiveContourPair N m₁ m₂ u (a • p) q=a*positiveContourPair N m₁ m₂ u p q := by
  unfold positiveContourPair
  simp_rw [positiveContourKernel_smul_left]
  exact intervalIntegral.integral_const_mul _ _

def positiveContourBilinForm (N m₁ m₂ : ℕ) (hN : 0 < N) (u : ℝ) (hu : 1 < u) :
    LinearMap.BilinForm ℝ ℝ[X] where
  toFun p :=
    { toFun := positiveContourPair N m₁ m₂ u p
      map_add' := by
        intro q r
        rw [positiveContourPair_symm N m₁ m₂ u p (q+r),positiveContourPair_add_left N m₁ m₂ hN hu]
        rw [positiveContourPair_symm N m₁ m₂ u q p,positiveContourPair_symm N m₁ m₂ u r p]
      map_smul' := by
        intro a q
        simp only [RingHom.id_apply,smul_eq_mul]
        rw [positiveContourPair_symm N m₁ m₂ u p (a • q),positiveContourPair_smul_left,
          positiveContourPair_symm N m₁ m₂ u q p] }
  map_add' := by
    intro p q
    apply LinearMap.ext
    intro r
    exact positiveContourPair_add_left N m₁ m₂ hN hu p q r
  map_smul' := by
    intro a p
    apply LinearMap.ext
    intro q
    exact positiveContourPair_smul_left N m₁ m₂ u a p q

theorem positiveContourPair_self (N m₁ m₂ : ℕ) (u : ℝ) (p : ℝ[X]) :
    positiveContourPair N m₁ m₂ u p p=positiveContourNorm N m₁ m₂ u p := by
  rw [positiveContourNorm_integral]
  unfold positiveContourPair
  apply intervalIntegral.integral_congr
  intro θ hθ
  dsimp only
  unfold positiveContourKernel
  rw [Complex.sq_norm,Complex.normSq_apply]

def normalizedPhysicalPair (N m₁ m₂ : ℕ) (p q : ℝ[X]) : ℝ :=
  PhysicalMeasure.windowMomentFunctional N m₁ m₂
    (physicalRescalePolynomial N p*physicalRescalePolynomial N q)/physicalWeightScale N m₁ m₂

theorem normalizedPhysicalPair_symm (N m₁ m₂ : ℕ) (p q : ℝ[X]) :
    normalizedPhysicalPair N m₁ m₂ p q=normalizedPhysicalPair N m₁ m₂ q p := by
  unfold normalizedPhysicalPair
  rw [mul_comm]

theorem physicalRescalePolynomial_add (N : ℕ) (p q : ℝ[X]) :
    physicalRescalePolynomial N (p+q)=physicalRescalePolynomial N p+physicalRescalePolynomial N q := by
  simp [physicalRescalePolynomial,add_comp]

theorem physicalRescalePolynomial_smul (N : ℕ) (a : ℝ) (p : ℝ[X]) :
    physicalRescalePolynomial N (a • p)=a • physicalRescalePolynomial N p := by
  simp [physicalRescalePolynomial,Polynomial.smul_eq_C_mul,mul_comp]

theorem normalizedPhysicalPair_add_left (N m₁ m₂ : ℕ) (p q r : ℝ[X]) :
    normalizedPhysicalPair N m₁ m₂ (p+q) r=
      normalizedPhysicalPair N m₁ m₂ p r+normalizedPhysicalPair N m₁ m₂ q r := by
  simp [normalizedPhysicalPair,physicalRescalePolynomial_add,add_mul,map_add,add_div]

theorem normalizedPhysicalPair_smul_left (N m₁ m₂ : ℕ) (a : ℝ) (p q : ℝ[X]) :
    normalizedPhysicalPair N m₁ m₂ (a • p) q=a*normalizedPhysicalPair N m₁ m₂ p q := by
  simp [normalizedPhysicalPair,physicalRescalePolynomial_smul,smul_mul_assoc,map_smul,smul_eq_mul,mul_div_assoc]

def normalizedPhysicalBilinForm (N m₁ m₂ : ℕ) : LinearMap.BilinForm ℝ ℝ[X] where
  toFun p :=
    { toFun := normalizedPhysicalPair N m₁ m₂ p
      map_add' := by
        intro q r
        rw [normalizedPhysicalPair_symm N m₁ m₂ p (q+r),normalizedPhysicalPair_add_left]
        rw [normalizedPhysicalPair_symm N m₁ m₂ q p,normalizedPhysicalPair_symm N m₁ m₂ r p]
      map_smul' := by
        intro a q
        simp only [RingHom.id_apply,smul_eq_mul]
        rw [normalizedPhysicalPair_symm N m₁ m₂ p (a • q),normalizedPhysicalPair_smul_left,
          normalizedPhysicalPair_symm N m₁ m₂ q p] }
  map_add' := by
    intro p q
    apply LinearMap.ext
    intro r
    exact normalizedPhysicalPair_add_left N m₁ m₂ p q r
  map_smul' := by
    intro a p
    apply LinearMap.ext
    intro q
    exact normalizedPhysicalPair_smul_left N m₁ m₂ a p q

theorem normalizedPhysicalPair_self (N m₁ m₂ : ℕ) (p : ℝ[X]) :
    normalizedPhysicalPair N m₁ m₂ p p=normalizedPhysicalNorm N m₁ m₂ p := by
  simp only [normalizedPhysicalPair,normalizedPhysicalNorm,windowSquaredNorm,pow_two]

theorem physicalRescalePolynomial_ne_zero (N : ℕ) (hN : 0 < N) {p : ℝ[X]} (hp : p≠0) :
    physicalRescalePolynomial N p≠0 := by
  have hNr : (N:ℝ)≠0 := by exact_mod_cast hN.ne'
  have hr : (((N:ℝ)^2)⁻¹) ∈ nonZeroDivisors ℝ := by
    rw [mem_nonZeroDivisors_iff_ne_zero]
    exact inv_ne_zero (pow_ne_zero _ hNr)
  exact (Polynomial.comp_C_mul_X_eq_zero_iff hr).not.mpr hp

theorem normalizedPhysicalNorm_pos (N m₁ m₂ : ℕ) (hN : 0 < N) {p : ℝ[X]} (hp : p≠0) :
    0 < normalizedPhysicalNorm N m₁ m₂ p := by
  unfold normalizedPhysicalNorm windowSquaredNorm
  exact div_pos (PhysicalMeasure.windowMomentFunctional_square_pos N m₁ m₂ _
    (physicalRescalePolynomial_ne_zero N hN hp)) (physicalWeightScale_pos hN m₁ m₂)

end Zeta3.Analysis

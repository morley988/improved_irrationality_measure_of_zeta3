import Zeta3.Analysis.ContourBilinear
import Zeta3.Analysis.ConcreteResponse
import Zeta5.Analysis.GramBound

/-!
# Exact real coefficient forms and the original Hankel matrix

The residue coefficient is extended linearly to real polynomials and then
identified with both the complex contour form and the actual rational
Hankel coefficient matrix.  This supplies the algebraic basis-change bridge.
-/

noncomputable section
open Polynomial Matrix
open scoped BigOperators
namespace Zeta3.Analysis

def realSquarePole (i : ℕ) : ℝ := (Zeta5.Construction.pole (i+1):ℚ)

def realNumeratorLinearMap (N : ℕ) : ℝ[X] →ₗ[ℝ] ℝ where
  toFun P := ∑ i ∈ Finset.range N,
    P.eval (realSquarePole i)/(PhysicalMeasure.realDenominator N).derivative.eval (realSquarePole i)*
      ((i+1:ℕ):ℝ)^2
  map_add' := by
    intro P Q
    simp [eval_add,add_div,add_mul,Finset.sum_add_distrib]
  map_smul' := by
    intro a P
    simp [Polynomial.smul_eq_C_mul,eval_mul,eval_C,smul_eq_mul,
      div_eq_mul_inv,mul_assoc,Finset.mul_sum]

def realWindowLinearFunctional (N m₁ m₂ : ℕ) : ℝ[X] →ₗ[ℝ] ℝ :=
  (realNumeratorLinearMap N).comp (LinearMap.mulLeft ℝ
    (PhysicalMeasure.realPositiveFactor m₁*PhysicalMeasure.realPositiveFactor m₂))

def realWindowCoefficientPair (N m₁ m₂ : ℕ) (p q : ℝ[X]) : ℝ :=
  realWindowLinearFunctional N m₁ m₂ (physicalRescalePolynomial N p*physicalRescalePolynomial N q)/
    physicalWeightScale N m₁ m₂

theorem complexSquarePole_eq_ofReal (i:ℕ) : complexSquarePole i=(realSquarePole i:ℂ) := by
  simp [complexSquarePole,realSquarePole]

theorem complexDenominator_eq_map_real (N:ℕ) :
    complexDenominator N=(PhysicalMeasure.realDenominator N).map Complex.ofRealHom := by
  unfold complexDenominator PhysicalMeasure.realDenominator
  rw [Polynomial.map_map]
  congr 1

theorem complexNumeratorLinear_map_real (N:ℕ) (P:ℝ[X]) :
    complexNumeratorLinear N (P.map Complex.ofRealHom)=(realNumeratorLinearMap N P:ℂ) := by
  unfold complexNumeratorLinear
  simp only [realNumeratorLinearMap,LinearMap.coe_mk,AddHom.coe_mk]
  push_cast
  apply Finset.sum_congr rfl
  intro i hi
  rw [complexDenominator_eq_map_real,Polynomial.derivative_map,complexSquarePole_eq_ofReal]
  have he (Q:ℝ[X]) : (Q.map Complex.ofRealHom).eval (realSquarePole i:ℂ)=Complex.ofReal (Q.eval (realSquarePole i)) :=
    by simpa only [Complex.ofRealHom_eq_coe] using (Polynomial.eval_map_apply (p:=Q) Complex.ofRealHom (realSquarePole i))
  rw [he,he]

theorem realNumeratorLinearMap_rat (N:ℕ) (P:ℚ[X]) :
    realNumeratorLinearMap N (P.map (Rat.castHom ℝ))=(Zeta3.Construction.numeratorLinear N P:ℝ) := by
  change (∑ i ∈ Finset.range N,
    (P.map (Rat.castHom ℝ)).eval (realSquarePole i)/
      (PhysicalMeasure.realDenominator N).derivative.eval (realSquarePole i)*((i+1:ℕ):ℝ)^2)=_
  unfold Zeta3.Construction.numeratorLinear
  push_cast
  apply Finset.sum_congr rfl
  intro i hi
  simp only [PhysicalMeasure.realDenominator,Polynomial.derivative_map,realSquarePole,
    ← Rat.coe_castHom (α:=ℝ),eval_map_apply]

theorem realPositiveFactor_map_complex (m:ℕ) :
    (PhysicalMeasure.realPositiveFactor m).map Complex.ofRealHom=
      (Zeta3.Construction.positiveFactor m).map (Rat.castHom ℂ) := by
  unfold PhysicalMeasure.realPositiveFactor
  rw [Polynomial.map_map]
  congr 1

theorem physicalRescalePolynomial_map_complex (N:ℕ) (p:ℝ[X]) :
    (physicalRescalePolynomial N p).map Complex.ofRealHom=
      complexRescalePolynomial N (p.map Complex.ofRealHom) := by
  simp [physicalRescalePolynomial,complexRescalePolynomial,Polynomial.map_comp,Polynomial.map_mul]

theorem normalizedComplexWindowCoefficient_real (N m₁ m₂:ℕ) (p q:ℝ[X]) :
    normalizedComplexWindowCoefficient N m₁ m₂ (p.map Complex.ofRealHom) (q.map Complex.ofRealHom)=
      (realWindowCoefficientPair N m₁ m₂ p q:ℂ) := by
  unfold normalizedComplexWindowCoefficient complexWindowCoefficient realWindowCoefficientPair
  have he : ((PhysicalMeasure.realPositiveFactor m₁*PhysicalMeasure.realPositiveFactor m₂)*
      (physicalRescalePolynomial N p*physicalRescalePolynomial N q)).map Complex.ofRealHom=
      (Zeta3.Construction.positiveFactor m₁).map (Rat.castHom ℂ)*
      (Zeta3.Construction.positiveFactor m₂).map (Rat.castHom ℂ)*
      complexRescalePolynomial N (p.map Complex.ofRealHom)*complexRescalePolynomial N (q.map Complex.ofRealHom) := by
    simp only [Polynomial.map_mul,realPositiveFactor_map_complex,physicalRescalePolynomial_map_complex]
    ring
  rw [← he,complexNumeratorLinear_map_real]
  unfold realWindowLinearFunctional
  simp only [LinearMap.comp_apply,LinearMap.mulLeft_apply,Complex.ofReal_div]

theorem realHankelLinear_eq_windowMonomialGram (n:ℕ) :
    Zeta3.Transfer.realHankelLinear n=
      Zeta5.Analysis.realMonomialGram (realWindowLinearFunctional (50*n) (4*n) (16*n)) (51*n) := by
  ext i j
  change (Zeta3.Construction.numeratorLinear (50*n)
    (Zeta3.Construction.positiveFactor (4*n)*Zeta3.Construction.positiveFactor (16*n)*X^(i.val+j.val)):ℝ)=_
  rw [← realNumeratorLinearMap_rat]
  simp only [Zeta5.Analysis.realMonomialGram,Zeta5.Analysis.polynomialGram,realWindowLinearFunctional,
    LinearMap.comp_apply,LinearMap.mulLeft_apply,Polynomial.map_mul,Polynomial.map_pow,Polynomial.map_X,
    PhysicalMeasure.realPositiveFactor,pow_add]

theorem complexHankelLinear_eq_real_map (n:ℕ) :
    complexHankelLinear n=(Zeta3.Transfer.realHankelLinear n).map Complex.ofRealHom := by
  ext i j
  simp [complexHankelLinear,Zeta3.Transfer.realHankelLinear]

theorem realWindowCoefficientPair_congruence (N m₁ m₂ r:ℕ) (p:Fin r→ℝ[X])
    (hp:∀i,(physicalRescalePolynomial N (p i)).natDegree<r) :
    (fun i j => realWindowCoefficientPair N m₁ m₂ (p i) (p j) : Matrix (Fin r) (Fin r) ℝ)=
      (physicalWeightScale N m₁ m₂)⁻¹ •
      ((Zeta5.Analysis.realCoefficientMatrix r (fun i => physicalRescalePolynomial N (p i))).transpose*
        Zeta5.Analysis.realMonomialGram (realWindowLinearFunctional N m₁ m₂) r*
        Zeta5.Analysis.realCoefficientMatrix r (fun i => physicalRescalePolynomial N (p i))) := by
  rw [← Zeta5.Analysis.real_polynomialGram_change_of_basis _ _ _ hp]
  ext i j
  simp only [realWindowCoefficientPair,Zeta5.Analysis.polynomialGram,Matrix.smul_apply,smul_eq_mul]
  ring

theorem normalizedPhysicalPair_congruence (N m₁ m₂ r:ℕ) (p:Fin r→ℝ[X])
    (hp:∀i,(physicalRescalePolynomial N (p i)).natDegree<r) :
    (fun i j => normalizedPhysicalPair N m₁ m₂ (p i) (p j) : Matrix (Fin r) (Fin r) ℝ)=
      (physicalWeightScale N m₁ m₂)⁻¹ •
      ((Zeta5.Analysis.realCoefficientMatrix r (fun i => physicalRescalePolynomial N (p i))).transpose*
        Zeta5.Analysis.realMonomialGram (PhysicalMeasure.windowMomentFunctional N m₁ m₂) r*
        Zeta5.Analysis.realCoefficientMatrix r (fun i => physicalRescalePolynomial N (p i))) := by
  rw [← Zeta5.Analysis.real_polynomialGram_change_of_basis _ _ _ hp]
  ext i j
  simp only [normalizedPhysicalPair,Zeta5.Analysis.polynomialGram,Matrix.smul_apply,smul_eq_mul]
  ring

end Zeta3.Analysis

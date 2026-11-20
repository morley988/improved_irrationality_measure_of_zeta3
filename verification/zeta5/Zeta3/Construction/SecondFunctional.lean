import Zeta3.Construction.SecondDimensions
import Zeta3.Arithmetic.SecondAssembly

/-! The actual physical cubic functional is linear, and its required
finite-degree coefficients are integral at the good primes. -/
noncomputable section
namespace Zeta3.Construction.Features
open Polynomial Finset Zeta5.Arithmetic Zeta5.Construction Zeta3.Arithmetic OddZeta.FourValue

/-- The rational functional from the actual signed physical nodes. -/
def physicalLocalCubicFunctionalMap (N p c : ℕ) [Fact p.Prime] : ℚ[X] →ₗ[ℚ] ℚ :=
  (∑ a∈physicalLevels N p c,
    (((physicalLocalMonic N p c).derivative.eval (a:ℚ))⁻¹ * harmonicLevel a) •
      Polynomial.leval (a:ℚ)) +
    (1/2:ℚ) • bernoulliFunctional.comp
      (Polynomial.derivative.comp (monicQuotientMap (physicalLocalMonic N p c)
        (physicalLocalMonic_monic N (c:ℤ))))

@[simp] theorem physicalLocalCubicFunctionalMap_apply (N p c : ℕ) [Fact p.Prime] (P : ℚ[X]) :
    physicalLocalCubicFunctionalMap N p c P=physicalLocalCubicFunctional N p c P := by
  simp only [physicalLocalCubicFunctionalMap,LinearMap.add_apply,LinearMap.sum_apply,
    LinearMap.smul_apply,LinearMap.comp_apply,monicQuotientMap_apply,
    Polynomial.leval_apply,smul_eq_mul,physicalLocalCubicFunctional,nodeCubicFunctional]
  congr 1
  apply sum_congr rfl
  intro a ha
  ring

variable {p : ℕ} [Fact p.Prime]

theorem bernoulli_derivative_integral_of_degree {P : ℚ[X]}
    (hp : 2<p) (hP : PolynomialPadicLower p 0 P) (hdeg : P.natDegree≤p-1) :
    PadicLower p 0 (bernoulliFunctional P.derivative) := by
  rw [bernoulliFunctional_derivative_eq_sum]
  apply padicLower_sum
  intro j hj
  have hjp : j-1<p-1 := by have := mem_range.mp hj;omega
  simpa only [zero_add] using ((hP j).mul (padicLower_nat j)).mul
    (bernoulli_integral_of_lt (p:=p) (j-1) hp hjp)

theorem physicalLocalCubicFunctional_integral {N c : ℕ} {P : ℚ[X]}
    (hp : 2<p) (hc : 0<c) (hcp : 2*c<p) (hsmall : 2*N<p^2)
    (hP : PolynomialPadicLower p 0 P)
    (hdeg : P.natDegree≤(physicalLocalMonic N p c).natDegree+(p-1)) :
    PadicLower p 0 (physicalLocalCubicFunctional N p c P) := by
  rw [physicalLocalCubicFunctional_eq_signed]
  apply PadicLower.add
  · apply padicLower_sum
    intro i hi
    have hH : PadicLower p 0 (harmonicLevel (physicalLocalLevel p c i)) := by
      rw [harmonicLevel_physical hc (by omega) hi]
      apply harmonicThree_integral
      have hiN := i.1.isLt
      apply (Nat.div_lt_iff_lt_mul (Fact.out:p.Prime).pos).mpr
      nlinarith
    simpa only [zero_add] using
      ((hP.eval_integral (padicLower_int _)).mul
        (physicalLocalMonic_derivative_inverse_integral hsmall hi)).mul hH
  · have hL := physicalLocalMonic_monic (p:=p) N (c:ℤ)
    have hQ : PolynomialPadicLower p 0 (P / physicalLocalMonic N p c) := by
      rw [← divByMonic_eq_div _ hL]
      exact polynomialPadicLower_divByMonic hP (physicalLocalMonic_integral N _) hL
    have hQdeg : (P / physicalLocalMonic N p c).natDegree≤p-1 := by
      rw [← divByMonic_eq_div _ hL,natDegree_divByMonic _ hL]
      omega
    simpa only [zero_add] using (half_integral hp).mul
      (bernoulli_derivative_integral_of_degree hp hQ hQdeg)

/-- Coefficient reduction gives a linear functional on the finite degree
range actually required by the two windows. Its extension outside that
range is defined to be zero. -/
def residuePhysicalFunctional (N c d : ℕ) (hp : 2<p) (hc : 0<c) (hcp : 2*c<p)
    (hsmall : 2*N<p^2) (hd : d≤(physicalLocalMonic N p c).natDegree+(p-1)) :
    (PadicResidueField p)[X] →ₗ[PadicResidueField p] PadicResidueField p :=
  Polynomial.lsum (fun j => LinearMap.mulRight (PadicResidueField p)
    (if hj : j≤d then padicReduction p
      ⟨physicalLocalCubicFunctional N p c (X^j),
        physicalLocalCubicFunctional_integral hp hc hcp hsmall
          (polynomialPadicLower_X.pow j) (by rw [natDegree_X_pow];omega)⟩ else 0))

@[simp] theorem residuePhysicalFunctional_monomial (N c d : ℕ)
    (hp : 2<p) (hc : 0<c) (hcp : 2*c<p) (hsmall : 2*N<p^2)
    (hd : d≤(physicalLocalMonic N p c).natDegree+(p-1)) (j : ℕ)
    (a : PadicResidueField p) :
    residuePhysicalFunctional N c d hp hc hcp hsmall hd (monomial j a)=
      a*(if hj : j≤d then padicReduction p
      ⟨physicalLocalCubicFunctional N p c (X^j),
        physicalLocalCubicFunctional_integral hp hc hcp hsmall
          (polynomialPadicLower_X.pow j) (by rw [natDegree_X_pow];omega)⟩ else 0) := by
  simp [residuePhysicalFunctional,Polynomial.lsum_apply,Polynomial.sum_monomial_index]

end Zeta3.Construction.Features

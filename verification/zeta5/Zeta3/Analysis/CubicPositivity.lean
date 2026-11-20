import Zeta3.Analysis.CubicStieltjes
import Zeta3.Construction.Asymmetric
import Zeta3.Transfer.ConcreteMultiplicity
import Mathlib.Algebra.Polynomial.Basis

/-!
# Positive definiteness of the actual cubic Hankel pencil

The unequal factorial windows are first converted to their common positive
weight. The real matrix at ζ(3) is then exactly a Gram matrix for integration
against a strictly positive density. Thus positive definiteness and
nonvanishing are proved for the concrete family, including its empty stage.
-/

noncomputable section
namespace Zeta3.Analysis.PhysicalMeasure
open Real Set MeasureTheory Filter Polynomial Zeta3.Construction
open scoped Topology BigOperators

def realPositiveFactor (m : ℕ) : ℝ[X] :=
  (positiveFactor m).map (Rat.castHom ℝ)

theorem realPositiveFactor_eval_pos (m : ℕ) {t : ℝ} (ht : 0 < t) :
    0 < (realPositiveFactor m).eval t := by
  simp only [realPositiveFactor, positiveFactor, Polynomial.map_prod, Polynomial.map_add,
    Polynomial.map_X, Polynomial.map_C, eval_prod, eval_add, eval_X, eval_C,
    Rat.coe_castHom, Rat.cast_pow, Rat.cast_natCast]
  exact Finset.prod_pos (fun a _ => add_pos_of_pos_of_nonneg ht (sq_nonneg _))

def windowMomentFunctional (N m₁ m₂ : ℕ) : ℝ[X] →ₗ[ℝ] ℝ :=
  (momentFunctional N).comp
    (LinearMap.mulLeft ℝ (realPositiveFactor m₁ * realPositiveFactor m₂))

theorem windowMomentFunctional_square_pos (N m₁ m₂ : ℕ) (p : ℝ[X]) (hp : p ≠ 0) :
    0 < windowMomentFunctional N m₁ m₂ (p ^ 2) := by
  let q := realPositiveFactor m₁ * realPositiveFactor m₂ * p ^ 2
  have hpos : ∀ᵐ x ∂volume.restrict (Ioi (0 : ℝ)),
      0 < q.eval (x ^ 2) * weightedDensity N x := by
    filter_upwards [self_mem_ae_restrict measurableSet_Ioi,
      ae_restrict_of_ae (polynomial_square_argument_ne_zero_ae p hp)] with x hx hp'
    simp only [q, eval_mul, eval_pow]
    exact mul_pos (mul_pos (mul_pos
      (realPositiveFactor_eval_pos m₁ (sq_pos_of_pos hx))
      (realPositiveFactor_eval_pos m₂ (sq_pos_of_pos hx)))
      (sq_pos_of_ne_zero hp')) (weightedDensity_pos N hx)
  have hn : 0 ≤ᵐ[volume.restrict (Ioi (0 : ℝ))]
      (fun x => q.eval (x ^ 2) * weightedDensity N x) := hpos.mono (fun _ h => h.le)
  have hi := weighted_polynomial_integrable N q
  change 0 < momentFunctional N q
  have hnonneg : 0 ≤ momentFunctional N q := integral_nonneg_of_ae hn
  apply lt_of_le_of_ne hnonneg
  intro hz
  have hzero := (integral_eq_zero_iff_of_nonneg_ae hn hi).mp hz.symm
  have hfalse : ∀ᵐ x ∂volume.restrict (Ioi (0 : ℝ)), False := by
    filter_upwards [hpos, hzero] with x hx hz'
    exact (ne_of_gt hx) hz'
  have hvol : volume (Ioi (0 : ℝ)) ≠ 0 := by simp
  haveI : (ae (volume.restrict (Ioi (0 : ℝ)))).NeBot := (ae_restrict_neBot).mpr hvol
  obtain ⟨_, hx⟩ := Filter.Eventually.exists hfalse
  exact hx

theorem monomials_fin_linearIndependent (r : ℕ) :
    LinearIndependent ℝ (fun j : Fin r => (X : ℝ[X]) ^ j.val) := by
  have h := (Polynomial.basisMonomials ℝ).linearIndependent.comp
    (fun j : Fin r => j.val) Fin.val_injective
  simpa only [Polynomial.coe_basisMonomials, Function.comp_def, X_pow_eq_monomial] using h

theorem realHankel_eq_physicalGram (n : ℕ) :
    Zeta3.Transfer.realHankelConstant n + (Zeta5.Endpoint.realZeta 3) •
      Zeta3.Transfer.realHankelLinear n =
        Zeta5.Analysis.polynomialGram (windowMomentFunctional (50 * n) (4 * n) (16 * n))
          (fun j : Fin (51 * n) => (X : ℝ[X]) ^ j.val) := by
  ext i j
  have h := momentFunctional_eq_numeratorFunctional_realZetaThree (50 * n)
    (positiveFactor (4 * n) * positiveFactor (16 * n) * X ^ (i.val + j.val))
  rw [numeratorFunctional_affine] at h
  simp only [eval₂_add, eval₂_C, eval₂_mul, eval₂_X, Rat.coe_castHom,
    Polynomial.map_mul, Polynomial.map_pow, Polynomial.map_X] at h
  change (numeratorConstant (50 * n)
    (positiveFactor (4 * n) * positiveFactor (16 * n) * X ^ (i.val + j.val)) : ℝ) +
    Zeta5.Endpoint.realZeta 3 * (numeratorLinear (50 * n)
    (positiveFactor (4 * n) * positiveFactor (16 * n) * X ^ (i.val + j.val)) : ℝ) = _
  rw [← h]
  simp only [Zeta5.Analysis.polynomialGram, windowMomentFunctional,
    LinearMap.comp_apply, LinearMap.mulLeft_apply, realPositiveFactor, pow_add]

/-- The full physical positive-definiteness input for the actual polynomial
family, with the ζ(3) identity already discharged. -/
theorem realHankel_realZetaThree_posDef (n : ℕ) :
    (Zeta3.Transfer.realHankelConstant n + (Zeta5.Endpoint.realZeta 3) •
      Zeta3.Transfer.realHankelLinear n).PosDef := by
  rw [realHankel_eq_physicalGram]
  exact Zeta5.Analysis.polynomialGram_posDef _
    (windowMomentFunctional_square_pos (50 * n) (4 * n) (16 * n)) _
    (monomials_fin_linearIndependent (51 * n))

theorem windowIntegerPolynomial_ne_zero (n : ℕ) : windowIntegerPolynomial n ≠ 0 :=
  Zeta3.Transfer.windowIntegerPolynomial_ne_zero_of_hankel_posDef n
    (Zeta5.Endpoint.realZeta 3) (realHankel_realZetaThree_posDef n)

theorem windowIntegerPolynomial_eval_realZetaThree_pos (n : ℕ) :
    ((windowIntegerPolynomial n).map (Int.castRingHom ℝ)).eval (Zeta5.Endpoint.realZeta 3) > 0 := by
  rw [Zeta3.Transfer.windowIntegerPolynomial_eval_eq_hankel_det]
  exact mul_pos (Zeta3.Transfer.integerHankelScale_pos n)
    (realHankel_realZetaThree_posDef n).det_pos

end Zeta3.Analysis.PhysicalMeasure

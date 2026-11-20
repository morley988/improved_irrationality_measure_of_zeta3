import Zeta5.Construction.Functional

/-!
# The actual cubic rational functional

This module defines the cubic Bernoulli moments and cubic simple-pole
prescription used in the asymmetric zeta(3) determinant.  All coefficients are
rational.  The variable of the target polynomial is the candidate zeta value;
the variable of the input polynomial is the integration variable.

The fixed-denominator map is an actual rational linear map.  Its construction
uses the exact square-node partial fractions already proved in the zeta(5)
project, but neither its moments nor its Stieltjes polynomial are borrowed
from zeta(5).  No analytic integral identity is assumed in this module.
-/

noncomputable section
namespace Zeta3.Construction

open Polynomial
open Zeta5.Construction

/-- The cubic Bernoulli moment `(-1)^k (2k+3) B_(2k+2) / 2`. -/
def rationalMoment (k : ℕ) : ℚ :=
  (-1 : ℚ) ^ k * (2 * k + 3) * bernoulli (2 * k + 2) / 2

def polynomialMoment (q : ℚ[X]) : ℚ :=
  q.sum (fun k a => a * rationalMoment k)

def polynomialMomentMap : ℚ[X] →ₗ[ℚ] ℚ :=
  Polynomial.lsum (fun k => LinearMap.mulRight ℚ (rationalMoment k))

@[simp] theorem polynomialMomentMap_apply (P : ℚ[X]) :
    polynomialMomentMap P = polynomialMoment P := rfl

@[simp] theorem polynomialMoment_X_pow (k : ℕ) :
    polynomialMoment (X ^ k) = rationalMoment k := by
  simp [polynomialMoment, X_pow_eq_monomial]

def harmonicThree (n : ℕ) : ℚ :=
  ∑ k ∈ Finset.range n, 1 / (((k + 1 : ℕ) : ℚ) ^ 3)

def stieltjesConstant (i : ℕ) : ℚ :=
  -(i : ℚ) ^ 2 * harmonicThree (i - 1) - 1 / (2 * (i : ℚ)) - 1 / 2

/-- The cubic prescription for `J_X(1/(t+i²))`; applications have `i≥1`. -/
def stieltjes (i : ℕ) : ℚ[X] :=
  C (stieltjesConstant i) + X * C ((i : ℚ) ^ 2)

/-- `J_(3,X)(P / D_N)`, defined by monic division and simple-pole residues. -/
def numeratorFunctional (N : ℕ) : ℚ[X] →ₗ[ℚ] ℚ[X] :=
  (Polynomial.CAlgHom : ℚ →ₐ[ℚ] ℚ[X]).toLinearMap.comp
      (polynomialMomentMap.comp (monicQuotientMap (denominator N) (denominator_monic N))) +
    ∑ i ∈ Finset.range N,
      (LinearMap.toSpanSingleton ℚ ℚ[X] (stieltjes (i + 1))).comp (residueMap N (i + 1))

theorem numeratorFunctional_apply (N : ℕ) (P : ℚ[X]) :
    numeratorFunctional N P = C (polynomialMoment (P / denominator N)) +
      ∑ i ∈ Finset.range N,
        C (P.eval (pole (i + 1)) / (denominator N).derivative.eval (pole (i + 1))) *
          stieltjes (i + 1) := by
  simp [numeratorFunctional, Polynomial.smul_eq_C_mul]

def numeratorConstant (N : ℕ) (P : ℚ[X]) : ℚ :=
  polynomialMoment (P / denominator N) +
    ∑ i ∈ Finset.range N,
      (P.eval (pole (i + 1)) / (denominator N).derivative.eval (pole (i + 1))) *
        stieltjesConstant (i + 1)

def numeratorLinear (N : ℕ) (P : ℚ[X]) : ℚ :=
  ∑ i ∈ Finset.range N,
    (P.eval (pole (i + 1)) / (denominator N).derivative.eval (pole (i + 1))) *
      ((i + 1 : ℕ) : ℚ) ^ 2

theorem numeratorFunctional_affine (N : ℕ) (P : ℚ[X]) :
    numeratorFunctional N P = C (numeratorConstant N P) + X * C (numeratorLinear N P) := by
  rw [numeratorFunctional_apply]
  simp only [numeratorConstant, numeratorLinear, stieltjes, map_add, map_mul, map_sum]
  simp only [Finset.mul_sum, Finset.sum_mul, mul_add, Finset.sum_add_distrib]
  ring
  congr 1
  apply Finset.sum_congr rfl
  intro i hi
  ring

theorem numeratorFunctional_natDegree_le_one (N : ℕ) (P : ℚ[X]) :
    (numeratorFunctional N P).natDegree ≤ 1 := by
  rw [numeratorFunctional_affine]
  compute_degree

theorem numeratorFunctional_constant_of_vanishing (N : ℕ) (P : ℚ[X])
    (hP : ∀ i ∈ Finset.range N, P.eval (pole (i + 1)) = 0) :
    numeratorFunctional N P = C (polynomialMoment (P / denominator N)) := by
  rw [numeratorFunctional_apply]
  have hz : ∑ i ∈ Finset.range N,
      C (P.eval (pole (i + 1)) / (denominator N).derivative.eval (pole (i + 1))) *
        stieltjes (i + 1) = 0 := by
    apply Finset.sum_eq_zero
    intro i hi
    simp [hP i hi]
  rw [hz, add_zero]

/-- Polynomial inputs have exactly the prescribed cubic moments, independently
of the denominator representation. -/
theorem numeratorFunctional_mul_denominator (N : ℕ) (P : ℚ[X]) :
    numeratorFunctional N (P * denominator N) = C (polynomialMoment P) := by
  rw [numeratorFunctional_constant_of_vanishing]
  · rw [mul_div_cancel_right₀ _ (denominator_ne_zero N)]
  · intro i hi
    rw [eval_mul, pole, denominator_eval_neg_square_eq_zero (i := i + 1) (N := N) (by omega) (by
      have h := Finset.mem_range.mp hi
      omega), mul_zero]

theorem numeratorFunctional_monomial_prescription (N k : ℕ) :
    numeratorFunctional N (X ^ k * denominator N) = C (rationalMoment k) := by
  rw [numeratorFunctional_mul_denominator, polynomialMoment_X_pow]

theorem rationalMoment_zero : rationalMoment 0 = 1 / 4 := by
  norm_num [rationalMoment, bernoulli]

theorem harmonicThree_zero : harmonicThree 0 = 0 := by simp [harmonicThree]

theorem stieltjes_one : stieltjes 1 = X - 1 := by
  have hs : stieltjesConstant 1 = -(1 : ℚ) := by
    norm_num [stieltjesConstant, harmonicThree]
  simp only [stieltjes, hs, Nat.cast_one, one_pow, C_1, mul_one, C_neg]
  ring

theorem stieltjes_eval (i : ℕ) (x : ℝ) :
    (stieltjes i).eval₂ (Rat.castHom ℝ) x =
      (stieltjesConstant i : ℝ) + x * (i : ℝ) ^ 2 := by
  rw [stieltjes, eval₂_add, eval₂_C, eval₂_mul, eval₂_X, eval₂_C]
  simp only [Rat.coe_castHom, Rat.cast_pow, Rat.cast_natCast]

/-- The partial-fraction numerator identity used by this cubic map is a
proved identity, independent of the chosen moment functional. -/
theorem squareNode_partialFraction_identity (N : ℕ) (P : ℚ[X]) :
    P = (P / denominator N) * denominator N +
      ∑ i ∈ Finset.range N,
        C (P.eval (pole (i + 1)) / (denominator N).derivative.eval (pole (i + 1))) *
          (denominator N / (X - C (pole (i + 1)))) :=
  Zeta5.Construction.squareNode_partialFraction_identity N P

end Zeta3.Construction

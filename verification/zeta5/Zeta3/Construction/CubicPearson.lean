import Zeta3.Construction.IntegerPartialFractions
import Zeta3.Construction.CubicRationalFunctional
import Zeta3.Construction.PearsonCompression

/-!
# The actual cubic Pearson identity

For m₁=a+1 and m₂=b+1 the physical weight is
x⁷∏_{j=1}^a(x²−j²)∏_{j=1}^b(x²−j²)/∏_{j=1}^N(x²−j²).
The telescoping shift relation is proved from actual finite products. Its
order seven at zero kills the Laurent coefficient obstruction, so the
Pearson and reflection laws below have no functional-identity hypotheses.
-/

noncomputable section
namespace Zeta3.Construction.Rational
open Polynomial
open scoped RatFunc
variable {K : Type*} [Field K] [CharZero K]

def symmetricSquareProduct (N : ℕ) : K[X] :=
  ∏ j ∈ Finset.range N, (X ^ 2 - C (((j + 1 : ℕ) : K) ^ 2))

theorem centeredDenominator_eq_X_mul_squareProduct (N : ℕ) :
    centeredDenominator (K := K) N = X * symmetricSquareProduct N :=
  centeredDenominator_product N

theorem symmetricSquareProduct_monic (N : ℕ) : (symmetricSquareProduct (K := K) N).Monic := by
  apply Polynomial.monic_prod_of_monic
  intro j hj
  have h : (X ^ 2 - C (((j + 1 : ℕ) : K) ^ 2) : K[X]) =
      (X - C ((j + 1 : ℕ) : K)) * (X + C ((j + 1 : ℕ) : K)) := by
    simp only [map_pow]
    ring
  rw [h]
  exact (monic_X_sub_C _).mul (monic_X_add_C _)

theorem symmetricSquareProduct_eval_zero_ne (N : ℕ) :
    (symmetricSquareProduct (K := K) N).eval 0 ≠ 0 := by
  rw [symmetricSquareProduct, eval_prod]
  apply Finset.prod_ne_zero_iff.mpr
  intro j hj
  simp only [eval_sub, eval_pow, eval_X, eval_C, zero_pow (by norm_num : 2 ≠ 0), zero_sub]
  exact neg_ne_zero.mpr (pow_ne_zero _ (Nat.cast_ne_zero.mpr (by omega)))

theorem symmetricSquareProduct_reflection (N : ℕ) :
    (symmetricSquareProduct (K := K) N).comp (-X) = symmetricSquareProduct N := by
  simp [symmetricSquareProduct, Polynomial.prod_comp]

def cubicWeightNumerator (a b : ℕ) : K[X] :=
  X ^ 6 * centeredDenominator a * centeredDenominator b

def cubicWeight (N a b : ℕ) : RatFunc K :=
  algebraMap K[X] (RatFunc K) (X ^ 7 * symmetricSquareProduct a * symmetricSquareProduct b) /
    algebraMap K[X] (RatFunc K) (symmetricSquareProduct N)

theorem cubicWeight_centered (N a b : ℕ) :
    cubicWeight (K := K) N a b =
      algebraMap K[X] (RatFunc K) (cubicWeightNumerator a b) /
        algebraMap K[X] (RatFunc K) (centeredDenominator N) := by
  have hX : algebraMap K[X] (RatFunc K) (X : K[X]) ≠ 0 :=
    RatFunc.algebraMap_ne_zero X_ne_zero
  have hD : algebraMap K[X] (RatFunc K) (symmetricSquareProduct (K := K) N) ≠ 0 :=
    RatFunc.algebraMap_ne_zero (symmetricSquareProduct_monic N).ne_zero
  simp only [cubicWeight, cubicWeightNumerator, centeredDenominator_eq_X_mul_squareProduct,
    map_mul, map_pow]
  field_simp

theorem cubicWeight_mem_simpleRational (N a b : ℕ) :
    cubicWeight (K := K) N a b ∈ simpleRational := by
  rw [cubicWeight_centered]
  exact centered_fraction_mem_simpleRational N _

theorem cubicWeight_times_polynomial_mem (N a b : ℕ) (f : K[X]) :
    cubicWeight (K := K) N a b * algebraMap K[X] (RatFunc K) f ∈ simpleRational := by
  rw [mul_comm]
  exact polynomial_mul_mem_simpleRational f (cubicWeight_mem_simpleRational N a b)

theorem cubicWeight_boundary_zero (N a b : ℕ) (f : K[X]) :
    rationalCoefficientAt 0 2 (cubicWeight (K := K) N a b * algebraMap K[X] (RatFunc K) f) = 0 := by
  have heq : cubicWeight (K := K) N a b * algebraMap K[X] (RatFunc K) f =
      algebraMap K[X] (RatFunc K) (X ^ 7 * (symmetricSquareProduct a * symmetricSquareProduct b * f)) /
        algebraMap K[X] (RatFunc K) (symmetricSquareProduct N) := by
    simp only [cubicWeight, map_mul]
    ring
  rw [heq]
  simpa only [map_zero, sub_zero, Nat.cast_ofNat] using
    rationalCoefficientAt_boundary_factor (0 : K)
      (symmetricSquareProduct a * symmetricSquareProduct b * f)
      (symmetricSquareProduct N) (symmetricSquareProduct_eval_zero_ne N) 7 2 (by norm_num)

theorem cubicWeight_reflection (N a b : ℕ) :
    rationalReflection (cubicWeight (K := K) N a b) = -cubicWeight N a b := by
  rw [cubicWeight, rationalReflection_fraction]
  simp only [mul_comp, pow_comp, X_comp, symmetricSquareProduct_reflection]
  have hp : ((-X : K[X]) ^ 7) = -(X ^ 7) := by ring
  rw [hp]
  simp only [neg_mul, map_neg, neg_div]

theorem polynomialA_shift (N a b : ℕ) :
    (Pearson.polynomialA (K := K) N (a + 1) (b + 1)).comp (X + 1) =
      X ^ 6 * (X - C (a : K)) * (X - C (b : K)) * (X + C ((N + 1 : ℕ) : K)) := by
  simp only [Pearson.polynomialA, mul_comp, pow_comp, sub_comp, add_comp,
    X_comp, C_comp, one_comp, add_sub_cancel_right, Nat.cast_add, Nat.cast_one, map_add, map_one]
  ring

theorem cubicWeight_shift_cleared (N a b : ℕ) :
    (cubicWeightNumerator (K := K) a b).comp (X + 1) *
        (Pearson.polynomialA N (a + 1) (b + 1)).comp (X + 1) * centeredDenominator N =
      cubicWeightNumerator a b * Pearson.polynomialB N (a + 1) (b + 1) *
        (centeredDenominator N).comp (X + 1) := by
  rw [polynomialA_shift]
  simp only [cubicWeightNumerator, mul_comp, pow_comp, X_comp, Pearson.polynomialB]
  calc
    _ = X ^ 6 * (X + 1) ^ 6 *
        ((centeredDenominator a).comp (X + 1) * (X - C (a : K))) *
        ((centeredDenominator b).comp (X + 1) * (X - C (b : K))) *
        (centeredDenominator N * (X + C ((N + 1 : ℕ) : K))) := by ring
    _ = X ^ 6 * (X + 1) ^ 6 *
        (centeredDenominator a * (X + C ((a + 1 : ℕ) : K))) *
        (centeredDenominator b * (X + C ((b + 1 : ℕ) : K))) *
        ((centeredDenominator N).comp (X + 1) * (X - C (N : K))) := by
      rw [centeredDenominator_shift, centeredDenominator_shift, centeredDenominator_shift]
    _ = _ := by ring

theorem cubicWeight_shift (N a b : ℕ) :
    rationalShift 1 (cubicWeight (K := K) N a b) *
        algebraMap K[X] (RatFunc K) ((Pearson.polynomialA N (a + 1) (b + 1)).comp (X + 1)) =
      cubicWeight N a b * algebraMap K[X] (RatFunc K) (Pearson.polynomialB N (a + 1) (b + 1)) := by
  have hD : algebraMap K[X] (RatFunc K) (centeredDenominator (K := K) N) ≠ 0 :=
    RatFunc.algebraMap_ne_zero (centeredDenominator_monic N).ne_zero
  have hDs : algebraMap K[X] (RatFunc K) ((centeredDenominator (K := K) N).comp (X + 1)) ≠ 0 := by
    have h := (rationalShift (1 : K)).injective.ne hD
    change rationalShift (1 : K) (algebraMap K[X] (RatFunc K) (centeredDenominator N)) ≠
      rationalShift (1 : K) 0 at h
    simpa only [rationalShift_polynomial, taylor_apply, C_1, map_zero] using h
  rw [cubicWeight_centered, rationalShift_fraction, taylor_apply, C_1, taylor_apply, C_1]
  rw [div_mul_eq_mul_div, div_mul_eq_mul_div]
  apply (div_eq_div_iff hDs hD).mpr
  have h := congrArg (algebraMap K[X] (RatFunc K)) (cubicWeight_shift_cleared (K := K) N a b)
  simpa only [map_mul] using h

def cubicLiftedFunctional (ξ : K) (N a b : ℕ) : K[X] →ₗ[K] K :=
  (cubicRationalMap ξ).comp
    ((LinearMap.mulLeft K (cubicWeight (K := K) N a b)).comp (polynomialEmbedding (K := K)))

@[simp] theorem cubicLiftedFunctional_apply (ξ : K) (N a b : ℕ) (f : K[X]) :
    cubicLiftedFunctional ξ N a b f =
      cubicRationalMap ξ (cubicWeight N a b * algebraMap K[X] (RatFunc K) f) := rfl

/-- The actual cubic Pearson identity, proved by finite products, the rational
translation identity, and vanishing of its coefficient boundary term. -/
theorem cubicLiftedFunctional_pearson (ξ : K) (N a b : ℕ) (f : K[X]) :
    cubicLiftedFunctional ξ N a b
        (Pearson.polynomialB N (a + 1) (b + 1) * f.comp (X + 1)) =
      cubicLiftedFunctional ξ N a b (Pearson.polynomialA N (a + 1) (b + 1) * f) := by
  have h := cubicRationalMap_difference ξ
    (cubicWeight_times_polynomial_mem N a b (Pearson.polynomialA N (a + 1) (b + 1) * f))
  rw [cubicWeight_boundary_zero] at h
  have heq : rationalShift 1 (cubicWeight N a b *
      algebraMap K[X] (RatFunc K) (Pearson.polynomialA N (a + 1) (b + 1) * f)) =
        cubicWeight N a b * algebraMap K[X] (RatFunc K)
          (Pearson.polynomialB N (a + 1) (b + 1) * f.comp (X + 1)) := by
    rw [map_mul, rationalShift_polynomial, taylor_apply, C_1, mul_comp, map_mul,
      ← mul_assoc, cubicWeight_shift, mul_assoc, ← map_mul]
  rw [heq] at h
  exact sub_eq_zero.mp h

/-- Reflection-evenness is proved for the same actual functional. -/
theorem cubicLiftedFunctional_even (ξ : K) (N a b : ℕ) (f : K[X]) :
    cubicLiftedFunctional ξ N a b (f.comp (-X)) = cubicLiftedFunctional ξ N a b f := by
  have h := cubicRationalMap_reflection ξ (cubicWeight_times_polynomial_mem N a b f)
  rw [cubicWeight_boundary_zero, neg_zero, map_mul, cubicWeight_reflection,
    rationalReflection_polynomial, neg_mul, map_neg] at h
  exact neg_add_eq_zero.mp h

end Zeta3.Construction.Rational

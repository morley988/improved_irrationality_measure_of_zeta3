import Zeta3.Construction.CubicCompatibility
import Zeta5.Construction.ResidueDerivative

/-! Exact matching of the cubic Pearson weight with the two unequal windows. -/

noncomputable section
namespace Zeta3.Construction.Rational
open Polynomial Zeta5.Construction
open scoped RatFunc
variable {K : Type*} [Field K] [CharZero K]

theorem positiveFactor_succ (m : ℕ) :
    positiveFactor (m + 1) = positiveFactor m * (X + C ((m : ℚ) ^ 2)) := by
  simp only [positiveFactor, Finset.prod_range_succ]

theorem symmetricSquareProduct_succ (m : ℕ) :
    symmetricSquareProduct (K := K) (m + 1) =
      symmetricSquareProduct m * (X ^ 2 - C (((m + 1 : ℕ) : K) ^ 2)) := by
  simp only [symmetricSquareProduct, Finset.prod_range_succ]

theorem positiveFactor_squareLift (a : ℕ) :
    (positiveFactor (a + 1)).comp (-(X ^ 2)) =
      C ((-1 : ℚ) ^ (a + 1)) * X ^ 2 * symmetricSquareProduct a := by
  induction a with
  | zero => simp [positiveFactor, symmetricSquareProduct]
  | succ a ih =>
    rw [positiveFactor_succ, mul_comp, ih, add_comp, X_comp, C_comp,
      symmetricSquareProduct_succ, pow_succ, map_mul]
    simp only [map_neg, map_one]
    ring

theorem denominator_squareLift (N : ℕ) :
    (denominator N).comp (-(X ^ 2)) =
      C ((-1 : ℚ) ^ N) * symmetricSquareProduct N := by
  induction N with
  | zero => simp [denominator, symmetricSquareProduct]
  | succ N ih =>
    rw [denominator_succ, mul_comp, ih, add_comp, X_comp, C_comp,
      symmetricSquareProduct_succ, pow_succ (-1 : ℚ) N, map_mul]
    simp only [map_neg, map_one]
    ring

theorem symmetricSquareProduct_map (N : ℕ) :
    (symmetricSquareProduct (K := ℚ) N).map (Rat.castHom K) =
      symmetricSquareProduct (K := K) N := by
  simp only [symmetricSquareProduct, Polynomial.map_prod, Polynomial.map_sub,
    Polynomial.map_pow, Polynomial.map_X, Polynomial.map_C, Rat.coe_castHom,
    Rat.cast_pow, Rat.cast_natCast]

theorem squareImage_positiveFactor_four (n : ℕ) (hn : 0 < n) :
    squareImage (K := K) (positiveFactor (4 * n)) =
      RatFunc.X ^ 2 * algebraMap K[X] (RatFunc K) (symmetricSquareProduct (4 * n - 1)) := by
  have h := positiveFactor_squareLift (4 * n - 1)
  rw [show 4 * n - 1 + 1 = 4 * n by omega] at h
  have hs : (-1 : ℚ) ^ (4 * n) = 1 := by rw [pow_mul]; norm_num
  rw [hs, C_1, one_mul] at h
  have hm := congrArg (rationalPolynomialImage (K := K)) h
  change squareImage (positiveFactor (4 * n)) = _ at hm
  simpa only [rationalPolynomialImage, RingHom.comp_apply, Polynomial.coe_mapRingHom, Polynomial.map_mul,
    Polynomial.map_pow, Polynomial.map_X, symmetricSquareProduct_map,
    map_mul, map_pow, RatFunc.algebraMap_X] using hm

theorem squareImage_positiveFactor_sixteen (n : ℕ) (hn : 0 < n) :
    squareImage (K := K) (positiveFactor (16 * n)) =
      RatFunc.X ^ 2 * algebraMap K[X] (RatFunc K) (symmetricSquareProduct (16 * n - 1)) := by
  have h := positiveFactor_squareLift (16 * n - 1)
  rw [show 16 * n - 1 + 1 = 16 * n by omega] at h
  have hs : (-1 : ℚ) ^ (16 * n) = 1 := by rw [pow_mul]; norm_num
  rw [hs, C_1, one_mul] at h
  have hm := congrArg (rationalPolynomialImage (K := K)) h
  change squareImage (positiveFactor (16 * n)) = _ at hm
  simpa only [rationalPolynomialImage, RingHom.comp_apply, Polynomial.coe_mapRingHom, Polynomial.map_mul,
    Polynomial.map_pow, Polynomial.map_X, symmetricSquareProduct_map,
    map_mul, map_pow, RatFunc.algebraMap_X] using hm

theorem squareImage_denominator_fifty (n : ℕ) :
    squareImage (K := K) (denominator (50 * n)) =
      algebraMap K[X] (RatFunc K) (symmetricSquareProduct (50 * n)) := by
  have h := denominator_squareLift (50 * n)
  have hs : (-1 : ℚ) ^ (50 * n) = 1 := by rw [pow_mul]; norm_num
  rw [hs, C_1, one_mul] at h
  have hm := congrArg (rationalPolynomialImage (K := K)) h
  change squareImage (denominator (50 * n)) = _ at hm
  simpa only [rationalPolynomialImage, RingHom.comp_apply, Polynomial.coe_mapRingHom,
    symmetricSquareProduct_map] using hm

theorem cubicWeight_concrete_squareLift (n : ℕ) (hn : 0 < n) (p : ℚ[X]) :
    cubicWeight (K := K) (50 * n) (4 * n - 1) (16 * n - 1) *
        algebraMap K[X] (RatFunc K) ((p.map (Rat.castHom K)).comp (-(X ^ 2))) =
      cubicSquareLift (50 * n) (positiveFactor (4 * n) * positiveFactor (16 * n) * p) := by
  rw [cubicSquareLift, map_mul, map_mul, squareImage_positiveFactor_four n hn,
    squareImage_positiveFactor_sixteen n hn, squareImage_denominator_fifty, squareImage_apply]
  simp only [cubicWeight, map_mul, map_pow, RatFunc.algebraMap_X]
  ring

def concretePearsonFunctional (ξ : K) (n : ℕ) : K[X] →ₗ[K] K :=
  Pearson.compressedFunctional (cubicLiftedFunctional ξ (50 * n) (4 * n - 1) (16 * n - 1))

/-- The compressed Pearson functional is exactly the implementation used by
the unequal-window determinant, at every candidate value ξ. -/
theorem concretePearsonFunctional_rational (ξ : K) (n : ℕ) (hn : 0 < n) (p : ℚ[X]) :
    concretePearsonFunctional ξ n (p.map (Rat.castHom K)) =
      (numeratorFunctional (50 * n)
        (positiveFactor (4 * n) * positiveFactor (16 * n) * p)).eval₂ (Rat.castHom K) ξ := by
  simp only [concretePearsonFunctional, Pearson.compressedFunctional_apply,
    cubicLiftedFunctional_apply, Pearson.squareLift]
  rw [cubicWeight_concrete_squareLift (K := K) n hn p,
    cubicRationalMap_cubicSquareLift ξ (50 * n)
      (positiveFactor (4 * n) * positiveFactor (16 * n) * p)]

theorem concretePearsonFunctional_monomial (ξ : K) (n : ℕ) (hn : 0 < n) (k : ℕ) :
    concretePearsonFunctional ξ n (X ^ k) =
      (numeratorFunctional (50 * n)
        (positiveFactor (4 * n) * positiveFactor (16 * n) * X ^ k)).eval₂ (Rat.castHom K) ξ := by
  simpa only [Polynomial.map_pow, Polynomial.map_X] using
    concretePearsonFunctional_rational ξ n hn (X ^ k)

end Zeta3.Construction.Rational

import Zeta3.Construction.CubicPearson
import Zeta3.Construction.Prescription
import Zeta3.Construction.Asymmetric

/-!
# Compatibility of the rational Pearson functional with the actual determinant

This module identifies the actual Bernoulli/simple-pole implementation of J
with K applied after t=−x². The proof checks the polynomial and simple-pole
parts and then uses the proved exact partial-fraction decomposition.
-/

noncomputable section
namespace Zeta3.Construction.Rational
open Polynomial Zeta5.Construction
open scoped RatFunc
variable {K : Type*} [Field K] [CharZero K]

def rationalPolynomialImage : ℚ[X] →+* RatFunc K :=
  (algebraMap K[X] (RatFunc K)).comp (Polynomial.mapRingHom (Rat.castHom K))

def squareImage : ℚ[X] →+* RatFunc K :=
  rationalPolynomialImage.comp (Polynomial.compRingHom (-(X ^ 2)))

theorem squareImage_apply (p : ℚ[X]) :
    squareImage (K := K) p = algebraMap K[X] (RatFunc K)
      ((p.map (Rat.castHom K)).comp (-(X ^ 2))) := by
  simp [squareImage, rationalPolynomialImage, Polynomial.map_comp]

@[simp] theorem squareImage_C (c : ℚ) :
    squareImage (K := K) (C c) = RatFunc.C (c : K) := by
  rw [squareImage_apply]
  simp

@[simp] theorem squareImage_X : squareImage (K := K) X = -(RatFunc.X ^ 2) := by
  rw [squareImage_apply]
  simp

theorem squareImage_injective : Function.Injective (squareImage (K := K)) := by
  intro p q h
  have hm : (Pearson.squareLift p).map (Rat.castHom K) =
      (Pearson.squareLift q).map (Rat.castHom K) := RatFunc.algebraMap_injective K h
  have hl : Pearson.squareLift p = Pearson.squareLift q :=
    (Polynomial.map_injective (Rat.castHom K) (Rat.castHom K).injective) hm
  have hc := congrArg Pearson.squareCompress hl
  simpa only [Pearson.squareCompress_squareLift] using hc

theorem squareImage_ne_zero {p : ℚ[X]} (hp : p ≠ 0) : squareImage (K := K) p ≠ 0 := by
  intro hz
  have h0 : squareImage (K := K) (0 : ℚ[X]) = 0 := map_zero _
  exact hp (squareImage_injective (hz.trans h0.symm))

def cubicSquareLift (N : ℕ) (p : ℚ[X]) : RatFunc K :=
  RatFunc.X ^ 3 * squareImage p / squareImage (denominator N)

theorem cubicSquareLift_add (N : ℕ) (p q : ℚ[X]) :
    cubicSquareLift (K := K) N (p + q) = cubicSquareLift N p + cubicSquareLift N q := by
  simp [cubicSquareLift, mul_add, add_div]

theorem cubicSquareLift_C_mul (N : ℕ) (c : ℚ) (p : ℚ[X]) :
    cubicSquareLift (K := K) N (C c * p) = (c : K) • cubicSquareLift N p := by
  simp only [cubicSquareLift, map_mul, squareImage_C, RatFunc.smul_eq_C_mul]
  ring

theorem cubicSquareLift_polynomial (N : ℕ) (p : ℚ[X]) :
    cubicSquareLift (K := K) N (p * denominator N) =
      algebraMap K[X] (RatFunc K) (X ^ 3 * (p.map (Rat.castHom K)).comp (-(X ^ 2))) := by
  have hD := squareImage_ne_zero (K := K) (denominator_ne_zero N)
  rw [cubicSquareLift, map_mul]
  rw [← mul_assoc, mul_div_cancel_right₀ _ hD, squareImage_apply]
  simp only [map_mul, map_pow, RatFunc.algebraMap_X]

theorem cubicPolynomialMap_cubic_lift (p : ℚ[X]) :
    cubicPolynomialMap (X ^ 3 * (p.map (Rat.castHom K)).comp (-(X ^ 2))) =
      (polynomialMoment p : K) := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
    simp only [Polynomial.map_add, add_comp, mul_add, map_add, hp, hq]
    have hadd : polynomialMoment (p + q) = polynomialMoment p + polynomialMoment q :=
      polynomialMomentMap.map_add p q
    rw [hadd, Rat.cast_add]
  | monomial k a =>
    have heq : X ^ 3 * ((monomial k a).map (Rat.castHom K)).comp (-(X ^ 2)) =
        C ((a : K) * (-1 : K) ^ k) * X ^ (2 * k + 3) := by
      simp only [← C_mul_X_pow_eq_monomial, Polynomial.map_mul, Polynomial.map_C,
        Polynomial.map_pow, Polynomial.map_X, mul_comp, C_comp,
        pow_comp, X_comp, Rat.coe_castHom]
      rw [neg_pow, ← pow_mul, pow_add, map_mul, map_pow]
      simp only [map_neg, map_one]
      ring
    rw [heq, ← smul_eq_C_mul, map_smul, smul_eq_mul, cubicPolynomialMap_X_pow]
    have hmono : polynomialMoment (monomial k a) = a * rationalMoment k := by
      simp [polynomialMoment]
    rw [hmono]
    simp only [rationalMoment, show 2 * k + 3 - 1 = 2 * k + 2 by omega]
    push_cast
    ring

theorem simplePoleNumerator_mul_factor {N i : ℕ} (hi : i < N) :
    simplePoleNumerator N i * (X - C (pole (i + 1))) = denominator N := by
  rw [simplePoleNumerator_eq_nodal_erase hi, denominator_eq_nodal,
    Lagrange.nodal_eq_mul_nodal_erase (s := Finset.range N)
      (v := fun j : ℕ => pole (j + 1)) (Finset.mem_range.mpr hi)]
  ring

theorem cube_quadratic_partialFractions (a : K) :
    RatFunc.X ^ 3 / (RatFunc.C (a ^ 2) - RatFunc.X ^ 2) =
      -RatFunc.X - (a ^ 2 / 2) • (rationalPole a 1 + rationalPole (-a) 1) := by
  have hm : (RatFunc.X : RatFunc K) - RatFunc.C a ≠ 0 := by
    simpa only [map_sub, RatFunc.algebraMap_X, RatFunc.algebraMap_C] using
      RatFunc.algebraMap_ne_zero (monic_X_sub_C a).ne_zero
  have hp : (RatFunc.X : RatFunc K) + RatFunc.C a ≠ 0 := by
    simpa only [map_add, RatFunc.algebraMap_X, RatFunc.algebraMap_C] using
      RatFunc.algebraMap_ne_zero (monic_X_add_C a).ne_zero
  have hq : RatFunc.C (a ^ 2) - (RatFunc.X : RatFunc K) ^ 2 ≠ 0 := by
    rw [show RatFunc.C (a ^ 2) - (RatFunc.X : RatFunc K) ^ 2 =
      -((RatFunc.X - RatFunc.C a) * (RatFunc.X + RatFunc.C a)) by rw [map_pow]; ring]
    exact neg_ne_zero.mpr (mul_ne_zero hm hp)
  simp only [rationalPole, pow_one, map_sub, map_add, map_neg, RatFunc.algebraMap_X,
    RatFunc.algebraMap_C, sub_neg_eq_add, RatFunc.smul_eq_C_mul, map_div₀,
    map_pow, map_ofNat]
  rw [map_pow] at hq
  field_simp
  ring

theorem cubicSquareLift_simplePole {N i : ℕ} (hi : i < N) :
    cubicSquareLift (K := K) N (simplePoleNumerator N i) =
      -RatFunc.X - (((i + 1 : ℕ) : K) ^ 2 / 2) •
        (rationalPole ((i + 1 : ℕ) : K) 1 + rationalPole (-((i + 1 : ℕ) : K)) 1) := by
  have hD := squareImage_ne_zero (K := K) (denominator_ne_zero N)
  have hF := squareImage_ne_zero (K := K) (monic_X_sub_C (pole (i + 1))).ne_zero
  have he := congrArg (squareImage (K := K)) (simplePoleNumerator_mul_factor hi)
  rw [map_mul] at he
  have hratio : cubicSquareLift (K := K) N (simplePoleNumerator N i) =
      RatFunc.X ^ 3 / squareImage (X - C (pole (i + 1))) := by
    rw [cubicSquareLift]
    apply (div_eq_div_iff hD hF).mpr
    rw [mul_assoc, he]
  rw [hratio]
  have hfactor : squareImage (K := K) (X - C (pole (i + 1))) =
      RatFunc.C (((i + 1 : ℕ) : K) ^ 2) - RatFunc.X ^ 2 := by
    simp only [map_sub, squareImage_X, squareImage_C, pole, Rat.cast_neg, Rat.cast_pow,
      Rat.cast_natCast, map_neg]
    ring
  rw [hfactor]
  exact cube_quadratic_partialFractions _

theorem cubicRationalMap_X (ξ : K) : cubicRationalMap ξ RatFunc.X = 1 / 2 := by
  rw [← RatFunc.algebraMap_X, cubicRationalMap_polynomial]
  have h := cubicPolynomialMap_X_pow (K := K) 1
  simpa using h

theorem cubicRationalMap_nat_pole (ξ : K) (n : ℕ) :
    cubicRationalMap ξ (rationalPole (n : K) 1) = -ξ + (harmonicThree n : K) := by
  have h := cubicRationalMap_pole ξ (n : ℤ)
  simpa only [Int.cast_natCast, cubicPoleValue, integerHarmonic] using h

theorem cubicRationalMap_negative_pole (ξ : K) (n : ℕ) :
    cubicRationalMap ξ (rationalPole (-((n + 1 : ℕ) : K)) 1) =
      -ξ + (harmonicThree n : K) := by
  have h := cubicRationalMap_pole ξ (Int.negSucc n)
  simpa only [Int.cast_negSucc, Nat.cast_add, Nat.cast_one, cubicPoleValue, integerHarmonic] using h

theorem cubicRationalMap_cubicSquareLift_simplePole (ξ : K) {N i : ℕ} (hi : i < N) :
    cubicRationalMap ξ (cubicSquareLift N (simplePoleNumerator N i)) =
      (stieltjes (i + 1)).eval₂ (Rat.castHom K) ξ := by
  rw [cubicSquareLift_simplePole hi, map_sub, map_neg, map_smul, map_add,
    cubicRationalMap_X, cubicRationalMap_nat_pole, cubicRationalMap_negative_pole]
  simp only [smul_eq_mul, stieltjes, stieltjesConstant, eval₂_add, eval₂_C,
    eval₂_mul, eval₂_X, Rat.coe_castHom, Rat.cast_sub, Rat.cast_add, Rat.cast_mul,
    Rat.cast_neg, Rat.cast_div, Rat.cast_pow, Rat.cast_natCast, Rat.cast_one,
    Rat.cast_ofNat, Nat.add_sub_cancel, harmonicThree_succ]
  push_cast
  have hiK : (i : K) + 1 ≠ 0 := by exact_mod_cast (show i + 1 ≠ 0 by omega)
  field_simp
  ring

theorem cubicSquareLift_partialFraction (N : ℕ) (p : ℚ[X]) :
    cubicSquareLift (K := K) N p =
      cubicSquareLift N ((p / denominator N) * denominator N) +
        ∑ i ∈ Finset.range N,
          (p.eval (pole (i + 1)) / (denominator N).derivative.eval (pole (i + 1)) : K) •
            cubicSquareLift N (simplePoleNumerator N i) := by
  have h := congrArg (cubicSquareLift (K := K) N) (squareNode_partialFraction_identity N p)
  rw [cubicSquareLift_add] at h
  rw [h]
  congr 1
  simp only [cubicSquareLift, simplePoleNumerator, map_sum, Finset.mul_sum,
    Finset.sum_div, map_mul, squareImage_C, RatFunc.smul_eq_C_mul]
  apply Finset.sum_congr rfl
  intro i hi
  simp only [Rat.cast_div]
  ring

/-- The complete implementation-level compatibility theorem. Both defining
parts of J are identified, so no integral or Pearson hypothesis remains. -/
theorem cubicRationalMap_cubicSquareLift (ξ : K) (N : ℕ) (p : ℚ[X]) :
    cubicRationalMap ξ (cubicSquareLift N p) =
      (numeratorFunctional N p).eval₂ (Rat.castHom K) ξ := by
  rw [cubicSquareLift_partialFraction, map_add, cubicSquareLift_polynomial,
    cubicRationalMap_polynomial, cubicPolynomialMap_cubic_lift, map_sum,
    numeratorFunctional_apply, eval₂_add, eval₂_C, eval₂_finsetSum]
  congr 1
  apply Finset.sum_congr rfl
  intro i hi
  rw [map_smul, cubicRationalMap_cubicSquareLift_simplePole ξ (Finset.mem_range.mp hi),
    eval₂_mul, eval₂_C]
  simp only [smul_eq_mul, Rat.coe_castHom, Rat.cast_div]

end Zeta3.Construction.Rational

import Zeta3.Construction.SimpleRational
import Zeta3.Construction.BernoulliCubic
import Zeta3.Construction.Functional
import Zeta3.Construction.RationalReflection

/-!
# The actual cubic functional on rational functions

Its values on every polynomial and every integer simple pole are prescribed
explicitly. Consistency follows from the injectivity theorem in
`SimpleRational`, and the extension outside that subspace is never used to
assert a Pearson identity.
-/

noncomputable section
namespace Zeta3.Construction.Rational
open Polynomial Finset
open scoped RatFunc
variable {K : Type*} [Field K] [CharZero K]

def integerHarmonic : ℤ → ℚ
  | .ofNat n => harmonicThree n
  | .negSucc n => harmonicThree n

theorem harmonicThree_succ (n : ℕ) :
    harmonicThree (n + 1) = harmonicThree n + 1 / ((n + 1 : ℕ) : ℚ) ^ 3 := by
  simp only [harmonicThree, Finset.sum_range_succ]

theorem integerHarmonic_step (i : ℤ) :
    integerHarmonic (i - 1) - integerHarmonic i = -((i : ℚ) ^ 3)⁻¹ := by
  cases i with
  | ofNat n =>
    cases n with
    | zero =>
      change harmonicThree 0 - harmonicThree 0 = -((0 : ℚ) ^ 3)⁻¹
      simp
    | succ n =>
      have hsub : Int.ofNat (n + 1) - 1 = Int.ofNat n := by
        simp only [Int.ofNat_eq_natCast]
        omega
      rw [hsub]
      simp only [integerHarmonic, harmonicThree_succ, Int.ofNat_eq_natCast,
        Int.cast_natCast, one_div]
      ring
  | negSucc n =>
    have hsub : Int.negSucc n - 1 = Int.negSucc (n + 1) := by omega
    rw [hsub]
    simp only [integerHarmonic, harmonicThree_succ, Int.cast_negSucc, Nat.cast_add,
      Nat.cast_one, one_div]
    rw [show (-((n : ℚ) + 1)) ^ 3 = -(((n : ℚ) + 1) ^ 3) by ring, inv_neg]
    ring

theorem integerHarmonic_reflection (i : ℤ) :
    integerHarmonic i - integerHarmonic (-i) = ((i : ℚ) ^ 3)⁻¹ := by
  cases i with
  | ofNat n =>
    cases n with
    | zero =>
      change harmonicThree 0 - harmonicThree 0 = ((0 : ℚ) ^ 3)⁻¹
      simp
    | succ n =>
      have hneg : -(Int.ofNat (n + 1)) = Int.negSucc n := by
        simp [Int.ofNat_eq_natCast, Int.negSucc_eq]
      rw [hneg]
      simp only [integerHarmonic, harmonicThree_succ, Int.ofNat_eq_natCast, Int.cast_natCast,
        Int.cast_add, Int.cast_one, Nat.cast_add, Nat.cast_one, one_div]
      ring
  | negSucc n =>
    have hneg : -(Int.negSucc n) = Int.ofNat (n + 1) := by
      simp [Int.ofNat_eq_natCast, Int.negSucc_eq, neg_neg]
    rw [hneg]
    simp only [integerHarmonic, harmonicThree_succ, Int.cast_negSucc, Nat.cast_add,
      Nat.cast_one, one_div]
    rw [show (-((n : ℚ) + 1)) ^ 3 = -(((n : ℚ) + 1) ^ 3) by ring, inv_neg]
    ring

def cubicPoleValue (ξ : K) (i : ℤ) : K := -ξ + (integerHarmonic i : K)

theorem cubicPoleValue_step (ξ : K) (i : ℤ) :
    cubicPoleValue ξ (i - 1) - cubicPoleValue ξ i = -((i : K) ^ 3)⁻¹ := by
  have h := congrArg (Rat.castHom K) (integerHarmonic_step i)
  simp only [Rat.coe_castHom, Rat.cast_sub, Rat.cast_neg, Rat.cast_inv, Rat.cast_pow,
    Rat.cast_intCast] at h
  unfold cubicPoleValue
  linear_combination h

theorem cubicPoleValue_reflection (ξ : K) (i : ℤ) :
    cubicPoleValue ξ i - cubicPoleValue ξ (-i) = ((i : K) ^ 3)⁻¹ := by
  have h := congrArg (Rat.castHom K) (integerHarmonic_reflection i)
  simp only [Rat.coe_castHom, Rat.cast_sub, Rat.cast_inv, Rat.cast_pow, Rat.cast_intCast] at h
  unfold cubicPoleValue
  linear_combination h

def simpleDataValue (ξ : K) : (K[X] × (ℤ →₀ K)) →ₗ[K] K :=
  cubicPolynomialMap.comp (LinearMap.fst K K[X] (ℤ →₀ K)) +
    (Finsupp.linearCombination K (cubicPoleValue ξ)).comp
      (LinearMap.snd K K[X] (ℤ →₀ K))

def cubicRationalMap (ξ : K) : RatFunc K →ₗ[K] K :=
  (simpleDataValue ξ).comp simpleRepresentation.leftInverse

theorem cubicRationalMap_representation (ξ : K) (p : K[X]) (r : ℤ →₀ K) :
    cubicRationalMap ξ (simpleRepresentation (p, r)) =
      cubicPolynomialMap p + ∑ i ∈ r.support, r i * cubicPoleValue ξ i := by
  rw [cubicRationalMap, LinearMap.comp_apply,
    LinearMap.leftInverse_apply_of_inj (LinearMap.ker_eq_bot.mpr simpleRepresentation_injective)]
  rfl

@[simp] theorem cubicRationalMap_polynomial (ξ : K) (p : K[X]) :
    cubicRationalMap ξ (algebraMap K[X] (RatFunc K) p) = cubicPolynomialMap p := by
  rw [← simpleRepresentation_polynomial p, cubicRationalMap_representation]
  simp

@[simp] theorem cubicRationalMap_pole (ξ : K) (i : ℤ) :
    cubicRationalMap ξ (rationalPole (i : K) 1) = cubicPoleValue ξ i := by
  have h := cubicRationalMap_representation ξ 0 (Finsupp.single i 1)
  simpa [simpleDataValue, Finsupp.sum_single_index] using h

theorem cubicRationalMap_difference (ξ : K) {f : RatFunc K} (hf : f ∈ simpleRational) :
    cubicRationalMap ξ (rationalShift 1 f) - cubicRationalMap ξ f =
      rationalCoefficientAt 0 2 f := by
  apply simpleRational_induction hf
    (fun f => cubicRationalMap ξ (rationalShift 1 f) - cubicRationalMap ξ f =
      rationalCoefficientAt 0 2 f)
  · intro p
    have hcoeff : rationalCoefficientAt (0 : K) 2 (algebraMap K[X] (RatFunc K) p) = p.coeff 2 := by
      simpa only [Nat.cast_ofNat, Polynomial.taylor_zero] using
        rationalCoefficientAt_polynomial (0 : K) p 2
    rw [rationalShift_polynomial, cubicRationalMap_polynomial, cubicRationalMap_polynomial,
      hcoeff, ← map_sub]
    exact cubicPolynomialMap_difference p
  · intro i
    have hcoeff : rationalCoefficientAt (0 : K) 2 (rationalPole (i : K) 1) = -((i : K) ^ 3)⁻¹ := by
      simpa only [Nat.cast_ofNat] using rationalCoefficientAt_zero_pole (i : K) 2
    rw [rationalPole_shift,
      show (i : K) - 1 = ((i - 1 : ℤ) : K) by push_cast; rfl,
      cubicRationalMap_pole, cubicRationalMap_pole, cubicPoleValue_step,
      hcoeff]
  · intro f g hf hg
    simp only [map_add]
    linear_combination hf + hg
  · intro c f hf
    change cubicRationalMap ξ ((rationalShift (1 : K)).toLinearMap (c • f)) -
      cubicRationalMap ξ (c • f) = rationalCoefficientAt 0 2 (c • f)
    simp only [map_smul, smul_eq_mul]
    change c * cubicRationalMap ξ (rationalShift 1 f) - c * cubicRationalMap ξ f =
      c * rationalCoefficientAt 0 2 f
    linear_combination c * hf

theorem cubicRationalMap_reflection (ξ : K) {f : RatFunc K} (hf : f ∈ simpleRational) :
    cubicRationalMap ξ (rationalReflection f) + cubicRationalMap ξ f =
      -rationalCoefficientAt 0 2 f := by
  apply simpleRational_induction hf
    (fun f => cubicRationalMap ξ (rationalReflection f) + cubicRationalMap ξ f =
      -rationalCoefficientAt 0 2 f)
  · intro p
    have hcoeff : rationalCoefficientAt (0 : K) 2 (algebraMap K[X] (RatFunc K) p) = p.coeff 2 := by
      simpa only [Nat.cast_ofNat, Polynomial.taylor_zero] using
        rationalCoefficientAt_polynomial (0 : K) p 2
    rw [rationalReflection_polynomial, cubicRationalMap_polynomial,
      cubicRationalMap_polynomial, hcoeff]
    exact cubicPolynomialMap_reflection p
  · intro i
    have hcoeff : rationalCoefficientAt (0 : K) 2 (rationalPole (i : K) 1) = -((i : K) ^ 3)⁻¹ := by
      simpa only [Nat.cast_ofNat] using rationalCoefficientAt_zero_pole (i : K) 2
    rw [rationalReflection_pole, ← Int.cast_neg, map_neg, cubicRationalMap_pole,
      cubicRationalMap_pole, hcoeff, neg_neg]
    linear_combination cubicPoleValue_reflection ξ i
  · intro f g hf hg
    simp only [map_add]
    linear_combination hf + hg
  · intro c f hf
    change cubicRationalMap ξ (rationalReflection.toLinearMap (c • f)) +
      cubicRationalMap ξ (c • f) = -rationalCoefficientAt 0 2 (c • f)
    simp only [map_smul, smul_eq_mul]
    change c * cubicRationalMap ξ (rationalReflection f) + c * cubicRationalMap ξ f =
      -(c * rationalCoefficientAt 0 2 f)
    linear_combination c * hf

end Zeta3.Construction.Rational

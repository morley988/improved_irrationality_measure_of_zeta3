import Zeta5.Arithmetic.BernoulliFunctional
import Zeta3.Construction.PearsonDegrees

/-!
# The cubic Bernoulli functional on polynomials

These identities hold over every characteristic-zero field. They are the
polynomial part of the rational Pearson functional, including the exact
coefficient-of-x² boundary term in the translation identity.
-/

noncomputable section
namespace Zeta3.Construction.Rational
open Polynomial Finset
variable {K : Type*} [Field K] [CharZero K]

def bernoulliMap : K[X] →ₗ[K] K :=
  Polynomial.lsum (fun n => LinearMap.mulRight K (_root_.bernoulli n : K))

@[simp] theorem bernoulliMap_monomial (n : ℕ) (a : K) :
    bernoulliMap (monomial n a) = a * (_root_.bernoulli n : K) := by
  simp [bernoulliMap, Polynomial.lsum_apply, Polynomial.sum_monomial_index]

@[simp] theorem bernoulliMap_X_pow (n : ℕ) :
    bernoulliMap ((X : K[X]) ^ n) = (_root_.bernoulli n : K) := by
  simpa only [monomial_one_right_eq_X_pow, one_mul] using bernoulliMap_monomial n (1 : K)

@[simp] theorem bernoulliMap_C (a : K) : bernoulliMap (C a) = a := by
  simpa only [monomial_zero_left, bernoulli_zero, Rat.cast_one, mul_one] using
    bernoulliMap_monomial 0 a

@[simp] theorem bernoulliMap_C_mul (a : K) (p : K[X]) :
    bernoulliMap (C a * p) = a * bernoulliMap p := by
  rw [← smul_eq_C_mul, map_smul, smul_eq_mul]

theorem bernoulliMap_shift_pow (n : ℕ) :
    bernoulliMap ((X + 1 : K[X]) ^ n) =
      ∑ k ∈ range (n + 1), (n.choose k : K) * (_root_.bernoulli k : K) := by
  rw [add_pow, map_sum]
  apply Finset.sum_congr rfl
  intro k hk
  simp only [one_pow, mul_one]
  rw [mul_comm, ← C_eq_natCast, bernoulliMap_C_mul, bernoulliMap_X_pow]

theorem bernoulliMap_difference (p : K[X]) :
    bernoulliMap (p.comp (X + 1) - p) = p.derivative.eval 0 := by
  have hsum (n : ℕ) : (∑ k ∈ range n, (n.choose k : K) * (_root_.bernoulli k : K)) =
      if n = 1 then 1 else 0 := by
    calc
      _ = ((∑ k ∈ range n, (n.choose k : ℚ) * _root_.bernoulli k : ℚ) : K) := by
        push_cast
        rfl
      _ = _ := by rw [_root_.sum_bernoulli]; split_ifs <;> norm_num
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
    rw [add_comp, add_sub_add_comm, map_add, hp, hq, derivative_add, eval_add]
  | monomial n a =>
    rw [← C_mul_X_pow_eq_monomial, mul_comp, C_comp, pow_comp, X_comp,
      map_sub, bernoulliMap_C_mul, bernoulliMap_C_mul,
      bernoulliMap_shift_pow, bernoulliMap_X_pow, sum_range_succ,
      Nat.choose_self, Nat.cast_one, one_mul, hsum]
    rw [derivative_C_mul_X_pow]
    simp only [eval_mul, eval_C, eval_pow, eval_X]
    by_cases hn : n = 1
    · subst n; norm_num; ring
    · rw [if_neg hn]
      cases n with
      | zero => simp
      | succ n =>
        have hn0 : n ≠ 0 := by omega
        simp [Nat.add_sub_cancel, zero_pow hn0]

/-- The polynomial part K(f)=B(f')/2 of the cubic functional. -/
def cubicPolynomialMap : K[X] →ₗ[K] K :=
  (2 : K)⁻¹ • (bernoulliMap.comp Polynomial.derivative)

theorem cubicPolynomialMap_apply (p : K[X]) :
    cubicPolynomialMap p = bernoulliMap p.derivative / 2 := by
  simp only [cubicPolynomialMap, LinearMap.smul_apply, LinearMap.comp_apply, smul_eq_mul]
  ring

@[simp] theorem cubicPolynomialMap_C (a : K) : cubicPolynomialMap (C a) = 0 := by
  rw [cubicPolynomialMap_apply, derivative_C, map_zero, zero_div]

@[simp] theorem cubicPolynomialMap_X_pow (n : ℕ) :
    cubicPolynomialMap ((X : K[X]) ^ n) = (n : K) * (_root_.bernoulli (n - 1) : K) / 2 := by
  rw [cubicPolynomialMap_apply, derivative_X_pow]
  rw [bernoulliMap_C_mul, bernoulliMap_X_pow]

theorem cubicPolynomialMap_difference (p : K[X]) :
    cubicPolynomialMap (p.comp (X + 1) - p) = p.coeff 2 := by
  rw [cubicPolynomialMap_apply, derivative_sub, derivative_comp]
  simp only [derivative_add, derivative_X, derivative_one, add_zero, one_mul]
  rw [bernoulliMap_difference, ← coeff_zero_eq_eval_zero, coeff_derivative, coeff_derivative]
  norm_num

theorem cubicPolynomialMap_even_monomial (k : ℕ) :
    cubicPolynomialMap ((X : K[X]) ^ (2 * k)) = if k = 1 then -(2 : K)⁻¹ else 0 := by
  rw [cubicPolynomialMap_X_pow]
  by_cases hk0 : k = 0
  · simp [hk0]
  by_cases hk1 : k = 1
  · simp [hk1, bernoulli_one]
    ring
  · have hodd : Odd (2 * k - 1) := by
      refine ⟨k - 1, ?_⟩
      omega
    rw [bernoulli_eq_zero_of_odd hodd (by omega), Rat.cast_zero, mul_zero, zero_div,
      if_neg hk1]

theorem cubicPolynomialMap_reflection (p : K[X]) :
    cubicPolynomialMap (p.comp (-X)) + cubicPolynomialMap p = -p.coeff 2 := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
    simp only [add_comp, map_add, coeff_add]
    linear_combination hp + hq
  | monomial n a =>
    rw [← C_mul_X_pow_eq_monomial, mul_comp, C_comp, pow_comp, X_comp]
    rw [neg_pow, ← smul_eq_C_mul, map_smul]
    rw [← smul_eq_C_mul, map_smul]
    simp only [smul_eq_mul]
    rcases Nat.even_or_odd n with hn | hn
    · obtain ⟨k, rfl⟩ := hn
      have hpow : ((-1 : K[X]) ^ (k + k)) = 1 := by
        rw [show k + k = 2 * k by omega, pow_mul]
        simp
      rw [hpow, one_mul]
      rw [show k + k = 2 * k by omega, cubicPolynomialMap_even_monomial]
      by_cases hk : k = 1
      · subst k
        norm_num
        ring
      · have hne : 2 * k ≠ 2 := by omega
        simp [hk, coeff_C_mul, coeff_X_pow, hne, Ne.symm hne]
    · have hp : ((-1 : K[X]) ^ n) = -1 := hn.neg_one_pow
      rw [hp, neg_one_mul, map_neg]
      have hne : n ≠ 2 := by
        obtain ⟨k, hk⟩ := hn
        omega
      simp [coeff_C_mul, coeff_X_pow, hne, Ne.symm hne]

end Zeta3.Construction.Rational

import Zeta3.Arithmetic.StieltjesValuations
import Zeta5.Arithmetic.BernoulliLoss

/-!
# The cubic functional is a first-derivative Bernoulli evaluation

This is an identity for the actual cubic moments. It gives a loss of two
prime powers below the prime square: one for the derivative and one for
Bernoulli evaluation. The analogous quintic argument loses four powers.
-/

noncomputable section
namespace Zeta3.Arithmetic
open Polynomial Finset OddZeta.FourValue Zeta3.Construction
open Zeta5.Arithmetic

def bernoulliMomentNumerator (P : ℚ[X]) : ℚ[X] := X ^ 3 * P.comp (-(X ^ 2))

theorem bernoulliMomentNumerator_add (P Q : ℚ[X]) :
    bernoulliMomentNumerator (P + Q) = bernoulliMomentNumerator P + bernoulliMomentNumerator Q := by
  simp only [bernoulliMomentNumerator, add_comp, mul_add]

theorem bernoulliMomentNumerator_monomial (n : ℕ) (a : ℚ) :
    bernoulliMomentNumerator (monomial n a) = C (a * (-1 : ℚ) ^ n) * X ^ (2 * n + 3) := by
  apply Polynomial.funext
  intro x
  simp only [bernoulliMomentNumerator, eval_mul, eval_pow, eval_X, eval_comp,
    eval_neg, eval_monomial, eval_C]
  rw [neg_pow, pow_add, pow_mul]
  ring

theorem bernoulliMomentNumerator_natDegree_le (P : ℚ[X]) :
    (bernoulliMomentNumerator P).natDegree ≤ 2 * P.natDegree + 3 := by
  apply natDegree_mul_le.trans
  rw [natDegree_X_pow, natDegree_comp, natDegree_neg, natDegree_X_pow]
  omega

theorem bernoulliMoment_monomial (n : ℕ) (a : ℚ) :
    (1 / 2 : ℚ) * bernoulliFunctional (bernoulliMomentNumerator (monomial n a)).derivative =
      a * rationalMoment n := by
  rw [bernoulliMomentNumerator_monomial, derivative_C_mul_X_pow,
    show 2 * n + 3 - 1 = 2 * n + 2 by omega,
    bernoulliFunctional_C_mul, bernoulliFunctional_X_pow]
  simp only [rationalMoment]
  push_cast
  ring

theorem polynomialMoment_eq_bernoulliFunctional (P : ℚ[X]) :
    polynomialMoment P = (1 / 2 : ℚ) * bernoulliFunctional (bernoulliMomentNumerator P).derivative := by
  change polynomialMomentMap P = _
  induction P using Polynomial.induction_on' with
  | add P Q hP hQ =>
    rw [map_add, hP, hQ, bernoulliMomentNumerator_add]
    simp only [map_add, mul_add]
  | monomial n a =>
    rw [bernoulliMoment_monomial]
    simp [polynomialMomentMap, Polynomial.lsum_apply, Polynomial.sum_monomial_index]

variable {p : ℕ} [Fact p.Prime]

theorem polynomialMoment_padicLower_of_integerValuedNumerator {P : ℚ[X]} {w : ℤ} {L : ℕ}
    (hp : 2 < p) (hP : IntegerValuedLower p w (bernoulliMomentNumerator P))
    (hL : (bernoulliMomentNumerator P).natDegree ≤ L) (hLp : L + 1 < p ^ 2) :
    PadicLower p (w - 2) (polynomialMoment P) := by
  rw [polynomialMoment_eq_bernoulliFunctional]
  have h := (half_integral (p := p) hp).mul
    (bernoulliFunctional_iterate_derivative_below_square hP hL hLp 1)
  simpa only [Function.iterate_one, Nat.cast_one, zero_add,
    show w - 1 - 1 = w - 2 by omega] using h

theorem polynomialMoment_padicLower_log {P : ℚ[X]} {w : ℤ} {L : ℕ}
    (hP : IntegerValuedLower p w (bernoulliMomentNumerator P))
    (hL : (bernoulliMomentNumerator P).natDegree ≤ L) :
    PadicLower p (w - 2 * (Nat.log p (L + 1) : ℤ) - (padicValNat p 2 : ℤ))
      (polynomialMoment P) := by
  rw [polynomialMoment_eq_bernoulliFunctional]
  have h2 : PadicLower p (-(padicValNat p 2 : ℤ)) (1 / 2 : ℚ) := by
    right
    simp only [one_div, padicValRat.inv]
    norm_cast
  have h := h2.mul (bernoulliFunctional_iterate_derivative_log hP hL 1)
  simp only [Function.iterate_one] at h
  convert h using 1
  push_cast
  ring

theorem bernoulliMomentNumerator_integerValued {Q : ℚ[X]} {w : ℤ}
    (hQ : IntegerValuedLower p w (Q.comp (-(X ^ 2)))) :
    IntegerValuedLower p w (bernoulliMomentNumerator Q) := by
  intro k
  have hpower : PadicLower p 0 ((k : ℚ) ^ 3) := by
    have he : ((k ^ 3 : ℤ) : ℚ) = (k : ℚ) ^ 3 := by push_cast; rfl
    rw [← he]
    exact padicLower_int (p := p) (k ^ 3)
  simpa only [bernoulliMomentNumerator, eval_mul, eval_pow, eval_X, zero_add] using
    hpower.mul (hQ k)

end Zeta3.Arithmetic

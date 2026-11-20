import Zeta5.Arithmetic.SmallPrimeQuotient
import Zeta3.Arithmetic.BernoulliMoments

/-! All-prime cubic high-quotient bounds. The generic exact quotient and
binomial scalar factorization are reused, with the actual cubic Bernoulli
numerator and its first derivative. -/
noncomputable section
namespace Zeta3.Arithmetic
open Polynomial Finset OddZeta.FourValue Zeta5.Construction
open Zeta5.Arithmetic

lemma bernoulliCentralQuotient_eval (N k : ℕ) (x : ℚ) :
    (bernoulliMomentNumerator (centralQuotientPolynomial N k)).eval x =
      (-((-1 : ℚ)^(N+k+1)))*centralQuotientScalar N k*x^5*
        (binomialPolynomial k).eval (x-((N+1 : ℕ) : ℚ))*
        (binomialPolynomial k).eval (-x-((N+1 : ℕ) : ℚ)) := by
  have hpair : (∏ a ∈ range k, (-x^2+((N+1+a : ℕ) : ℚ)^2)) =
      (descPochhammer ℚ k).eval (x-((N+1 : ℕ) : ℚ))*
        (descPochhammer ℚ k).eval (-x-((N+1 : ℕ) : ℚ)) := by
    rw [descPochhammer_eval_eq_prod_range, descPochhammer_eval_eq_prod_range,
      ← prod_mul_distrib]
    apply prod_congr rfl
    intro a _
    push_cast
    ring
  simp only [bernoulliMomentNumerator, centralQuotientPolynomial, centralTailProduct,
    eval_mul, eval_pow, eval_X, eval_comp, eval_neg, eval_C, eval_prod, eval_add]
  rw [hpair]
  simp only [binomialPolynomial, eval_mul, eval_C, centralQuotientScalar]
  have hf : (Nat.factorial k : ℚ) ≠ 0 := by positivity
  field_simp

variable {p : ℕ} [Fact p.Prime]

theorem bernoulliCentralQuotient_integerValuedLower (N k D : ℕ)
    (hD : 2*(N+k+1) ≤ D) :
    IntegerValuedLower p (-5*(Nat.log p D : ℤ))
      (bernoulliMomentNumerator (centralQuotientPolynomial N k)) := by
  intro x
  rw [bernoulliCentralQuotient_eval]
  have hleft : (x : ℚ)-((N+1 : ℕ) : ℚ) = ((x-(N+1 : ℕ) : ℤ) : ℚ) := by
    push_cast
    rfl
  have hright : -(x : ℚ)-((N+1 : ℕ) : ℚ) = ((-x-(N+1 : ℕ) : ℤ) : ℚ) := by
    push_cast
    rfl
  rw [hleft, hright, binomialPolynomial_eval_int, binomialPolynomial_eval_int]
  have hs := (sign_prime_integral (p := p) (N+k+1)).neg
  have hc := centralQuotientScalar_padicLower_log (p := p) N k D hD
  have hx : PadicLower p 0 ((x : ℚ)^5) := by
    right
    rw [padicValRat.pow, padicValRat.of_int]
    positivity
  simpa only [zero_add, add_zero] using
    (((hs.mul hc).mul hx).mul (padicLower_int _)).mul (padicLower_int _)

theorem centralQuotientMoment_padicLower_log (N k D : ℕ)
    (hD : 2*(N+k+1) ≤ D) (hdeg : 2*k+6 ≤ D) :
    PadicLower p (-9*(Nat.log p D : ℤ)-(padicValNat p 24 : ℤ))
      (Zeta3.Construction.polynomialMoment (centralQuotientPolynomial N k)) := by
  have hi := bernoulliCentralQuotient_integerValuedLower (p := p) N k D hD
  have hd : (bernoulliMomentNumerator (centralQuotientPolynomial N k)).natDegree ≤ 2*k+5 :=
    (bernoulliMomentNumerator_natDegree_le _).trans (by
      have h := centralQuotientPolynomial_natDegree_le N k
      omega)
  have h := polynomialMoment_padicLower_log hi hd
  apply h.mono
  have hl : (Nat.log p (2*k+5+1) : ℤ) ≤ Nat.log p D := by
    exact_mod_cast Nat.log_mono_right hdeg
  have h24 : padicValNat p 2 ≤ padicValNat p 24 := by
    rw [show 24 = 2 * 12 by norm_num, padicValNat.mul (by norm_num) (by norm_num)]
    omega
  omega

theorem numeratorFunctional_scaledCentral_high (N k : ℕ) :
    Zeta3.Construction.numeratorFunctional N (scaledCentralNumerator N (N+k+1)) =
      C (Zeta3.Construction.polynomialMoment (centralQuotientPolynomial N k)) := by
  rw [Zeta3.Construction.numeratorFunctional_apply, scaledCentralNumerator_high_factorization,
    mul_div_cancel_left₀ _ (denominator_ne_zero N)]
  have hz : (∑ i ∈ range N,
      C ((denominator N*centralQuotientPolynomial N k).eval (pole (i+1))/
        (denominator N).derivative.eval (pole (i+1)))*Zeta3.Construction.stieltjes (i+1)) = 0 := by
    apply sum_eq_zero
    intro i hi
    rw [eval_mul, pole, denominator_eval_neg_square_eq_zero (by omega : 1 ≤ i+1)
      (by simpa using mem_range.mp hi)]
    simp
  rw [hz, add_zero]

end Zeta3.Arithmetic

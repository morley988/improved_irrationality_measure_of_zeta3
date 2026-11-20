import Zeta5.Arithmetic.SmallPrimeProper
import Zeta3.Arithmetic.SmallPrimeQuotient

/-! All-prime cubic proper-fraction bounds, including the actual cubic
harmonic sum and the constant quotient. The final loss is conservatively
weakened to the same fixed factor24 used by the manuscript. -/
noncomputable section
namespace Zeta3.Arithmetic
open Polynomial Finset OddZeta.FourValue Zeta5.Construction
open Zeta5.Arithmetic
variable {p : ℕ} [Fact p.Prime]

lemma harmonicThree_padicLower_log (n D : ℕ) (hnD : n ≤ D) :
    PadicLower p (-3*(Nat.log p D : ℤ)) (Zeta3.Construction.harmonicThree n) := by
  unfold Zeta3.Construction.harmonicThree
  apply padicLower_sum
  intro i hi
  exact reciprocalPower_padicLower_log (i+1) 3 D (by have := mem_range.mp hi; omega)

theorem stieltjes_polynomial_padicLower_log (i D : ℕ) (hiD : i ≤ D) :
    PolynomialPadicLower p (-3*(Nat.log p D : ℤ)-2*(padicValNat p 2 : ℤ)) (Zeta3.Construction.stieltjes i) := by
  have hL : (0 : ℤ) ≤ Nat.log p D := by positivity
  have h2 : (0 : ℤ) ≤ padicValNat p 2 := by positivity
  have hi4 : PadicLower p 0 ((i : ℚ)^2) := by
    right
    rw [padicValRat.pow, padicValRat.of_nat]
    positivity
  have hprod := (hi4.neg).mul (harmonicThree_padicLower_log (i-1) D (by omega))
  have hrec : PadicLower p (-(padicValNat p 2 : ℤ)-(Nat.log p D : ℤ))
      (1/(2*(i : ℚ))) := by
    convert! (inverse_two_exact_lower (p := p)).mul
      (inverse_nat_padicLower_log (p := p) hiD) using 1
    simp [one_div, mul_inv_rev, mul_comm]
  have hquarter : PadicLower p (-2*(padicValNat p 2 : ℤ)) (1/2 : ℚ) := by
    simpa only [one_div] using (inverse_two_exact_lower (p := p)).mono
      (show -2*(padicValNat p 2 : ℤ) ≤ -(padicValNat p 2 : ℤ) by omega)
  have hc : PadicLower p (-3*(Nat.log p D : ℤ)-2*(padicValNat p 2 : ℤ))
      (Zeta3.Construction.stieltjesConstant i) := by
    have hp' := hprod.mono (show -3*(Nat.log p D : ℤ)-2*(padicValNat p 2 : ℤ) ≤
      0 + -3*(Nat.log p D : ℤ) by omega)
    have hr' := hrec.mono (show -3*(Nat.log p D : ℤ)-2*(padicValNat p 2 : ℤ) ≤
      -(padicValNat p 2 : ℤ)-(Nat.log p D : ℤ) by omega)
    have hq' := hquarter.mono (show -3*(Nat.log p D : ℤ)-2*(padicValNat p 2 : ℤ) ≤
      -2*(padicValNat p 2 : ℤ) by omega)
    simpa only [Zeta3.Construction.stieltjesConstant, sub_eq_add_neg] using (hp'.add hr'.neg).add hq'.neg
  exact (PolynomialPadicLower.constant hc).add ((stieltjes_linear_integral i).mono (by omega))

lemma scaledCentralResidue_padicLower_log (N l i D : ℕ)
    (hi : 0 < i) (hiN : i ≤ N) (hND : 2*N ≤ D) :
    PolynomialPadicLower p (-9*(Nat.log p D : ℤ)-(padicValNat p 24 : ℤ))
      (C ((scaledCentralNumerator N l).eval (pole i)/
        (denominator N).derivative.eval (pole i))*Zeta3.Construction.stieltjes i) := by
  have hv : PadicLower p (-(padicValNat p 2 : ℤ))
      ((centralPolynomial l).eval ((i : ℚ)^2)) := by
    simpa only [Int.cast_natCast] using centralPolynomial_square_padicLower (p := p) l (i : ℤ)
  have hscaled := (factorialScaledDerivativeInverse_padicLower_log N i D hi hiN hND).mul hv
  have he : (scaledCentralNumerator N l).eval (pole i)/(denominator N).derivative.eval (pole i) =
      ((Nat.factorial N : ℚ)^2/(denominator N).derivative.eval (pole i))*
        (centralPolynomial l).eval ((i : ℚ)^2) := by
    simp only [scaledCentralNumerator, windowBasis, eval_mul, eval_C, eval_comp,
      eval_neg, eval_X, pole, neg_neg]
    ring
  rw [he]
  have h := (PolynomialPadicLower.constant hscaled).mul
    (stieltjes_polynomial_padicLower_log i D (by omega))
  apply h.mono
  have hL : (0 : ℤ) ≤ Nat.log p D := by positivity
  have h3 : (0 : ℤ) ≤ padicValNat p 3 := by positivity
  rw [padicValNat_twentyFour]
  simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat]
  omega

lemma polynomialMoment_C (a : ℚ) : Zeta3.Construction.polynomialMoment (C a) = a*Zeta3.Construction.rationalMoment 0 := by
  simp [Zeta3.Construction.polynomialMoment, Polynomial.sum_C_index]

lemma rationalMoment_zero_padicLower :
    PadicLower p (-(padicValNat p 24 : ℤ)) (Zeta3.Construction.rationalMoment 0) := by
  have h24 : PadicLower p (-(padicValNat p 24 : ℤ)) ((24 : ℚ)⁻¹) := by
    right
    rw [padicValRat.inv]
    change -(padicValNat p 24 : ℤ) ≤ -padicValRat p ((24 : ℕ) : ℚ)
    rw [padicValRat.of_nat]
  have h := (padicLower_nat (p := p) 6).mul h24
  rw [Zeta3.Construction.rationalMoment_zero]
  norm_num at h ⊢
  exact h

lemma scaledCentralQuotientMoment_padicLower_log (N l D : ℕ)
    (hlN : l ≤ N) (hND : 2*N ≤ D) :
    PadicLower p (-9*(Nat.log p D : ℤ)-(padicValNat p 24 : ℤ))
      (Zeta3.Construction.polynomialMoment (scaledCentralNumerator N l/denominator N)) := by
  rcases hlN.eq_or_lt with heq | hlN
  · subst l
    rw [scaledCentralQuotient_diagonal, polynomialMoment_C]
    have hr := factorialRatio_padicLower_log (p := p) N N D le_rfl hND
    simp only [Nat.sub_self, Nat.factorial_zero, Nat.cast_one, one_mul,
      show N+N = 2*N by omega] at hr
    have h := ((sign_prime_integral (p := p) N).mul hr).mul
      (rationalMoment_zero_padicLower (p := p))
    apply h.mono
    have hL : (0 : ℤ) ≤ Nat.log p D := by positivity
    omega
  · rw [scaledCentralQuotient_zero N l hlN]
    simp [Zeta3.Construction.polynomialMoment, PadicLower]

theorem numeratorFunctional_scaledCentral_proper_padicLower_log (N l D : ℕ)
    (hlN : l ≤ N) (hND : 2*N ≤ D) :
    PolynomialPadicLower p (-9*(Nat.log p D : ℤ)-(padicValNat p 24 : ℤ))
      (Zeta3.Construction.numeratorFunctional N (scaledCentralNumerator N l)) := by
  rw [Zeta3.Construction.numeratorFunctional_apply]
  apply (PolynomialPadicLower.constant (scaledCentralQuotientMoment_padicLower_log N l D hlN hND)).add
  apply PolynomialPadicLower.sum
  intro i hi
  exact scaledCentralResidue_padicLower_log N l (i+1) D (by omega)
    (by simpa using mem_range.mp hi) hND

end Zeta3.Arithmetic

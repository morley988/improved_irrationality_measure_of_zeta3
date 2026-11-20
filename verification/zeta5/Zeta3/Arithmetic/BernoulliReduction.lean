import Zeta3.Arithmetic.LocalPrecision
import Zeta3.Arithmetic.LocalUnitReduction

/-! Passing congruences through the single derivative and Bernoulli
functional. The high coefficients retain their Newton precision, so the
possible Bernoulli denominator at large degree is accounted for. -/
noncomputable section
namespace Zeta3.Arithmetic
open Polynomial Finset OddZeta.FourValue Zeta5.Arithmetic
variable {p : ℕ} [Fact p.Prime]

theorem bernoulliFunctional_derivative_integral_congruence
    (P R : ℚ[X]) (E : ℕ) (hp : 2 < p) (hE : E + 3 ≤ p)
    (hP : ∀ j : ℕ, PadicLower p (max 0 ((j : ℤ) - E)) (P.coeff j))
    (hR : R.natDegree ≤ p - 1)
    (hcongr : ∀ j, 0 < j → PadicLower p 1 (P.coeff j - R.coeff j)) :
    PadicLower p 1 (bernoulliFunctional P.derivative - bernoulliFunctional R.derivative) := by
  rw [← map_sub, ← derivative_sub, bernoulliFunctional_derivative_eq_sum]
  apply padicLower_sum
  intro j hj
  rw [coeff_sub]
  by_cases hj0 : j = 0
  · subst j
    simp only [Nat.cast_zero, mul_zero, zero_mul]
    exact PadicLower.zero _
  by_cases hjp : j < p
  · have h := ((hcongr j (by omega)).mul (padicLower_nat (p := p) j)).mul
      (bernoulli_integral_of_lt (p := p) (j - 1) hp (by omega))
    exact h.mono (by norm_num)
  · have hRzero : R.coeff j = 0 := coeff_eq_zero_of_natDegree_lt (by omega)
    rw [hRzero, sub_zero]
    have h := ((hP j).mul (padicLower_nat (p := p) j)).mul (bernoulli_padicLower (p := p) (j - 1) hp)
    exact h.mono (by omega)

theorem bernoulliFunctional_derivative_zero_of_constant_reduction
    (P : ℚ[X]) (E : ℕ) (hp : 2 < p) (hE : E + 3 ≤ p)
    (hP : ∀ j : ℕ, PadicLower p (max 0 ((j : ℤ) - E)) (P.coeff j))
    (hcongr : ∀ j, 0 < j → PadicLower p 1 (P.coeff j)) :
    PadicLower p 1 (bernoulliFunctional P.derivative) := by
  have h := bernoulliFunctional_derivative_integral_congruence P 0 E hp hE hP
    (by simp) (by simpa using hcongr)
  simpa only [derivative_zero, map_zero, sub_zero] using h

theorem polynomialPadicLower_pow_sub_pow {F G : ℚ[X]}
    (hF : PolynomialPadicLower p 0 F) (hG : PolynomialPadicLower p 0 G)
    (hFG : PolynomialPadicLower p 1 (F - G)) (n : ℕ) :
    PolynomialPadicLower p 1 (F ^ n - G ^ n) := by
  induction n with
  | zero => simpa using (PolynomialPadicLower.zero (p := p) 1)
  | succ n ih =>
    have h₁ : PolynomialPadicLower p 1 (F ^ n * (F - G)) := by simpa using (hF.pow n).mul hFG
    have h₂ : PolynomialPadicLower p 1 ((F ^ n - G ^ n) * G) := by simpa using ih.mul hG
    have he : F ^ (n + 1) - G ^ (n + 1) = F ^ n * (F - G) + (F ^ n - G ^ n) * G := by ring
    rw [he]
    exact h₁.add h₂

theorem localAffine_pow_sub_constant (c : ℤ) (n : ℕ) :
    PolynomialPadicLower p 1 ((localAffine p c) ^ n - C ((c : ℚ) ^ n)) := by
  have hbase : PolynomialPadicLower p 1 (localAffine p c - C (c : ℚ)) := by
    have he : localAffine p c - C (c : ℚ) = C (p : ℚ) * X := by unfold localAffine; ring
    rw [he]
    have hp1 : PadicLower p 1 (p : ℚ) := by simpa using prime_power_padicLower (p := p) 1
    simpa using (PolynomialPadicLower.constant hp1).mul polynomialPadicLower_X
  simpa only [map_pow] using polynomialPadicLower_pow_sub_pow (localAffine_integral c)
    (PolynomialPadicLower.constant (padicLower_int c)) hbase n

theorem localCubicProduct_constant_reduction {Q : ℚ[X]} {a : ℚ} (c : ℤ)
    (hQ : PolynomialPadicLower p 0 Q) (ha : PadicLower p 0 a)
    (hQa : PolynomialPadicLower p 1 (Q - C a)) :
    PolynomialPadicLower p 1 ((localAffine p c) ^ 3 * Q - C ((c : ℚ) ^ 3 * a)) := by
  have h₁ : PolynomialPadicLower p 1 (((localAffine p c) ^ 3 - C ((c : ℚ) ^ 3)) * Q) := by
    simpa using (localAffine_pow_sub_constant (p := p) c 3).mul hQ
  have hc3 : PadicLower p 0 ((c : ℚ) ^ 3) := by
    have he : ((c ^ 3 : ℤ) : ℚ) = (c : ℚ) ^ 3 := by norm_cast
    rw [← he]
    exact padicLower_int (p := p) (c ^ 3)
  have h₂ : PolynomialPadicLower p 1 (C ((c : ℚ) ^ 3) * (Q - C a)) := by
    simpa using (PolynomialPadicLower.constant hc3).mul hQa
  have he : (localAffine p c) ^ 3 * Q - C ((c : ℚ) ^ 3 * a) =
      ((localAffine p c) ^ 3 - C ((c : ℚ) ^ 3)) * Q + C ((c : ℚ) ^ 3) * (Q - C a) := by
    rw [C_mul]; ring
  rw [he]
  exact h₁.add h₂

end Zeta3.Arithmetic

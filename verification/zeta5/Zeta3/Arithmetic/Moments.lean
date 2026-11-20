import Zeta3.Construction.Functional
import Zeta5.Arithmetic.Moments
import Zeta5.Arithmetic.StieltjesValuations

/-!
# Cubic Bernoulli moments and their genuine local denominator threshold

Von Staudt--Clausen gives a one-prime loss for every actual cubic moment.
The first possible Bernoulli pole is canceled by the single numerator
factor `2k+3`. Thus all moments through index `p-3` are integral at an odd
prime. The threshold is `p-2`, as needed for the cubic terminal quotient
block; the longer quintic integrality range is not reused.
-/

noncomputable section
namespace Zeta3.Arithmetic
open Polynomial OddZeta.FourValue Zeta3.Construction
open Zeta5.Arithmetic

variable {p : ℕ} [Fact p.Prime]

theorem rationalMoment_factorization (k : ℕ) :
    rationalMoment k = (-1 : ℚ) ^ k * (1 / 2) * ((2 * k + 3 : ℕ) : ℚ) *
      bernoulli (2 * (k + 1)) := by
  have he : 2 * (k + 1) = 2 * k + 2 := by omega
  simp only [rationalMoment, he]
  push_cast
  ring

theorem rationalMoment_padicLower (k : ℕ) (hp : 2 < p) :
    PadicLower p (-1) (rationalMoment k) := by
  rw [rationalMoment_factorization]
  have h := (((sign_prime_integral (p := p) k).mul (half_integral hp)).mul
    (padicLower_nat (p := p) (2 * k + 3))).mul
      (bernoulli_even_padicLower (p := p) (k + 1))
  simpa using h

omit [Fact p.Prime] in
theorem prime_dvd_cubicMomentNumerator (k : ℕ) (hp : 2 < p) (hk : k < p - 2)
    (hd : (p - 1) ∣ 2 * (k + 1)) : p ∣ 2 * k + 3 := by
  obtain ⟨a, ha⟩ := hd
  have ha1 : 1 ≤ a := by
    by_contra h
    have : a = 0 := by omega
    simp [this] at ha
  have ha2 : a < 2 := by
    by_contra h
    have ham := Nat.mul_le_mul_left (p - 1) (show 2 ≤ a by omega)
    omega
  have haeq : a = 1 := by omega
  rw [haeq, mul_one] at ha
  have he : 2 * k + 3 = p := by omega
  rw [he]

theorem rationalMoment_integral_of_lt (k : ℕ) (hp : 2 < p) (hk : k < p - 2) :
    PadicLower p 0 (rationalMoment k) := by
  rw [rationalMoment_factorization]
  have hsign := (sign_prime_integral (p := p) k).mul (half_integral hp)
  by_cases hd : (p - 1) ∣ 2 * (k + 1)
  · have hn := padicLower_nat_of_dvd (p := p) (2 * k + 3)
      (prime_dvd_cubicMomentNumerator k hp hk hd)
    simpa using (hsign.mul hn).mul (bernoulli_even_padicLower (p := p) (k + 1))
  · simpa using (hsign.mul (padicLower_nat (p := p) (2 * k + 3))).mul
      (bernoulli_even_integral_of_not_dvd (p := p) (k + 1) hd)

theorem polynomialMoment_weighted_lower {P : ℚ[X]} {w : ℤ} (hp : 2 < p)
    (hP : PolynomialPadicLower p w P) : PadicLower p (w - 1) (polynomialMoment P) := by
  unfold polynomialMoment
  rw [Polynomial.sum_def]
  apply padicLower_sum
  intro k hk
  simpa only [sub_eq_add_neg] using (hP k).mul (rationalMoment_padicLower (p := p) k hp)

theorem polynomialMoment_integral_of_degree_lt (P : ℚ[X]) (hp : 2 < p)
    (hP : PolynomialPadicLower p 0 P) (hdeg : P.natDegree < p - 2) :
    PadicLower p 0 (polynomialMoment P) := by
  unfold polynomialMoment
  rw [Polynomial.sum_def]
  apply padicLower_sum
  intro k hk
  have hkdeg : k ≤ P.natDegree := le_natDegree_of_ne_zero (mem_support_iff.mp hk)
  simpa using (hP k).mul
    (rationalMoment_integral_of_lt (p := p) k hp (hkdeg.trans_lt hdeg))

end Zeta3.Arithmetic

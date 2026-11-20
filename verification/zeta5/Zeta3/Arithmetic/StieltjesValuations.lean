import Zeta3.Arithmetic.Moments

/-!
# Valuations of the actual cubic Stieltjes polynomials

The cubic harmonic sum costs at most three prime powers below the prime
square. At physical multiples of the prime, its coefficient `i²` restores
two powers, leaving the one-power loss used for the zero class.
-/

noncomputable section
namespace Zeta3.Arithmetic
open Polynomial OddZeta.FourValue Zeta3.Construction
open Zeta5.Arithmetic
variable {p : ℕ} [Fact p.Prime]

theorem harmonicThree_padicLower (n : ℕ) (hn : n < p ^ 2) :
    PadicLower p (-3) (harmonicThree n) := by
  unfold harmonicThree
  apply padicLower_sum
  intro k hk
  exact reciprocalPower_padicLower (k + 1) 3 (by omega)
    (lt_of_le_of_lt (by simpa using Finset.mem_range.mp hk) hn)

theorem harmonicThree_integral (n : ℕ) (hn : n < p) :
    PadicLower p 0 (harmonicThree n) := by
  unfold harmonicThree
  apply padicLower_sum
  intro k hk
  exact reciprocalPower_integral (k + 1) 3
    (lt_of_le_of_lt (by simpa using Finset.mem_range.mp hk) hn)

theorem stieltjesConstant_padicLower (i : ℕ) (hp : 2 < p) (hi : 0 < i)
    (hi2 : i < p ^ 2) : PadicLower p (-3) (stieltjesConstant i) := by
  have hi2p : PadicLower p 0 ((i : ℚ) ^ 2) := by
    right
    rw [padicValRat.pow, padicValRat.of_nat]
    positivity
  have hprod := hi2p.neg.mul (harmonicThree_padicLower (i - 1) (by omega : i - 1 < p ^ 2))
  have hrecip := (reciprocalTwiceNat_padicLower i hp hi hi2).mono (by omega : (-3 : ℤ) ≤ -1)
  have hhalf := (half_integral (p := p) hp).mono (by omega : (-3 : ℤ) ≤ 0)
  simpa only [stieltjesConstant, sub_eq_add_neg, zero_add] using
    (hprod.add hrecip.neg).add hhalf.neg

theorem stieltjesConstant_integral (i : ℕ) (hp : 2 < p) (hip : i < p) :
    PadicLower p 0 (stieltjesConstant i) := by
  have hi2p : PadicLower p 0 ((i : ℚ) ^ 2) := by
    right
    rw [padicValRat.pow, padicValRat.of_nat]
    positivity
  have hprod := hi2p.neg.mul (harmonicThree_integral (i - 1) (by omega : i - 1 < p))
  have hrecip := reciprocalTwiceNat_integral i hp hip
  have hhalf := half_integral (p := p) hp
  simpa only [stieltjesConstant, sub_eq_add_neg, zero_add] using
    (hprod.add hrecip.neg).add hhalf.neg

theorem stieltjesConstant_multiple_p (i : ℕ) (hp : 2 < p) (hi : 0 < i)
    (hi2 : i < p ^ 2) (hpi : p ∣ i) : PadicLower p (-1) (stieltjesConstant i) := by
  have hi2p : PadicLower p 2 ((i : ℚ) ^ 2) := by
    right
    rw [padicValRat.pow, padicValRat.of_nat]
    have h := one_le_padicValNat_of_dvd (Nat.ne_of_gt hi) hpi
    omega
  have hprod := hi2p.neg.mul (harmonicThree_padicLower (i - 1) (by omega : i - 1 < p ^ 2))
  have hrecip := reciprocalTwiceNat_padicLower i hp hi hi2
  have hhalf := (half_integral (p := p) hp).mono (by omega : (-1 : ℤ) ≤ 0)
  simpa only [stieltjesConstant, sub_eq_add_neg, show (2 : ℤ) + -3 = -1 from rfl] using
    (hprod.add hrecip.neg).add hhalf.neg

theorem stieltjes_linear_integral (i : ℕ) :
    PolynomialPadicLower p 0 (X * C ((i : ℚ) ^ 2)) := by
  simpa using (polynomialPadicLower_X (p := p)).mul
    (PolynomialPadicLower.constant (show PadicLower p 0 ((i : ℚ) ^ 2) by
      right
      rw [padicValRat.pow, padicValRat.of_nat]
      positivity))

theorem stieltjes_polynomial_padicLower (i : ℕ) (hp : 2 < p) (hi : 0 < i)
    (hi2 : i < p ^ 2) : PolynomialPadicLower p (-3) (stieltjes i) :=
  (PolynomialPadicLower.constant (stieltjesConstant_padicLower i hp hi hi2)).add
    ((stieltjes_linear_integral i).mono (by omega))

theorem stieltjes_polynomial_integral (i : ℕ) (hp : 2 < p) (hip : i < p) :
    PolynomialPadicLower p 0 (stieltjes i) :=
  (PolynomialPadicLower.constant (stieltjesConstant_integral i hp hip)).add
    (stieltjes_linear_integral i)

theorem stieltjes_polynomial_multiple_p (i : ℕ) (hp : 2 < p) (hi : 0 < i)
    (hi2 : i < p ^ 2) (hpi : p ∣ i) : PolynomialPadicLower p (-1) (stieltjes i) :=
  (PolynomialPadicLower.constant (stieltjesConstant_multiple_p i hp hi hi2 hpi)).add
    ((stieltjes_linear_integral i).mono (by omega))

end Zeta3.Arithmetic

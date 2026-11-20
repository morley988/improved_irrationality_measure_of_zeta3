import Zeta3.Arithmetic.BernoulliMoments
import Zeta5.Arithmetic.LocalNewton

/-!
# Full local coefficient precision for integer-valued polynomials

The old generic Newton calculation is strengthened from divisibility by one
prime above the reduction degree to the exact lower bound
`max(0, j-floor(L/p))`. This is the precision needed before the single
cubic derivative and Bernoulli evaluation.
-/

noncomputable section
namespace Zeta3.Arithmetic
open Polynomial Finset OddZeta.FourValue Zeta5.Arithmetic
variable {p : ℕ} [Fact p.Prime]

theorem local_binomialPolynomial_coeff_precision {n : ℕ} (hn : n < p ^ 2)
    (c : ℤ) (j : ℕ) :
    PadicLower p ((j : ℤ) - (n / p : ℕ))
      (((binomialPolynomial n).comp (localAffine p c)).coeff j) := by
  rw [binomialPolynomial, mul_comp, C_comp, coeff_C_mul]
  have h := (inverse_factorial_padicLower hn).mul (local_descPochhammer_coeff n c j)
  convert h using 1
  omega

theorem integerValuedAt_local_coeff_precision {g : ℚ[X]} {L : ℕ}
    (hg : IntegerValuedAt p g) (hL : g.natDegree ≤ L) (hLp : L < p ^ 2)
    (c : ℤ) (j : ℕ) :
    PadicLower p (max 0 ((j : ℤ) - (L / p : ℕ))) ((g.comp (localAffine p c)).coeff j) := by
  have hraw : PadicLower p ((j : ℤ) - (L / p : ℕ))
      ((g.comp (localAffine p c)).coeff j) := by
    rw [← newtonExpansion_eq g hL, newtonExpansion, Polynomial.sum_comp, finsetSum_coeff]
    apply padicLower_sum
    intro a ha
    have haL : a ≤ L := Nat.le_of_lt_succ (mem_range.mp ha)
    rw [mul_comp, C_comp, coeff_C_mul]
    have hv := (newtonCoefficient_padicLower hg a).mul
      (local_binomialPolynomial_coeff_precision (haL.trans_lt hLp) c j)
    have hf : a / p ≤ L / p := Nat.div_le_div_right haL
    exact hv.mono (by omega)
  have hzero := integerValuedAt_local_integral hg hL hLp c j
  by_cases hnonneg : 0 ≤ (j : ℤ) - (L / p : ℕ)
  · simpa only [max_eq_right hnonneg] using hraw
  · simpa only [max_eq_left (le_of_not_ge hnonneg)] using hzero

theorem bernoulli_padicLower (n : ℕ) (hp : 2 < p) :
    PadicLower p (-1) (_root_.bernoulli n) := by
  by_cases hn1 : n = 1
  · subst n
    simpa only [bernoulli_one, neg_div] using
      ((half_integral (p := p) hp).neg.mono (by norm_num : (-1 : ℤ) ≤ 0))
  rcases Nat.even_or_odd n with heven | hodd
  · obtain ⟨k, hk⟩ := heven
    have hn : n = 2 * k := by omega
    rw [hn]
    exact bernoulli_even_padicLower k
  · rw [bernoulli_eq_zero_of_odd hodd (by have := hodd.pos; omega)]
    exact PadicLower.zero _

theorem bernoulli_integral_of_lt (n : ℕ) (hp : 2 < p) (hn : n < p - 1) :
    PadicLower p 0 (_root_.bernoulli n) := by
  by_cases hn0 : n = 0
  · subst n
    simpa only [bernoulli_zero, Nat.cast_one] using (padicLower_nat (p := p) 1)
  by_cases hn1 : n = 1
  · subst n
    simpa only [bernoulli_one, neg_div] using (half_integral (p := p) hp).neg
  rcases Nat.even_or_odd n with heven | hodd
  · obtain ⟨k, hk⟩ := heven
    have hn' : n = 2 * k := by omega
    rw [hn']
    apply bernoulli_even_integral_of_not_dvd
    intro hd
    have hle := Nat.le_of_dvd (show 0 < 2 * k by omega) hd
    omega
  · rw [bernoulli_eq_zero_of_odd hodd (by omega)]
    exact PadicLower.zero _

theorem bernoulliFunctional_derivative_eq_sum (P : ℚ[X]) :
    bernoulliFunctional P.derivative =
      ∑ j ∈ range (P.natDegree + 1), P.coeff j * (j : ℚ) * _root_.bernoulli (j - 1) := by
  conv_lhs => rw [P.as_sum_range_C_mul_X_pow]
  rw [derivative_sum, map_sum]
  simp only [derivative_C_mul_X_pow, bernoulliFunctional_C_mul, bernoulliFunctional_X_pow]

/-- At precision one or two, the high-degree tail may be removed before
one derivative and Bernoulli evaluation. The possible Bernoulli denominator
above degree `p-1` is paid by the proved coefficient precision. -/
theorem bernoulliFunctional_derivative_padicLower_of_precision
    (P : ℚ[X]) (E r : ℕ) (hp : 2 < p) (hE : E + 3 ≤ p) (hr : r ≤ 2)
    (hcoeff : ∀ j : ℕ, PadicLower p (max 0 ((j : ℤ) - E)) (P.coeff j))
    (hvanish : ∀ j : ℕ, j < E + r → P.coeff j = 0) :
    PadicLower p (r : ℤ) (bernoulliFunctional P.derivative) := by
  rw [bernoulliFunctional_derivative_eq_sum]
  apply padicLower_sum
  intro j hj
  by_cases hjlow : j < E + r
  · rw [hvanish j hjlow, zero_mul, zero_mul]
    exact PadicLower.zero _
  have hcoef := hcoeff j
  have hnum := padicLower_nat (p := p) j
  by_cases hjp : j < p
  · have hbern := bernoulli_integral_of_lt (p := p) (j - 1) hp (by omega)
    have h := (hcoef.mul hnum).mul hbern
    exact h.mono (by omega)
  · have hbern := bernoulli_padicLower (p := p) (j - 1) hp
    have h := (hcoef.mul hnum).mul hbern
    exact h.mono (by omega)

def coefficientTruncation (P : ℚ[X]) (d : ℕ) : ℚ[X] :=
  ∑ j ∈ range (d + 1), monomial j (P.coeff j)

@[simp] theorem coefficientTruncation_coeff (P : ℚ[X]) (d j : ℕ) :
    (coefficientTruncation P d).coeff j = if j ≤ d then P.coeff j else 0 := by
  simp [coefficientTruncation, finsetSum_coeff, coeff_monomial]

theorem local_derivative_bernoulli_truncation_precision
    {g : ℚ[X]} {L : ℕ} (hg : IntegerValuedAt p g)
    (hL : g.natDegree ≤ L) (hLp : L < p ^ 2) (hp : 2 < p)
    (hE : L / p ≤ p - 3) (c : ℤ) (r : ℕ) (hr : r ≤ 2) :
    PadicLower p (r : ℤ)
      (bernoulliFunctional (g.comp (localAffine p c)).derivative -
        bernoulliFunctional
          (coefficientTruncation (g.comp (localAffine p c)) (L / p + r - 1)).derivative) := by
  rw [← map_sub, ← derivative_sub]
  apply bernoulliFunctional_derivative_padicLower_of_precision _ (L / p) r hp (by omega) hr
  · intro j
    simp only [coeff_sub, coefficientTruncation_coeff]
    split_ifs with hj
    · rw [sub_self]
      exact PadicLower.zero _
    · rw [sub_zero]
      exact integerValuedAt_local_coeff_precision hg hL hLp c j
  · intro j hj
    simp only [coeff_sub, coefficientTruncation_coeff,
      if_pos (show j ≤ L / p + r - 1 by omega), sub_self]

end Zeta3.Arithmetic

import Zeta5.Arithmetic.LowPairs
import Zeta3.Arithmetic.StieltjesReflection
import Zeta3.Arithmetic.ReflectedMinors

/-! Integral cancellation of the actual cubic all-low reflected pair,
with a separate positive common factor from each unequal window. -/
noncomputable section
namespace Zeta3.Arithmetic
open Polynomial OddZeta.FourValue Zeta5.Construction
open Zeta5.Arithmetic
variable {p : ℕ} [Fact p.Prime]

theorem low_reflected_pair_integral (N m₁ m₂ r c : ℕ) (hp : 2 < p)
    (hc : 0 < c) (hcp : 2 * c < p) (hjN : p - c ≤ N)
    (hsmall : 2 * N < p ^ 2) (hcard : (reflectedNodes N p c).card = 2) :
    ∀ k l : Fin r, PolynomialPadicLower p 0
      (mixedMonomialAtom N m₁ m₂ r c k l + mixedMonomialAtom N m₁ m₂ r (p - c) k l) := by
  have hcplt : c < p := by omega
  have hj0 : 0 < p - c := by omega
  have hjplt : p - c < p := by omega
  have hcN : c ≤ N := by omega
  have hci : c ∈ reflectedNodes N p c :=
    mem_reflectedNodes.mpr ⟨hc, hcN, Or.inl (Nat.mod_eq_of_lt hcplt)⟩
  have hji : p - c ∈ reflectedNodes N p c :=
    mem_reflectedNodes.mpr ⟨hj0, hjN, Or.inr (Nat.mod_eq_of_lt hjplt)⟩
  have hsize : reflectedSize N p c = 2 :=
    (reflectedNodes_card N p c hc hcp).symm.trans hcard
  have hdc : padicValRat p ((denominator N).derivative.eval (pole c)) = 1 := by
    rw [denominator_derivative_reflected_valuation N c c (by omega) hc hcp hci (by omega), hsize]
    norm_num
  have hdj : padicValRat p ((denominator N).derivative.eval (pole (p - c))) = 1 := by
    rw [denominator_derivative_reflected_valuation N c (p - c) (by omega) hc hcp hji (by omega), hsize]
    norm_num
  have hdc0 : (denominator N).derivative.eval (pole c) ≠ 0 := by
    simpa only [Nat.sub_add_cancel hc] using
      (denominator_derivative_at_pole_ne_zero (N := N) (i := c - 1) (by omega))
  have hdj0 : (denominator N).derivative.eval (pole (p - c)) ≠ 0 := by
    simpa only [Nat.sub_add_cancel hj0] using
      (denominator_derivative_at_pole_ne_zero (N := N) (i := p - c - 1) (by omega))
  have hcint := pole_padicIntegral (p := p) c
  have hjint := pole_padicIntegral (p := p) (p - c)
  have hdiff : PadicLower p 1 (pole c - pole (p - c)) := by
    simpa only [neg_sub] using (reflected_pole_congr hc hcp hji).neg
  have hne : pole c ≠ pole (p - c) := by
    intro he
    have he' : (c : ℚ) ^ 2 = ((p - c : ℕ) : ℚ) ^ 2 := by simpa [pole] using he
    have he'' := (sq_eq_sq₀ (by positivity : (0 : ℚ) ≤ c)
      (by positivity : (0 : ℚ) ≤ (p - c : ℕ))).mp he'
    have heN : c = p - c := by exact_mod_cast he''
    omega
  have hD : PolynomialPadicLower p 0 (denominator N) := by
    rw [← denominatorInt_map]
    exact polynomialPadicLower_integer_map _
  have hDsum := derivative_sum_padicLower_two (denominator N) (pole c) (pole (p - c))
    hD hcint hjint hne
    (denominator_eval_neg_square_eq_zero hc hcN)
    (denominator_eval_neg_square_eq_zero hj0 hjN) hdiff
  have hinvsum := inverse_sum_integral_of_sum_gain hdc0 hdj0 hdc hdj hDsum
  have hcinv : PadicLower p (-1) ((denominator N).derivative.eval (pole c))⁻¹ := by
    right
    rw [padicValRat.inv, hdc]
  intro k l
  let P : ℚ[X] := Zeta3.Construction.positiveFactor m₁ * Zeta3.Construction.positiveFactor m₂ * X ^ (k.val + l.val)
  have hP : PolynomialPadicLower p 0 P := mixedMonomialNumerator_integral m₁ m₂ k.val l.val
  have hPi := hP.eval_integral hcint
  have hPj := hP.eval_integral hjint
  have hPdiff := padicLower_eval_sub_eval hP hcint hjint hdiff
  have hkj := stieltjes_polynomial_integral (p := p) (p - c) hp hjplt
  have hkdiff : PolynomialPadicLower p 1 (Zeta3.Construction.stieltjes c - Zeta3.Construction.stieltjes (p - c)) := by
    simpa only [neg_sub] using (stieltjes_reflection c (by omega) hc hcp).neg
  have hnumdiff := polynomial_product_difference_integral
    (P.eval (pole c)) (P.eval (pole (p - c))) (Zeta3.Construction.stieltjes c) (Zeta3.Construction.stieltjes (p - c))
    hPi hkj hPdiff hkdiff
  have hv := (PolynomialPadicLower.constant hPj).mul hkj
  have h := polynomial_pair_integral _ _ _ _ hv hnumdiff hcinv hinvsum
  convert h using 1 <;> first | rfl | (simp only [mixedMonomialAtom, mixedMonomialAtomWeight,
    P, eval_mul, eval_pow, eval_X, map_mul, div_eq_mul_inv]; ring)

end Zeta3.Arithmetic

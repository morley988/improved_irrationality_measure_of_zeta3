import Zeta3.Arithmetic.FactorialPrefactor
import Zeta5.Arithmetic.LargePrimes

/-! Above N, actual cubic residues are integral, but the quotient can
still have a fractional terminal block. Its size is retained in the bound. -/
noncomputable section
namespace Zeta3.Arithmetic
open Polynomial OddZeta.FourValue Zeta5.Construction Finset
open Zeta5.Arithmetic Zeta5.Arithmetic.Allocation
variable {p : ℕ} [Fact p.Prime]

theorem reflected_class_integral_above_N (N m₁ m₂ r c : ℕ) (hp : 2 < p)
    (hc : 0 < c) (hcp : 2 * c < p) (hNp : N < p) :
    ∀ k l : Fin r, PolynomialPadicLower p 0 (mixedMonomialReflectedClass N m₁ m₂ r p c k l) := by
  have hsmall : 2 * N < p ^ 2 := by nlinarith
  have hsize : reflectedSize N p c ≤ 2 := by
    simp only [reflectedSize, Nat.div_eq_of_lt hNp, Nat.mod_eq_of_lt hNp, mul_zero, zero_add]
    split_ifs <;> omega
  by_cases htwo : reflectedSize N p c = 2
  · have hci : c ≤ N ∧ p - c ≤ N := by
      simp only [reflectedSize, Nat.div_eq_of_lt hNp, Nat.mod_eq_of_lt hNp,
        mul_zero, zero_add] at htwo
      split_ifs at htwo <;> omega
    have hset : reflectedNodes N p c = {c, p - c} := by
      ext i
      simp only [mem_reflectedNodes, mem_insert, mem_singleton]
      constructor
      · rintro ⟨hi0, hiN, him⟩
        simpa only [Nat.mod_eq_of_lt (hiN.trans_lt hNp)] using him
      · rintro (rfl | rfl)
        · exact ⟨hc, hci.1, Or.inl (Nat.mod_eq_of_lt (hci.1.trans_lt hNp))⟩
        · exact ⟨by omega, hci.2, Or.inr (Nat.mod_eq_of_lt (hci.2.trans_lt hNp))⟩
    have hcard : (reflectedNodes N p c).card = 2 :=
      (reflectedNodes_card N p c hc hcp).trans htwo
    intro k l
    rw [mixedMonomialReflectedClass_eq_sum, hset, sum_pair (by omega : c ≠ p - c), Matrix.add_apply]
    exact low_reflected_pair_integral N m₁ m₂ r c hp hc hcp hci.2 hsmall hcard k l
  · have hle : reflectedSize N p c ≤ 1 := by omega
    intro k l
    rw [mixedMonomialReflectedClass_eq_sum]
    simp only [Matrix.sum_apply]
    apply PolynomialPadicLower.sum
    intro i hi
    obtain ⟨hi0, hiN, _⟩ := mem_reflectedNodes.mp hi
    have hd : padicValRat p ((denominator N).derivative.eval (pole i)) ≤ 0 := by
      rw [denominator_derivative_reflected_valuation N c i (by omega) hc hcp hi (by omega)]
      omega
    have hw := mixedMonomialAtomWeight_bound N m₁ m₂ i 0 0 0 ((positiveFactor_eval_integral (p := p) m₁ i).mul (positiveFactor_eval_integral m₂ i))
      (stieltjes_polynomial_integral i hp (hiN.trans_lt hNp)) hd
    have hx := PolynomialPadicLower.constant
      (padicIntegral_pow (pole_padicIntegral (p := p) i) (k.val + l.val))
    exact hw.mul hx

theorem mixedMonomialPencil_bound_above_N (N m₁ m₂ r : ℕ) (hp : 2 < p)
    (hNp : N < p) :
    PolynomialPadicLower p (-(mixedTerminalSize N m₁ m₂ r p : ℤ))
      (mixedMonomialPencil N m₁ m₂ r).det := by
  have hp0 : 0 < p := by omega
  have hodd : p % 2 = 1 := (Fact.out : p.Prime).mod_two_eq_one_iff_ne_two.mpr (by omega)
  let R : Matrix (Fin r) (Fin r) ℚ[X] :=
    ∑ c : Fin ((p - 1) / 2), mixedMonomialReflectedClass N m₁ m₂ r p (c.val + 1)
  have hR : ∀ i j, PolynomialPadicLower p 0 (R i j) := by
    intro i j
    simp only [R, Matrix.sum_apply]
    apply PolynomialPadicLower.sum
    intro c hc
    exact reflected_class_integral_above_N N m₁ m₂ r (c.val + 1) hp (by omega)
      (by have hc' := c.isLt; omega) hNp i j
  have hQ : MinorLower (p := p) (mixedQuotientPencil N m₁ m₂ r)
      (fun a => -(min a (mixedTerminalSize N m₁ m₂ r p) : ℤ)) := by
    intro a rows cols
    simpa only [Nat.cast_min] using mixedQuotientPencil_minor_padicLower N m₁ m₂ r a hp rows cols
  have h := minorLower_add_integral (p := p) _ R hQ hR r id id
  have heq : mixedQuotientPencil N m₁ m₂ r + R = mixedMonomialPencil N m₁ m₂ r := by
    rw [mixedMonomialPencil_reflected_decomposition N m₁ m₂ r p hp0 hodd,
      zeroClassNodes_empty_above_N N p hNp, sum_empty, add_zero]
  rw [heq, Matrix.submatrix_id_id] at h
  have ht : mixedTerminalSize N m₁ m₂ r p ≤ r := min_le_left _ _
  simpa only [min_eq_right (show (mixedTerminalSize N m₁ m₂ r p : ℤ) ≤ r by exact_mod_cast ht)] using h

theorem windowDeterminant_largePrime_bound (n : ℕ) (hn : 0 < n) (hNp : 50 * n < p) :
    PolynomialPadicLower p
      (-factorialCharge (50 * n) (4 * n) (16 * n) (51 * n) p -
        (mixedTerminalSize (50 * n) (4 * n) (16 * n) (51 * n) p : ℤ))
      (Zeta3.Construction.windowDeterminant n) := by
  have hp : 2 < p := by omega
  have hlarge : 134 * n < p ^ 2 := by
    have hs : (50 * n + 1) ^ 2 ≤ p ^ 2 := Nat.pow_le_pow_left (by omega) 2
    nlinarith
  have hM := mixedMonomialPencil_bound_above_N (p := p) (50 * n) (4 * n) (16 * n) (51 * n) hp hNp
  rw [mixedMonomialPencil_concrete] at hM
  simpa only [sub_eq_add_neg] using windowDeterminant_padicLower_of_hankel n _ hlarge hM

theorem windowDeterminant_integral_above_window (n : ℕ) (hn : 0 < n) (hp : 134 * n < p) :
    PolynomialPadicLower p 0 (Zeta3.Construction.windowDeterminant n) := by
  have hcharge : factorialCharge (50 * n) (4 * n) (16 * n) (51 * n) p = 0 := by
    unfold factorialCharge
    have hN : 50 * n < p := by omega
    rw [Nat.div_eq_of_lt hN]
    have he₁ : ∀ k : Fin (51 * n), (2 * (4 * n + k.val)) / p = 0 := by
      intro k
      exact Nat.div_eq_of_lt (by have hk := k.isLt; omega)
    have he₂ : ∀ k : Fin (51 * n), (2 * (16 * n + k.val)) / p = 0 := by
      intro k
      exact Nat.div_eq_of_lt (by have hk := k.isLt; omega)
    simp only [he₁, he₂, Nat.cast_zero, sum_const_zero, mul_zero, sub_zero, zero_add]
  have ht : mixedTerminalSize (50 * n) (4 * n) (16 * n) (51 * n) p = 0 := by
    rw [mixedTerminalSize_concrete]
    omega
  simpa only [hcharge, ht, Nat.cast_zero, neg_zero, sub_zero] using
    windowDeterminant_largePrime_bound (p := p) n hn (by omega)

end Zeta3.Arithmetic

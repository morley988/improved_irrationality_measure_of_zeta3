import Zeta3.Arithmetic.QuotientSupport
import Zeta3.Arithmetic.StieltjesValuations
import Zeta5.Arithmetic.ReflectedWeights

/-! Exact positive monomial pencil and residue decomposition for the two
cubic windows. Each common factor is counted separately. -/
noncomputable section
namespace Zeta3.Arithmetic
open Polynomial Finset OddZeta.FourValue Zeta5.Construction Zeta3.Construction
open Zeta5.Arithmetic

variable {p : ℕ} [Fact p.Prime]

def mixedMonomialPencil (N m₁ m₂ r : ℕ) : Matrix (Fin r) (Fin r) ℚ[X] :=
  fun i j => Zeta3.Construction.numeratorFunctional N
    (positiveFactor m₁ * positiveFactor m₂ * X ^ (i.val + j.val))

def mixedMonomialAtomWeight (N m₁ m₂ i : ℕ) : ℚ[X] :=
  C ((positiveFactor m₁).eval (pole i) * (positiveFactor m₂).eval (pole i) /
    (denominator N).derivative.eval (pole i)) * Zeta3.Construction.stieltjes i

def mixedMonomialAtom (N m₁ m₂ r i : ℕ) : Matrix (Fin r) (Fin r) ℚ[X] :=
  fun k l => mixedMonomialAtomWeight N m₁ m₂ i * C ((pole i) ^ (k.val + l.val))

theorem mixedMonomialPencil_residue_decomposition (N m₁ m₂ r : ℕ) :
    mixedMonomialPencil N m₁ m₂ r = mixedQuotientPencil N m₁ m₂ r +
      ∑ i ∈ Finset.range N, mixedMonomialAtom N m₁ m₂ r (i + 1) := by
  funext k l
  simp only [mixedMonomialPencil, Zeta3.Construction.numeratorFunctional_apply,
    Matrix.add_apply, Matrix.sum_apply, mixedQuotientPencil, mixedMonomialAtom,
    mixedQuotientMoment_eq_actual, mixedMonomialAtomWeight]
  congr 1
  apply Finset.sum_congr rfl
  intro i hi
  simp only [eval_mul, eval_pow, eval_X, div_eq_mul_inv, map_mul]
  ring

theorem mixedMonomialPencil_concrete (n : ℕ) :
    mixedMonomialPencil (50 * n) (4 * n) (16 * n) (51 * n) = hankelPencil n := rfl

theorem positiveFactor_eval_eq_integer (m i : ℕ) :
    (positiveFactor m).eval (pole i) =
      (((commonRootInt m).eval (-((i : ℤ) ^ 2)) : ℤ) : ℚ) := by
  rw [← commonRootInt_map]
  have he : pole i = (Int.castRingHom ℚ) (-((i : ℤ) ^ 2)) := by simp [pole]
  rw [he, eval_map_apply]
  rfl

theorem positiveFactor_eval_integral (m i : ℕ) :
    PadicLower p 0 ((positiveFactor m).eval (pole i)) := by
  rw [positiveFactor_eval_eq_integer]
  exact padicLower_int _

theorem positiveFactor_eval_gain {m c i : ℕ} (hc : c < m)
    (hcongr : (p : ℤ) ∣ (c : ℤ) ^ 2 - (i : ℤ) ^ 2) :
    PadicLower p 1 ((positiveFactor m).eval (pole i)) := by
  rw [positiveFactor_eval_eq_integer]
  exact padicLower_int_of_dvd _ (commonRootInt_eval_dvd hc hcongr)

theorem mixedMonomialNumerator_integral (m₁ m₂ k l : ℕ) :
    PolynomialPadicLower p 0 (positiveFactor m₁ * positiveFactor m₂ * X ^ (k + l)) := by
  have h := polynomialPadicLower_integer_map (p := p) (mixedMonomialNumeratorInt m₁ m₂ k l)
  simpa only [mixedMonomialNumeratorInt, Polynomial.map_mul, Polynomial.map_pow,
    Polynomial.map_X, commonRootInt_map] using h

theorem mixedMonomialAtomWeight_bound (N m₁ m₂ i : ℕ) (gain cost v : ℤ)
    (hroot : PadicLower p gain
      ((positiveFactor m₁).eval (pole i) * (positiveFactor m₂).eval (pole i)))
    (hkernel : PolynomialPadicLower p cost (Zeta3.Construction.stieltjes i))
    (hden : padicValRat p ((denominator N).derivative.eval (pole i)) ≤ v) :
    PolynomialPadicLower p (gain - v + cost) (mixedMonomialAtomWeight N m₁ m₂ i) := by
  have hinv : PadicLower p (-v) (((denominator N).derivative.eval (pole i))⁻¹) := by
    right
    rw [padicValRat.inv]
    exact neg_le_neg hden
  have hscalar := hroot.mul hinv
  simpa only [mixedMonomialAtomWeight, div_eq_mul_inv, sub_eq_add_neg] using
    (PolynomialPadicLower.constant hscalar).mul hkernel

def reflectedRootGain (m₁ m₂ c : ℕ) : ℕ :=
  (if c < m₁ then 1 else 0) + (if c < m₂ then 1 else 0)

theorem reflectedRootGain_le_two (m₁ m₂ c : ℕ) : reflectedRootGain m₁ m₂ c ≤ 2 := by
  unfold reflectedRootGain
  split_ifs <;> omega

theorem mixedRoot_reflected_gain {N m₁ m₂ c i : ℕ}
    (hc : 0 < c) (hcp : 2 * c < p) (hi : i ∈ reflectedNodes N p c) :
    PadicLower p (reflectedRootGain m₁ m₂ c)
      ((positiveFactor m₁).eval (pole i) * (positiveFactor m₂).eval (pole i)) := by
  have hcongr := reflected_square_congr hc hcp hi
  have hroot (m : ℕ) : PadicLower p (if c < m then 1 else 0)
      ((positiveFactor m).eval (pole i)) := by
    by_cases hm : c < m
    · simpa only [if_pos hm] using positiveFactor_eval_gain hm hcongr
    · simpa only [if_neg hm] using positiveFactor_eval_integral (p := p) m i
  simpa only [reflectedRootGain, Nat.cast_add, Nat.cast_ite, Nat.cast_one, Nat.cast_zero] using
    (hroot m₁).mul (hroot m₂)

theorem reflected_stieltjes_bound {N c i : ℕ} (hp : 2 < p)
    (hc : 0 < c) (hcp : 2 * c < p)
    (hi : i ∈ reflectedNodes N p c) (hsmall : i < p ^ 2) :
    PolynomialPadicLower p (-3 * (if p < i then (1 : ℤ) else 0))
      (Zeta3.Construction.stieltjes i) := by
  have hi0 := (mem_reflectedNodes.mp hi).1
  have hni := reflected_node_not_dvd hc hcp hi
  by_cases hhigh : p < i
  · simpa [hhigh] using stieltjes_polynomial_padicLower (p := p) i hp hi0 hsmall
  · have hilow : i < p := by
      have hne : i ≠ p := by intro he; subst i; exact hni (dvd_refl p)
      omega
    simpa [hhigh] using stieltjes_polynomial_integral (p := p) i hp hilow

theorem mixed_reflected_atomWeight_bound (N m₁ m₂ c i : ℕ) (hp : 2 < p)
    (hc : 0 < c) (hcp : 2 * c < p) (hpN : p ≤ N)
    (hi : i ∈ reflectedNodes N p c) (hsmall : N + i < p ^ 2) :
    PolynomialPadicLower p
      ((reflectedRootGain m₁ m₂ c : ℤ) - (highReflectedNodes N p c).card - 1 -
        3 * (if p < i then (1 : ℤ) else 0))
      (mixedMonomialAtomWeight N m₁ m₂ i) := by
  have hd := denominator_derivative_reflected_valuation N c i hp hc hcp hi hsmall
  have hh := highReflectedNodes_card_add_two N p c hc hcp hpN
  have hd' : padicValRat p ((denominator N).derivative.eval (pole i)) ≤
      ((highReflectedNodes N p c).card : ℤ) + 1 := by
    rw [hd, ← hh]
    push_cast
    omega
  have hw := mixedMonomialAtomWeight_bound N m₁ m₂ i (reflectedRootGain m₁ m₂ c)
    (-3 * (if p < i then (1 : ℤ) else 0)) ((highReflectedNodes N p c).card + 1)
    (mixedRoot_reflected_gain hc hcp hi)
    (reflected_stieltjes_bound hp hc hcp hi (by omega)) hd'
  convert hw using 1
  ring

end Zeta3.Arithmetic

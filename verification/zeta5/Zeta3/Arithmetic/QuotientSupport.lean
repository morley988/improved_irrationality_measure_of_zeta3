import Zeta3.Arithmetic.Moments
import Zeta3.Construction.Asymmetric
import Zeta5.Arithmetic.QuotientMinors

/-!
# Actual cubic quotient support for two unequal windows

The integral numerator is `C_m₁ C_m₂ X^(k+l)`. Monic division is performed
over the integers and then mapped to the rational polynomial functional.
The first uncanceled cubic moment pole occurs at index `p-2`, giving the
terminal block `min(r, m₁+m₂+2r+1-N-p)`. Every selected quotient minor loses
at most the smaller of its order and that terminal-block size.
-/

noncomputable section
namespace Zeta3.Arithmetic
open Polynomial Finset OddZeta.FourValue Zeta3.Construction
open Zeta5.Arithmetic

variable {p : ℕ} [Fact p.Prime]

theorem commonRootInt_map (m : ℕ) :
    (commonRootInt m).map (Int.castRingHom ℚ) = positiveFactor m := by
  unfold commonRootInt positiveFactor
  rw [Polynomial.map_prod]
  apply Finset.prod_congr rfl
  intro i hi
  simp

def mixedMonomialNumeratorInt (m₁ m₂ k l : ℕ) : ℤ[X] :=
  commonRootInt m₁ * commonRootInt m₂ * X ^ (k + l)

def mixedMonomialQuotientInt (N m₁ m₂ k l : ℕ) : ℤ[X] :=
  mixedMonomialNumeratorInt m₁ m₂ k l /ₘ denominatorInt N

def mixedQuotientMoment (N m₁ m₂ k l : ℕ) : ℚ :=
  polynomialMoment ((mixedMonomialQuotientInt N m₁ m₂ k l).map (Int.castRingHom ℚ))

theorem mixedMonomialNumeratorInt_natDegree (m₁ m₂ k l : ℕ) :
    (mixedMonomialNumeratorInt m₁ m₂ k l).natDegree = m₁ + m₂ + k + l := by
  rw [mixedMonomialNumeratorInt,
    natDegree_mul ((commonRootInt_monic m₁).mul (commonRootInt_monic m₂)).ne_zero
      (pow_ne_zero _ X_ne_zero),
    natDegree_mul (commonRootInt_monic m₁).ne_zero (commonRootInt_monic m₂).ne_zero,
    commonRootInt_natDegree, commonRootInt_natDegree, natDegree_X_pow]
  omega

theorem mixedMonomialQuotientInt_natDegree (N m₁ m₂ k l : ℕ) :
    (mixedMonomialQuotientInt N m₁ m₂ k l).natDegree = (m₁ + m₂ + k + l) - N := by
  rw [mixedMonomialQuotientInt, natDegree_divByMonic _ (denominatorInt_monic N),
    mixedMonomialNumeratorInt_natDegree, denominatorInt_natDegree]

theorem mixedMonomialQuotientInt_map (N m₁ m₂ k l : ℕ) :
    (mixedMonomialQuotientInt N m₁ m₂ k l).map (Int.castRingHom ℚ) =
      (positiveFactor m₁ * positiveFactor m₂ * X ^ (k + l)) /
        Zeta5.Construction.denominator N := by
  rw [mixedMonomialQuotientInt, Polynomial.map_divByMonic _ (denominatorInt_monic N),
    denominatorInt_map, divByMonic_eq_div _ (Zeta5.Construction.denominator_monic N)]
  congr 1
  simp only [mixedMonomialNumeratorInt, Polynomial.map_mul, Polynomial.map_pow,
    Polynomial.map_X, commonRootInt_map]

theorem mixedQuotientMoment_eq_actual (N m₁ m₂ k l : ℕ) :
    mixedQuotientMoment N m₁ m₂ k l =
      polynomialMoment ((positiveFactor m₁ * positiveFactor m₂ * X ^ (k + l)) /
        Zeta5.Construction.denominator N) := by
  rw [mixedQuotientMoment, mixedMonomialQuotientInt_map]

theorem mixedQuotientMoment_padicLower (N m₁ m₂ k l : ℕ) (hp : 2 < p) :
    PadicLower p (-1) (mixedQuotientMoment N m₁ m₂ k l) := by
  simpa only [mixedQuotientMoment, zero_sub] using polynomialMoment_weighted_lower (p := p) hp
    (polynomialPadicLower_integer_map (mixedMonomialQuotientInt N m₁ m₂ k l))

theorem mixedQuotientMoment_integral (N m₁ m₂ k l : ℕ) (hp : 2 < p)
    (hindex : m₁ + m₂ + k + l < N + (p - 2)) :
    PadicLower p 0 (mixedQuotientMoment N m₁ m₂ k l) := by
  apply polynomialMoment_integral_of_degree_lt _ hp
    (polynomialPadicLower_integer_map (mixedMonomialQuotientInt N m₁ m₂ k l))
  apply natDegree_map_le.trans_lt
  rw [mixedMonomialQuotientInt_natDegree]
  omega

def mixedTerminalSize (N m₁ m₂ r p : ℕ) : ℕ :=
  min r (m₁ + m₂ + 2 * r + 1 - (N + p))

theorem mixedQuotientMoment_integral_outside_terminal (N m₁ m₂ r k l : ℕ)
    (hp : 2 < p) (hk : k < r) (hl : l < r)
    (houtside : k < r - mixedTerminalSize N m₁ m₂ r p ∨
      l < r - mixedTerminalSize N m₁ m₂ r p) :
    PadicLower p 0 (mixedQuotientMoment N m₁ m₂ k l) := by
  apply mixedQuotientMoment_integral N m₁ m₂ k l hp
  unfold mixedTerminalSize at houtside
  omega

def mixedQuotientPencil (N m₁ m₂ r : ℕ) : Matrix (Fin r) (Fin r) ℚ[X] :=
  fun i j => C (mixedQuotientMoment N m₁ m₂ i.val j.val)

theorem mixedQuotientPencil_minor_padicLower (N m₁ m₂ r a : ℕ) (hp : 2 < p)
    (rows cols : Fin a → Fin r) :
    PolynomialPadicLower p (-(min a (mixedTerminalSize N m₁ m₂ r p) : ℕ))
      ((mixedQuotientPencil N m₁ m₂ r).submatrix rows cols).det := by
  classical
  by_cases hc : Function.Injective cols
  · let bad : Finset (Fin a) := Finset.univ.filter
      (fun j => r - mixedTerminalSize N m₁ m₂ r p ≤ (cols j).val)
    have hb := polynomialDet_terminal_columns
      ((mixedQuotientPencil N m₁ m₂ r).submatrix rows cols) bad
      (fun i j => PolynomialPadicLower.constant
        (mixedQuotientMoment_padicLower N m₁ m₂ (rows i).val (cols j).val hp)) (by
          intro i j hj
          apply PolynomialPadicLower.constant
          apply mixedQuotientMoment_integral_outside_terminal N m₁ m₂ r _ _ hp
            (rows i).isLt (cols j).isLt
          right
          have hn : ¬ r - mixedTerminalSize N m₁ m₂ r p ≤ (cols j).val := by
            simpa only [bad, Finset.mem_filter, Finset.mem_univ, true_and] using hj
          omega)
    have hcard : bad.card ≤ min a (mixedTerminalSize N m₁ m₂ r p) :=
      selected_terminal_card_le cols hc
    have hcast : (bad.card : ℤ) ≤ (min a (mixedTerminalSize N m₁ m₂ r p) : ℕ) := by
      exact_mod_cast hcard
    exact hb.mono (neg_le_neg hcast)
  · obtain ⟨i, j, hij, hne⟩ := Function.not_injective_iff.mp hc
    rw [Matrix.det_zero_of_column_eq hne (fun k => by simp [Matrix.submatrix_apply, hij])]
    exact PolynomialPadicLower.zero _

theorem mixedTerminalSize_concrete (n p : ℕ) :
    mixedTerminalSize (50 * n) (4 * n) (16 * n) (51 * n) p =
      min (51 * n) (72 * n + 1 - p) := by
  unfold mixedTerminalSize
  omega

end Zeta3.Arithmetic

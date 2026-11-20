import Zeta3.Construction.Asymmetric
import Zeta3.Transfer.DefinitePencil
import Zeta3.Transfer.Multiplicity

/-!
# The concrete cubic determinant's multiplicity interface

This module uses the actual asymmetric determinant and its actual primitive
integer normalization. The determinant's scalar factor, the symmetry of the
Hankel pencil, and the transfer from matrix nullity to root multiplicity are
proved here. Positive definiteness at the target and the Pearson nullity
bound remain explicit mathematical hypotheses.
-/

noncomputable section
namespace Zeta3.Transfer
open Polynomial Matrix Module
open Zeta3.Construction

def realHankelConstant (n : ℕ) : Matrix (Fin (51 * n)) (Fin (51 * n)) ℝ :=
  (hankelConstant n).map (Rat.castHom ℝ)

def realHankelLinear (n : ℕ) : Matrix (Fin (51 * n)) (Fin (51 * n)) ℝ :=
  (hankelLinear n).map (Rat.castHom ℝ)

def integerHankelScale (n : ℕ) : ℝ :=
  (windowNormalizer n : ℝ) *
    (factorialPrefactor (50 * n) (4 * n) (16 * n) (51 * n) : ℚ)

theorem integerHankelScale_pos (n : ℕ) : 0 < integerHankelScale n := by
  apply mul_pos
  · exact_mod_cast windowNormalizer_pos n
  · exact_mod_cast factorialPrefactor_pos (50 * n) (4 * n) (16 * n) (51 * n)

theorem realHankelLinear_isHermitian (n : ℕ) : (realHankelLinear n).IsHermitian := by
  apply Matrix.isHermitian_iff_isSymm.mpr
  exact (hankelLinear_isSymm n).map (Rat.castHom ℝ)

theorem windowIntegerPolynomial_eval_eq_hankel_det (n : ℕ) (x : ℝ) :
    ((windowIntegerPolynomial n).map (Int.castRingHom ℝ)).eval x =
      integerHankelScale n * (realHankelConstant n + x • realHankelLinear n).det := by
  rw [Polynomial.eval_map, windowIntegerPolynomial_eval_real,
    concrete_windowDeterminant_change_of_basis, eval₂_mul, eval₂_C,
    hankelPencil_det_eval_real]
  simp only [integerHankelScale, realHankelConstant, realHankelLinear,
    mul_assoc]
  rfl

theorem windowIntegerPolynomial_ne_zero_of_hankel_posDef (n : ℕ) (ξ : ℝ)
    (hG : (realHankelConstant n + ξ • realHankelLinear n).PosDef) :
    windowIntegerPolynomial n ≠ 0 := by
  intro h
  have heval := windowIntegerPolynomial_eval_eq_hankel_det n ξ
  rw [h, Polynomial.map_zero, eval_zero] at heval
  exact (mul_pos (integerHankelScale_pos n) hG.det_pos).ne' heval.symm

theorem windowIntegerPolynomial_rootMultiplicity_eq_hankel_nullity
    (n : ℕ) (ξ x : ℝ)
    (hG : (realHankelConstant n + ξ • realHankelLinear n).PosDef) :
    ((windowIntegerPolynomial n).map (Int.castRingHom ℝ)).rootMultiplicity x =
      finrank ℝ (LinearMap.ker (realHankelConstant n + x • realHankelLinear n).mulVecLin) := by
  exact rootMultiplicity_eq_finrank_ker_of_eval_eq_det
    ((windowIntegerPolynomial n).map (Int.castRingHom ℝ))
    (realHankelConstant n) (realHankelLinear n) ξ x (integerHankelScale n)
    (integerHankelScale_pos n).ne' (realHankelLinear_isHermitian n) hG
    (windowIntegerPolynomial_eval_eq_hankel_det n)

/-- Once the physical positive-definiteness and Pearson nullity statements
are established, the concrete primitive integer polynomial supplies exactly
the bounded rational jets required by the quantitative transfer theorem. -/
theorem windowIntegerPolynomial_hasBoundedRationalJets (ξ : ℝ) (bound : ℕ)
    (hG : ∀ n, (realHankelConstant n + ξ • realHankelLinear n).PosDef)
    (hnullity : ∀ (n : ℕ) (p : ℤ) (q : ℕ), 0 < q →
      finrank ℝ (LinearMap.ker
        (realHankelConstant n + ((p : ℝ) / (q : ℝ)) • realHankelLinear n).mulVecLin) ≤ bound) :
    HasBoundedRationalJets windowIntegerPolynomial bound := by
  apply hasBoundedRationalJets_of_rootMultiplicity_le windowIntegerPolynomial bound
    (fun n => windowIntegerPolynomial_ne_zero_of_hankel_posDef n ξ (hG n))
  intro n p q hq
  rw [windowIntegerPolynomial_rootMultiplicity_eq_hankel_nullity n ξ _ (hG n)]
  exact hnullity n p q hq

end Zeta3.Transfer

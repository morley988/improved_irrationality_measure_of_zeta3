import Zeta3.Analysis.CubicPositivity
import Zeta3.Analysis.DeterminantMajorant

/-!
# The actual normalized cubic polynomial's determinant response

This file proves the exact complex factorization at zeta(3).  The response
matrix is defined from the concrete rational Hankel coefficients and the
already proved positive physical Gram matrix.  No asymptotic estimate is
assumed in this algebraic identification.
-/

noncomputable section
namespace Zeta3.Analysis
open Matrix Polynomial
open Zeta3.Construction Zeta3.Transfer

def complexHankelConstant (n : ℕ) : Matrix (Fin (51 * n)) (Fin (51 * n)) ℂ :=
  (hankelConstant n).map (Rat.castHom ℂ)

def complexHankelLinear (n : ℕ) : Matrix (Fin (51 * n)) (Fin (51 * n)) ℂ :=
  (hankelLinear n).map (Rat.castHom ℂ)

def complexPhysicalGram (n : ℕ) : Matrix (Fin (51 * n)) (Fin (51 * n)) ℂ :=
  complexHankelConstant n + (Zeta5.Endpoint.realZeta 3 : ℂ) • complexHankelLinear n

def responseMatrix (n : ℕ) : Matrix (Fin (51 * n)) (Fin (51 * n)) ℂ :=
  (complexPhysicalGram n)⁻¹ * complexHankelLinear n

def determinantResponse (n : ℕ) (h : ℂ) : ℂ := (1 + h • responseMatrix n).det

theorem windowIntegerPolynomial_eval_complex (n : ℕ) (z : ℂ) :
    (windowIntegerPolynomial n).eval₂ (Int.castRingHom ℂ) z =
      (windowNormalizer n : ℂ) * (windowDeterminant n).eval₂ (Rat.castHom ℂ) z := by
  have h := congrArg (fun P : ℚ[X] => P.eval₂ (Rat.castHom ℂ) z)
    (windowIntegerPolynomial_map n)
  have hh : (Rat.castHom ℂ).comp (algebraMap ℤ ℚ) = Int.castRingHom ℂ := by
    ext k
    simp
  rw [Polynomial.eval₂_map, hh] at h
  simpa using h

theorem windowIntegerPolynomial_eval_complex_eq_hankel_det (n : ℕ) (z : ℂ) :
    (windowIntegerPolynomial n).eval₂ (Int.castRingHom ℂ) z =
      (integerHankelScale n : ℂ) * (complexHankelConstant n + z • complexHankelLinear n).det := by
  rw [windowIntegerPolynomial_eval_complex, concrete_windowDeterminant_change_of_basis,
    eval₂_mul, eval₂_C, hankelPencil_eq_affinePencil]
  rw [show (Zeta5.Analysis.affinePencil (hankelConstant n) (hankelLinear n)).det =
    Zeta5.Analysis.affineDet (hankelConstant n) (hankelLinear n) from rfl,
    Zeta5.Analysis.eval₂_affineDet]
  unfold integerHankelScale complexHankelConstant complexHankelLinear
  simp only [Rat.coe_castHom]
  push_cast
  ring

theorem complexPhysicalGram_eq_real_map (n : ℕ) :
    complexPhysicalGram n =
      (realHankelConstant n + Zeta5.Endpoint.realZeta 3 • realHankelLinear n).map Complex.ofRealHom := by
  ext i j
  simp only [complexPhysicalGram, complexHankelConstant, complexHankelLinear,
    realHankelConstant, realHankelLinear, Matrix.map_apply, Matrix.add_apply,
    Matrix.smul_apply, smul_eq_mul, Rat.coe_castHom]
  change ((hankelConstant n i j : ℚ) : ℂ) + (Zeta5.Endpoint.realZeta 3 : ℂ) *
    ((hankelLinear n i j : ℚ) : ℂ) =
    (((hankelConstant n i j : ℚ) : ℝ) + Zeta5.Endpoint.realZeta 3 *
      ((hankelLinear n i j : ℚ) : ℝ) : ℝ)
  push_cast
  rfl

theorem complexPhysicalGram_det_ne_zero (n : ℕ) : (complexPhysicalGram n).det ≠ 0 := by
  rw [complexPhysicalGram_eq_real_map]
  have h := Complex.ofRealHom.map_det (realHankelConstant n + Zeta5.Endpoint.realZeta 3 • realHankelLinear n)
  change ((realHankelConstant n + Zeta5.Endpoint.realZeta 3 • realHankelLinear n).det : ℂ) =
    ((realHankelConstant n + Zeta5.Endpoint.realZeta 3 • realHankelLinear n).map Complex.ofRealHom).det at h
  rw [← h]
  exact Complex.ofReal_ne_zero.mpr (PhysicalMeasure.realHankel_realZetaThree_posDef n).det_pos.ne'

theorem complexPencil_factorization (n : ℕ) (h : ℂ) :
    complexHankelConstant n + ((Zeta5.Endpoint.realZeta 3 : ℂ) + h) • complexHankelLinear n =
      complexPhysicalGram n * (1 + h • responseMatrix n) := by
  rw [responseMatrix, Matrix.mul_add, Matrix.mul_one, Matrix.mul_smul,
    Matrix.mul_nonsing_inv_cancel_left _ _ (isUnit_iff_ne_zero.mpr (complexPhysicalGram_det_ne_zero n))]
  unfold complexPhysicalGram
  rw [add_smul]
  abel

theorem windowIntegerPolynomial_response_identity (n : ℕ) (h : ℂ) :
    (windowIntegerPolynomial n).eval₂ (Int.castRingHom ℂ) ((Zeta5.Endpoint.realZeta 3 : ℂ) + h) =
      (windowIntegerPolynomial n).eval₂ (Int.castRingHom ℂ) (Zeta5.Endpoint.realZeta 3 : ℂ) *
        determinantResponse n h := by
  rw [windowIntegerPolynomial_eval_complex_eq_hankel_det,
    windowIntegerPolynomial_eval_complex_eq_hankel_det, complexPencil_factorization, Matrix.det_mul]
  change (integerHankelScale n : ℂ) * ((complexPhysicalGram n).det * determinantResponse n h) =
    ((integerHankelScale n : ℂ) * (complexPhysicalGram n).det) * determinantResponse n h
  ring

end Zeta3.Analysis

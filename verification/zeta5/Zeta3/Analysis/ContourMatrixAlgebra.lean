import Zeta3.Analysis.ConcreteResponse

/-!
# Determinant response under a normalized congruence

A basis orthonormal for a positive Gram matrix preserves the determinant
response.  This finite algebra lemma keeps the exact normalizing scale and
requires no numerical or asymptotic premise.
-/

noncomputable section
open Matrix
namespace Zeta3.Analysis

/-- The determinant response is unchanged after normalized Gram congruence. -/
theorem determinant_response_eq_of_congruence {ι : Type*} [Fintype ι] [DecidableEq ι]
    (G B C T : Matrix ι ι ℂ) (s h : ℂ)
    (hG : G.det ≠ 0)
    (hortho : s⁻¹ • (C.transpose * G * C) = 1)
    (hcoef : T = s⁻¹ • (C.transpose * B * C)) :
    (1 + h • T).det = (1 + h • (G⁻¹ * B)).det := by
  have hfactor : G * (1 + h • (G⁻¹ * B)) = G + h • B := by
    rw [Matrix.mul_add, Matrix.mul_one, Matrix.mul_smul,
      Matrix.mul_nonsing_inv_cancel_left _ _ (isUnit_iff_ne_zero.mpr hG)]
  have hcong : s⁻¹ • (C.transpose * (G + h • B) * C) = 1 + h • T := by
    rw [Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.smul_mul, smul_add,
      hortho, hcoef]
    simp only [smul_smul]
    congr 1
    rw [mul_comm]
  have hnorm := congrArg Matrix.det hortho
  have hdet := congrArg Matrix.det hcong
  rw [← hfactor] at hdet
  simp only [Matrix.det_smul, Matrix.det_mul, Matrix.det_transpose, Matrix.det_one] at hnorm hdet
  calc
    (1 + h • T).det = s⁻¹ ^ Fintype.card ι *
        (C.det * (G.det * (1+h • (G⁻¹*B)).det) * C.det) := hdet.symm
    _ = (s⁻¹ ^ Fintype.card ι * (C.det * G.det * C.det)) *
        (1+h • (G⁻¹*B)).det := by ring
    _ = (1+h • (G⁻¹*B)).det := by rw [hnorm,one_mul]

end Zeta3.Analysis

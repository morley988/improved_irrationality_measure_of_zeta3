import Zeta3.Transfer.DiagonalPencil
import Mathlib.Analysis.Matrix.PosDef

/-!
# Real symmetric pencils with a definite evaluation

The positive evaluation supplies an inner product in which the normalized
linear part is self-adjoint. Thus the diagonalization used in the
root-multiplicity argument is a proved spectral theorem, not external
evidence or a presumed numerical eigendecomposition.
-/

noncomputable section
namespace Zeta3.Transfer
open Polynomial Matrix Module

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

set_option backward.isDefEq.respectTransparency false in
theorem normalizedPencil_isSymmetric (G B : Matrix ι ι ℝ)
    (hG : G.PosDef) (hB : B.IsHermitian) :
    letI := G.toNormedAddCommGroup hG
    letI : SeminormedAddCommGroup (ι → ℝ) := G.toSeminormedAddCommGroup hG.posSemidef
    letI := G.toInnerProductSpace hG.posSemidef
    LinearMap.IsSymmetric (𝕜 := ℝ) (E := ι → ℝ) (G⁻¹ * B).mulVecLin := by
  let := G.toNormedAddCommGroup hG
  let : SeminormedAddCommGroup (ι → ℝ) := G.toSeminormedAddCommGroup hG.posSemidef
  let := G.toInnerProductSpace hG.posSemidef
  have hGs : Gᵀ = G := (Matrix.isHermitian_iff_isSymm.mp hG.isHermitian).eq
  have hBs : Bᵀ = B := (Matrix.isHermitian_iff_isSymm.mp hB).eq
  have hGB : G * (G⁻¹ * B) = B :=
    Matrix.mul_nonsing_inv_cancel_left G B (isUnit_iff_ne_zero.mpr hG.det_pos.ne')
  intro x y
  change (G *ᵥ y) ⬝ᵥ star ((G⁻¹ * B) *ᵥ x) =
    (G *ᵥ ((G⁻¹ * B) *ᵥ y)) ⬝ᵥ star x
  simp only [star_trivial, Matrix.mulVec_mulVec, hGB]
  calc
    (G *ᵥ y) ⬝ᵥ ((G⁻¹ * B) *ᵥ x) =
        ((G⁻¹ * B) *ᵥ x) ⬝ᵥ G *ᵥ y := dotProduct_comm _ _
    _ = y ⬝ᵥ G *ᵥ ((G⁻¹ * B) *ᵥ x) := by
      simpa only [hGs] using Matrix.dotProduct_transpose_mulVec G ((G⁻¹ * B) *ᵥ x) y
    _ = y ⬝ᵥ B *ᵥ x := by rw [Matrix.mulVec_mulVec, hGB]
    _ = x ⬝ᵥ B *ᵥ y := by
      simpa only [hBs] using Matrix.dotProduct_transpose_mulVec B y x
    _ = (B *ᵥ y) ⬝ᵥ x := dotProduct_comm _ _

set_option backward.isDefEq.respectTransparency false in
theorem exists_basis_normalizedPencil_diagonal (G B : Matrix ι ι ℝ)
    (hG : G.PosDef) (hB : B.IsHermitian) :
    ∃ (b : Basis (Fin (Fintype.card ι)) ℝ (ι → ℝ)) (values : Fin (Fintype.card ι) → ℝ),
      LinearMap.toMatrix b b (G⁻¹ * B).mulVecLin = Matrix.diagonal values := by
  let := G.toNormedAddCommGroup hG
  let : SeminormedAddCommGroup (ι → ℝ) := G.toSeminormedAddCommGroup hG.posSemidef
  let := G.toInnerProductSpace hG.posSemidef
  have hT := normalizedPencil_isSymmetric G B hG hB
  let b := (hT.eigenvectorBasis (finrank_pi ℝ)).toBasis
  let values := hT.eigenvalues (finrank_pi ℝ)
  refine ⟨b, values, ?_⟩
  simpa [b, values, Function.comp_def] using hT.toMatrix_eigenvectorBasis (finrank_pi ℝ)

/-- For a real symmetric affine pencil with one positive definite evaluation,
the determinant vanishes to precisely the dimension of the kernel. No
invertibility of the linear coefficient matrix is required. -/
theorem rootMultiplicity_realPencilDeterminant_eq_finrank_ker
    (A B : Matrix ι ι ℝ) (ξ x : ℝ) (hB : B.IsHermitian)
    (hG : (A + ξ • B).PosDef) :
    (realPencilDeterminant A B).rootMultiplicity x =
      finrank ℝ (LinearMap.ker (A + x • B).mulVecLin) := by
  obtain ⟨b, values, hdiag⟩ := exists_basis_normalizedPencil_diagonal (A + ξ • B) B hG hB
  exact rootMultiplicity_realPencilDeterminant_eq_finrank_ker_of_diagonal
    A B ξ x hG.det_pos.ne' b values hdiag

theorem realPencilDeterminant_ne_zero_of_posDef (A B : Matrix ι ι ℝ)
    (ξ : ℝ) (hG : (A + ξ • B).PosDef) : realPencilDeterminant A B ≠ 0 := by
  intro h
  have heval := congrArg (Polynomial.eval ξ) h
  rw [eval_realPencilDeterminant, eval_zero] at heval
  exact hG.det_pos.ne' heval

/-- A nonzero scalar factor and a proved evaluation identity preserve the
precise multiplicity-nullity equality. This form is convenient for integer
polynomials obtained by clearing the rational determinant coefficients. -/
theorem rootMultiplicity_eq_finrank_ker_of_eval_eq_det
    (P : ℝ[X]) (A B : Matrix ι ι ℝ) (ξ x c : ℝ)
    (hc : c ≠ 0) (hB : B.IsHermitian) (hG : (A + ξ • B).PosDef)
    (hidentity : ∀ y : ℝ, P.eval y = c * (A + y • B).det) :
    P.rootMultiplicity x = finrank ℝ (LinearMap.ker (A + x • B).mulVecLin) := by
  have hp : P = C c * realPencilDeterminant A B := by
    apply Polynomial.funext
    intro y
    simpa only [eval_mul, eval_C, eval_realPencilDeterminant] using hidentity y
  rw [hp, rootMultiplicity_mul (mul_ne_zero (C_ne_zero.mpr hc)
    (realPencilDeterminant_ne_zero_of_posDef A B ξ hG)), rootMultiplicity_C, zero_add]
  exact rootMultiplicity_realPencilDeterminant_eq_finrank_ker A B ξ x hB hG

theorem rootMultiplicity_le_of_eval_eq_definite_det
    (P : ℝ[X]) (A B : Matrix ι ι ℝ) (ξ x c : ℝ) (bound : ℕ)
    (hc : c ≠ 0) (hB : B.IsHermitian) (hG : (A + ξ • B).PosDef)
    (hidentity : ∀ y : ℝ, P.eval y = c * (A + y • B).det)
    (hnullity : finrank ℝ (LinearMap.ker (A + x • B).mulVecLin) ≤ bound) :
    P.rootMultiplicity x ≤ bound := by
  rw [rootMultiplicity_eq_finrank_ker_of_eval_eq_det P A B ξ x c hc hB hG hidentity]
  exact hnullity

end Zeta3.Transfer

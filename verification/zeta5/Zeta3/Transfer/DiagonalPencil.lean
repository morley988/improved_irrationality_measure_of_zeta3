import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Data.Real.Basic
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.LinearAlgebra.Determinant
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Multiplicity of a diagonalized affine pencil

An affine factor normalized to equal one at `ξ` is never the zero
polynomial. Its root multiplicity is therefore exactly one at a root and
zero elsewhere. These elementary facts convert a diagonal pencil into an
exact equality between determinant root multiplicity and matrix nullity.
-/

noncomputable section
namespace Zeta3.Transfer
open Polynomial Matrix Module

def normalizedLinearFactor (ξ v : ℝ) : ℝ[X] :=
  1 + (X - C ξ) * C v

@[simp] theorem eval_normalizedLinearFactor (ξ v x : ℝ) :
    (normalizedLinearFactor ξ v).eval x = 1 + (x - ξ) * v := by
  simp [normalizedLinearFactor]

theorem normalizedLinearFactor_ne_zero (ξ v : ℝ) :
    normalizedLinearFactor ξ v ≠ 0 := by
  intro h
  have := congrArg (Polynomial.eval ξ) h
  simp at this

theorem rootMultiplicity_normalizedLinearFactor (ξ v x : ℝ) :
    (normalizedLinearFactor ξ v).rootMultiplicity x =
      if 1 + (x - ξ) * v = 0 then 1 else 0 := by
  classical
  by_cases hx : 1 + (x - ξ) * v = 0
  · have hv : v ≠ 0 := by intro hv; simp [hv] at hx
    have hp : normalizedLinearFactor ξ v = C v * (X - C x) := by
      apply Polynomial.funext
      intro y
      simp only [eval_normalizedLinearFactor, eval_mul, eval_C, eval_sub, eval_X]
      nlinarith
    rw [hp, rootMultiplicity_mul (mul_ne_zero (C_ne_zero.mpr hv) (X_sub_C_ne_zero x)),
      rootMultiplicity_C, rootMultiplicity_X_sub_C_self, if_pos hx]
  · rw [if_neg hx]
    exact rootMultiplicity_eq_zero (by simpa only [IsRoot, eval_normalizedLinearFactor] using hx)

theorem rootMultiplicity_prod_of_ne_zero {ι : Type*} (s : Finset ι)
    (f : ι → ℝ[X]) (x : ℝ) (hf : ∀ i ∈ s, f i ≠ 0) :
    (∏ i ∈ s, f i).rootMultiplicity x = ∑ i ∈ s, (f i).rootMultiplicity x := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simp only [Finset.prod_empty, Finset.sum_empty]
    simpa only [map_one] using rootMultiplicity_C (1 : ℝ) x
  | @insert i s hi ih =>
    have hi0 := hf i (Finset.mem_insert_self i s)
    have hs0 : ∀ j ∈ s, f j ≠ 0 := fun j hj => hf j (Finset.mem_insert_of_mem hj)
    rw [Finset.prod_insert hi, Finset.sum_insert hi,
      rootMultiplicity_mul (mul_ne_zero hi0 (Finset.prod_ne_zero_iff.mpr hs0)), ih hs0]

theorem rootMultiplicity_normalized_product {ι : Type*} [Fintype ι]
    (ξ x : ℝ) (values : ι → ℝ) :
    (∏ i, normalizedLinearFactor ξ (values i)).rootMultiplicity x =
      Fintype.card {i // 1 + (x - ξ) * values i = 0} := by
  classical
  rw [rootMultiplicity_prod_of_ne_zero _ _ _
    (fun i _ => normalizedLinearFactor_ne_zero ξ (values i))]
  simp [rootMultiplicity_normalizedLinearFactor, Finset.sum_boole, Fintype.card_subtype]

theorem finrank_ker_diagonal_eq_card_zero {ι : Type*} [Fintype ι] [DecidableEq ι]
    (values : ι → ℝ) :
    finrank ℝ (LinearMap.ker (Matrix.diagonal values).mulVecLin) =
      Fintype.card {i // values i = 0} := by
  classical
  have hrank := LinearMap.finrank_range_add_finrank_ker (Matrix.diagonal values).mulVecLin
  have hcount := Finset.card_filter_add_card_filter_not (s := Finset.univ)
    (p := fun i => values i = 0)
  rw [finrank_pi] at hrank
  change (Matrix.diagonal values).rank + _ = _ at hrank
  rw [Matrix.rank_diagonal] at hrank
  simp only [← Fintype.card_subtype, Finset.card_univ] at hcount
  have hcount' : Fintype.card {i // values i ≠ 0} +
      Fintype.card {i // values i = 0} = Fintype.card ι := by
    simpa only [ne_eq, add_comm] using hcount
  exact Nat.add_left_cancel (hrank.trans hcount'.symm)

section Basis
variable {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

theorem mulVecLin_one_add_smul (M : Matrix ι ι ℝ) (t : ℝ) :
    (1 + t • M).mulVecLin = LinearMap.id + t • M.mulVecLin := by
  ext v i
  simp

theorem toMatrix_one_add_smul_of_diagonal (M : Matrix ι ι ℝ)
    (b : Basis κ ℝ (ι → ℝ)) (values : κ → ℝ)
    (hdiag : LinearMap.toMatrix b b M.mulVecLin = Matrix.diagonal values) (t : ℝ) :
    LinearMap.toMatrix b b (1 + t • M).mulVecLin =
      Matrix.diagonal (fun i => 1 + t * values i) := by
  rw [mulVecLin_one_add_smul, map_add, map_smul, LinearMap.toMatrix_id, hdiag]
  ext i j
  by_cases hij : i = j
  · subst j
    simp
  · simp [hij]

theorem det_one_add_smul_of_diagonal (M : Matrix ι ι ℝ)
    (b : Basis κ ℝ (ι → ℝ)) (values : κ → ℝ)
    (hdiag : LinearMap.toMatrix b b M.mulVecLin = Matrix.diagonal values) (t : ℝ) :
    (1 + t • M).det = ∏ i, (1 + t * values i) := by
  calc
    (1 + t • M).det = LinearMap.det (1 + t • M).mulVecLin :=
      (LinearMap.det_toLin' _).symm
    _ = (LinearMap.toMatrix b b (1 + t • M).mulVecLin).det :=
      (LinearMap.det_toMatrix b _).symm
    _ = ∏ i, (1 + t * values i) := by
      rw [toMatrix_one_add_smul_of_diagonal M b values hdiag, Matrix.det_diagonal]

theorem rank_one_add_smul_of_diagonal (M : Matrix ι ι ℝ)
    (b : Basis κ ℝ (ι → ℝ)) (values : κ → ℝ)
    (hdiag : LinearMap.toMatrix b b M.mulVecLin = Matrix.diagonal values) (t : ℝ) :
    (1 + t • M).rank = (Matrix.diagonal (fun i => 1 + t * values i)).rank := by
  rw [← toMatrix_one_add_smul_of_diagonal M b values hdiag]
  rw [Matrix.rank_eq_finrank_range_toLin _ b b, Matrix.toLin_toMatrix]
  rfl

end Basis

section Affine
variable {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

def realAffinePencil (A B : Matrix ι ι ℝ) : Matrix ι ι ℝ[X] :=
  fun i j => C (A i j) + X * C (B i j)

def realPencilDeterminant (A B : Matrix ι ι ℝ) : ℝ[X] :=
  (realAffinePencil A B).det

@[simp] theorem eval_realPencilDeterminant (A B : Matrix ι ι ℝ) (x : ℝ) :
    (realPencilDeterminant A B).eval x = (A + x • B).det := by
  change (Polynomial.evalRingHom x) (realAffinePencil A B).det = _
  rw [RingHom.map_det]
  congr 1
  ext i j
  simp [realAffinePencil, RingHom.mapMatrix_apply]
  ring

theorem affinePencil_factorization (A B : Matrix ι ι ℝ) (ξ x : ℝ)
    (hdet : (A + ξ • B).det ≠ 0) :
    A + x • B = (A + ξ • B) * (1 + (x - ξ) • ((A + ξ • B)⁻¹ * B)) := by
  rw [Matrix.mul_add, Matrix.mul_one, Matrix.mul_smul,
    Matrix.mul_nonsing_inv_cancel_left _ _ (isUnit_iff_ne_zero.mpr hdet)]
  ext i j
  simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
  ring

theorem realPencilDeterminant_eq_product_of_diagonal (A B : Matrix ι ι ℝ)
    (ξ : ℝ) (hdet : (A + ξ • B).det ≠ 0)
    (b : Basis κ ℝ (ι → ℝ)) (values : κ → ℝ)
    (hdiag : LinearMap.toMatrix b b ((A + ξ • B)⁻¹ * B).mulVecLin =
      Matrix.diagonal values) :
    realPencilDeterminant A B =
      C (A + ξ • B).det * ∏ i, normalizedLinearFactor ξ (values i) := by
  apply Polynomial.funext
  intro x
  rw [eval_realPencilDeterminant, affinePencil_factorization A B ξ x hdet, Matrix.det_mul,
    det_one_add_smul_of_diagonal _ b values hdiag]
  simp only [eval_mul, eval_C, eval_prod, eval_normalizedLinearFactor]

theorem finrank_ker_affinePencil_of_diagonal (A B : Matrix ι ι ℝ)
    (ξ x : ℝ) (hdet : (A + ξ • B).det ≠ 0)
    (b : Basis κ ℝ (ι → ℝ)) (values : κ → ℝ)
    (hdiag : LinearMap.toMatrix b b ((A + ξ • B)⁻¹ * B).mulVecLin =
      Matrix.diagonal values) :
    finrank ℝ (LinearMap.ker (A + x • B).mulVecLin) =
      Fintype.card {i // 1 + (x - ξ) * values i = 0} := by
  have hrank : (A + x • B).rank =
      (Matrix.diagonal (fun i => 1 + (x - ξ) * values i)).rank := by
    rw [affinePencil_factorization A B ξ x hdet,
      Matrix.rank_mul_eq_right_of_det_ne_zero _ _ hdet,
      rank_one_add_smul_of_diagonal _ b values hdiag]
  have hcard : Fintype.card ι = Fintype.card κ := by
    simpa only [finrank_pi] using Module.finrank_eq_card_basis b
  have hleft := LinearMap.finrank_range_add_finrank_ker (A + x • B).mulVecLin
  have hright := LinearMap.finrank_range_add_finrank_ker
    (Matrix.diagonal (fun i => 1 + (x - ξ) * values i)).mulVecLin
  change (A + x • B).rank + _ = _ at hleft
  change (Matrix.diagonal (fun i => 1 + (x - ξ) * values i)).rank + _ = _ at hright
  rw [hrank, finrank_pi, hcard] at hleft
  rw [finrank_pi, finrank_ker_diagonal_eq_card_zero] at hright
  exact Nat.add_left_cancel (hleft.trans hright.symm)

/-- Exact multiplicity-nullity equality for an affine real pencil whose
normalized linear part has a diagonalizing basis. -/
theorem rootMultiplicity_realPencilDeterminant_eq_finrank_ker_of_diagonal
    (A B : Matrix ι ι ℝ) (ξ x : ℝ) (hdet : (A + ξ • B).det ≠ 0)
    (b : Basis κ ℝ (ι → ℝ)) (values : κ → ℝ)
    (hdiag : LinearMap.toMatrix b b ((A + ξ • B)⁻¹ * B).mulVecLin =
      Matrix.diagonal values) :
    (realPencilDeterminant A B).rootMultiplicity x =
      finrank ℝ (LinearMap.ker (A + x • B).mulVecLin) := by
  classical
  rw [realPencilDeterminant_eq_product_of_diagonal A B ξ hdet b values hdiag,
    rootMultiplicity_mul (mul_ne_zero (C_ne_zero.mpr hdet)
      (Finset.prod_ne_zero_iff.mpr (fun i _ => normalizedLinearFactor_ne_zero ξ (values i)))),
    rootMultiplicity_C, zero_add, rootMultiplicity_normalized_product]
  exact (finrank_ker_affinePencil_of_diagonal A B ξ x hdet b values hdiag).symm

end Affine

end Zeta3.Transfer

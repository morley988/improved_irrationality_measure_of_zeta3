import Zeta5.Arithmetic.RestrictionPencil
import Zeta5.Arithmetic.PadicResidue
import Mathlib.LinearAlgebra.Vandermonde
import Mathlib.LinearAlgebra.Matrix.Rank

/-!
# Evaluation ranks of complete top features

The rectangular rank theorem is proved by an actual nonsingular Vandermonde
minor. Row and column unit factors are allowed. The subsequent arithmetic
application must still identify its local top coefficients with this form;
that identification is not hidden in the definition of the matrix.
-/

noncomputable section
namespace Zeta3.Construction.Features
open Polynomial Matrix
variable {K ι : Type*} [Field K] [Fintype ι] [DecidableEq ι]

def evaluationMatrix (H : ℕ) (v : ι → K) (q : Fin H → K[X]) : Matrix ι (Fin H) K :=
  fun i j => (q j).eval (v i)

theorem evaluationMatrix_rank (H : ℕ) (v : ι → K) (hv : Function.Injective v)
    (q : Fin H → K[X]) (hq : ∀ j, (q j).Monic) (hd : ∀ j, (q j).natDegree = j.val) :
    (evaluationMatrix H v q).rank = min H (Fintype.card ι) := by
  classical
  let k := min H (Fintype.card ι)
  let col : Fin k → Fin H := Fin.castLE (min_le_left _ _)
  let row : Fin k → ι := fun i => (Fintype.equivFin ι).symm (Fin.castLE (min_le_right _ _) i)
  have hrow : Function.Injective row :=
    (Fintype.equivFin ι).symm.injective.comp (Fin.castLE_injective _)
  have hdet : ((evaluationMatrix H v q).submatrix row col).det ≠ 0 := by
    have he := Matrix.det_eval_matrixOfPolynomials_eq_det_vandermonde
      (fun i : Fin k => v (row i)) (fun j : Fin k => q (col j))
      (fun j => hd (col j)) (fun j => hq (col j))
    change (Matrix.of (fun i j : Fin k => (q (col j)).eval (v (row i)))).det ≠ 0
    rw [← he]
    exact Matrix.det_vandermonde_ne_zero_iff.mpr (hv.comp hrow)
  have hminor := Matrix.rank_of_det_ne_zero hdet
  have hle := Matrix.rank_submatrix_le (evaluationMatrix H v q) row col
  rw [hminor, Fintype.card_fin] at hle
  apply le_antisymm
  · exact le_min (by simpa using Matrix.rank_le_card_width (evaluationMatrix H v q))
      (Matrix.rank_le_card_height _)
  · exact hle

def scaledEvaluationMatrix (H : ℕ) (v : ι → K) (q : Fin H → K[X])
    (a : ι → K) (b : Fin H → K) : Matrix ι (Fin H) K :=
  fun i j => a i * (q j).eval (v i) * b j

theorem scaledEvaluationMatrix_eq (H : ℕ) (v : ι → K) (q : Fin H → K[X])
    (a : ι → K) (b : Fin H → K) :
    scaledEvaluationMatrix H v q a b = diagonal a * evaluationMatrix H v q * diagonal b := by
  ext i j
  simp [scaledEvaluationMatrix, Matrix.diagonal_mul, Matrix.mul_diagonal, evaluationMatrix]

theorem scaledEvaluationMatrix_rank (H : ℕ) (v : ι → K) (hv : Function.Injective v)
    (q : Fin H → K[X]) (hq : ∀ j, (q j).Monic) (hd : ∀ j, (q j).natDegree = j.val)
    (a : ι → K) (b : Fin H → K) (ha : ∀ i, a i ≠ 0) (hb : ∀ j, b j ≠ 0) :
    (scaledEvaluationMatrix H v q a b).rank = min H (Fintype.card ι) := by
  have hA : (diagonal a).det ≠ 0 := by simpa [det_diagonal, Finset.prod_ne_zero_iff] using ha
  have hB : (diagonal b).det ≠ 0 := by simpa [det_diagonal, Finset.prod_ne_zero_iff] using hb
  rw [scaledEvaluationMatrix_eq, Matrix.rank_mul_eq_left_of_det_ne_zero _ _ hB,
    Matrix.rank_mul_eq_right_of_det_ne_zero _ _ hA]
  exact evaluationMatrix_rank H v hv q hq hd

/-- The monic top-feature family determined by the central recurrence. -/
def successiveRootFamily (s : ℕ → K) (h : ℕ) : K[X] :=
  ∏ j ∈ Finset.range h, (X - C (s j))

theorem successiveRootFamily_monic (s : ℕ → K) (h : ℕ) : (successiveRootFamily s h).Monic :=
  monic_prod_of_monic _ _ (fun _ _ => monic_X_sub_C _)

theorem successiveRootFamily_natDegree (s : ℕ → K) (h : ℕ) :
    (successiveRootFamily s h).natDegree = h := by
  rw [successiveRootFamily, natDegree_prod_of_monic _ _ (fun _ _ => monic_X_sub_C _)]
  simp

theorem successiveRootFamily_succ (s : ℕ → K) (h : ℕ) :
    successiveRootFamily s (h + 1) = successiveRootFamily s h * (X - C (s h)) := by
  simp only [successiveRootFamily, Finset.prod_range_succ]

/-- A unit recurrence forces the actual top-feature matrix to have maximal
rectangular rank. The initial row factors may vary with the residue class. -/
theorem recurrence_feature_rank (H : ℕ) (v : ι → K) (hv : Function.Injective v)
    (s d : ℕ → K) (hd : ∀ j, j+1 < H → d j ≠ 0) (T : ι → ℕ → K)
    (hzero : ∀ i, T i 0 ≠ 0)
    (hstep : ∀ i j, j + 1 < H → T i (j + 1) = T i j * (v i - s j) / d j) :
    (Matrix.of (fun i (j : Fin H) => T i j.val)).rank = min H (Fintype.card ι) := by
  let b : ℕ → K := fun h => (∏ j ∈ Finset.range h, d j)⁻¹
  have hb (h : ℕ) (hh : h < H) : b h ≠ 0 := by
    apply inv_ne_zero
    apply Finset.prod_ne_zero_iff.mpr
    intro j hj
    exact hd j (by have := Finset.mem_range.mp hj; omega)
  have he (i : ι) (h : ℕ) (hh : h < H) :
      T i h = T i 0 * (successiveRootFamily s h).eval (v i) * b h := by
    induction h with
    | zero => simp [successiveRootFamily, b]
    | succ h ih =>
      rw [hstep i h hh, ih (by omega), successiveRootFamily_succ, eval_mul, eval_sub, eval_X, eval_C]
      simp only [b, Finset.prod_range_succ, _root_.mul_inv_rev, div_eq_mul_inv]
      ring
  have hmatrix : Matrix.of (fun i (j : Fin H) => T i j.val) =
      scaledEvaluationMatrix H v (fun j => successiveRootFamily s j.val)
        (fun i => T i 0) (fun j => b j.val) := by
    ext i j
    exact he i j.val j.isLt
  rw [hmatrix]
  exact scaledEvaluationMatrix_rank H v hv _ (fun j => successiveRootFamily_monic s j.val)
    (fun j => successiveRootFamily_natDegree s j.val) _ _ hzero
    (fun j => hb j.val j.isLt)

end Zeta3.Construction.Features

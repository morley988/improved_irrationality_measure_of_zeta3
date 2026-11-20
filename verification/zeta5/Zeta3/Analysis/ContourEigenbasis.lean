import Zeta3.Analysis.ContourPhysicalSpace
import Zeta3.Analysis.ContourMatrixBridge

/-!
# The actual determinant response in the contour operator eigenbasis

The physical Hilbert eigenbasis consists of genuine real polynomials.
The diagonal positive contour norms are its eigenvalues, so the previously
proved exact coefficient response bound applies to the actual spectrum.
-/

noncomputable section
open Polynomial Matrix
open scoped BigOperators
namespace Zeta3.Analysis

section Generic
variable (N m₁ m₂ r : ℕ) (hN : 0<N) (u : ℝ) (hu : 1<u)

def contourEigenpolynomial (i : Fin r) : ℝ[X] :=
  ((contourPolynomialOperator_isSymmetric N m₁ m₂ r hN u hu).eigenvectorBasis
    (realDegreeLT_finrank r) i : ℝ[X])

theorem contourEigenpolynomial_natDegree_lt (hr : 0<r) (i : Fin r) :
    (contourEigenpolynomial N m₁ m₂ r hN u hu i).natDegree<r := by
  let b := (contourPolynomialOperator_isSymmetric N m₁ m₂ r hN u hu).eigenvectorBasis
    (realDegreeLT_finrank r)
  have hp : contourEigenpolynomial N m₁ m₂ r hN u hu i ∈ Polynomial.degreeLT ℝ r :=
    (show Polynomial.degreeLT ℝ r from b i).property
  by_cases hz : contourEigenpolynomial N m₁ m₂ r hN u hu i=0
  · simpa only [hz,Polynomial.natDegree_zero] using hr
  · exact (Polynomial.natDegree_lt_iff_degree_lt hz).mpr (Polynomial.mem_degreeLT.mp hp)

theorem physicalRescalePolynomial_natDegree (hpos : 0<N) (p : ℝ[X]) :
    (physicalRescalePolynomial N p).natDegree=p.natDegree := by
  have hNr : (N:ℝ)≠0 := by exact_mod_cast hpos.ne'
  rw [physicalRescalePolynomial,Polynomial.natDegree_comp,
    Polynomial.natDegree_C_mul_X _ (inv_ne_zero (pow_ne_zero 2 hNr)),mul_one]

theorem contourEigenpolynomial_orthonormal :
    normalizedPhysicalMatrix N m₁ m₂ r (contourEigenpolynomial N m₁ m₂ r hN u hu)=1 := by
  let b := (contourPolynomialOperator_isSymmetric N m₁ m₂ r hN u hu).eigenvectorBasis
    (realDegreeLT_finrank r)
  ext i j
  change normalizedPhysicalPair N m₁ m₂ (b i:ℝ[X]) (b j:ℝ[X])=(1:Matrix (Fin r) (Fin r) ℝ) i j
  rw [← physicalPolynomial_inner N m₁ m₂ r hN]
  exact b.inner_eq_ite i j

theorem positiveContourNorm_eigenpolynomial (i : Fin r) :
    positiveContourNorm N m₁ m₂ u (contourEigenpolynomial N m₁ m₂ r hN u hu i)=
      (contourPolynomialOperator_isSymmetric N m₁ m₂ r hN u hu).eigenvalues
        (realDegreeLT_finrank r) i := by
  let hT := contourPolynomialOperator_isSymmetric N m₁ m₂ r hN u hu
  let b := hT.eigenvectorBasis (realDegreeLT_finrank r)
  change positiveContourNorm N m₁ m₂ u (b i:ℝ[X])=_
  rw [← contourPolynomialOperator_inner_self N m₁ m₂ r hN u hu (b i)]
  erw [hT.apply_eigenvectorBasis (realDegreeLT_finrank r) i]
  simp [real_inner_smul_left,b,hT,OrthonormalBasis.inner_eq_ite]

end Generic

/-- The actual response majorant in terms of the actual positive spectrum. -/
theorem determinantResponse_eigenvalue_majorant (n : ℕ) (hn : 0<n)
    (u : ℝ) (hu : 1<u) (h : ℂ) :
    ‖determinantResponse n h‖≤(Nat.factorial (51*n):ℝ)*
      ∏ i : Fin (51*n), (1+‖h‖*
        (contourPolynomialOperator_isSymmetric (50*n) (4*n) (16*n) (51*n)
          (by omega) u hu).eigenvalues (realDegreeLT_finrank (51*n)) i) := by
  have hN : 0<50*n := by omega
  have hr : 0<51*n := by omega
  let p := contourEigenpolynomial (50*n) (4*n) (16*n) (51*n) hN u hu
  have hp (i : Fin (51*n)) : (physicalRescalePolynomial (50*n) (p i)).natDegree<51*n := by
    rw [physicalRescalePolynomial_natDegree (50*n) hN]
    exact contourEigenpolynomial_natDegree_lt _ _ _ _ hN u hu hr i
  have hb := determinantResponse_majorant_of_physical_orthonormal n hn p hp
    (contourEigenpolynomial_orthonormal _ _ _ _ hN u hu) u hu h
  simpa only [p,positiveContourNorm_eigenpolynomial] using hb

end Zeta3.Analysis

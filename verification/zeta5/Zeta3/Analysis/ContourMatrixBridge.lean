import Zeta3.Analysis.ContourCoefficientLinear
import Zeta3.Analysis.ContourMatrixAlgebra

/-!
# Exact contour-basis identification of the actual determinant response

Any tuple of physical-orthonormal real polynomials of the full required
dimension gives precisely the original Hankel determinant response.  The
coefficient matrix is the actual normalized contour residue form.
-/

noncomputable section
open Matrix Polynomial
open scoped BigOperators
namespace Zeta3.Analysis

theorem map_normalized_real_congruence {ι : Type*} [Fintype ι]
    (s : ℝ) (C G : Matrix ι ι ℝ) :
    (s⁻¹ • (C.transpose*G*C)).map Complex.ofRealHom =
      (s:ℂ)⁻¹ • ((C.map Complex.ofRealHom).transpose *
        G.map Complex.ofRealHom * C.map Complex.ofRealHom) := by
  rw [Matrix.map_smul' _ _ _ (map_mul Complex.ofRealHom)]
  simp only [map_inv₀, Matrix.map_mul, Matrix.transpose_map,Complex.ofRealHom_eq_coe]

def normalizedPhysicalMatrix (N m₁ m₂ r : ℕ) (p : Fin r → ℝ[X]) : Matrix (Fin r) (Fin r) ℝ :=
  fun i j => normalizedPhysicalPair N m₁ m₂ (p i) (p j)

def realWindowCoefficientMatrix (N m₁ m₂ r : ℕ) (p : Fin r → ℝ[X]) : Matrix (Fin r) (Fin r) ℝ :=
  fun i j => realWindowCoefficientPair N m₁ m₂ (p i) (p j)

theorem normalizedComplexWindowMatrix_real (N m₁ m₂ r : ℕ) (p : Fin r → ℝ[X]) :
    normalizedComplexWindowMatrix N m₁ m₂ (fun i => (p i).map Complex.ofRealHom)=
      (realWindowCoefficientMatrix N m₁ m₂ r p).map Complex.ofRealHom := by
  ext i j
  exact normalizedComplexWindowCoefficient_real N m₁ m₂ (p i) (p j)

theorem complexPhysicalGram_eq_monomial (n : ℕ) :
    complexPhysicalGram n=
      (Zeta5.Analysis.realMonomialGram
        (PhysicalMeasure.windowMomentFunctional (50*n) (4*n) (16*n)) (51*n)).map Complex.ofRealHom := by
  rw [complexPhysicalGram_eq_real_map,PhysicalMeasure.realHankel_eq_physicalGram]
  rfl

/-- Exact response identity for any physical orthonormal polynomial tuple. -/
theorem determinantResponse_eq_contour_matrix (n : ℕ) (p : Fin (51*n) → ℝ[X])
    (hp : ∀i,(physicalRescalePolynomial (50*n) (p i)).natDegree<51*n)
    (hortho : normalizedPhysicalMatrix (50*n) (4*n) (16*n) (51*n) p=1) (h : ℂ) :
    determinantResponse n h=
      (1+h • normalizedComplexWindowMatrix (50*n) (4*n) (16*n)
        (fun i => (p i).map Complex.ofRealHom)).det := by
  let C := Zeta5.Analysis.realCoefficientMatrix (51*n)
    (fun i => physicalRescalePolynomial (50*n) (p i))
  have hGr : (physicalWeightScale (50*n) (4*n) (16*n))⁻¹ •
      (C.transpose * Zeta5.Analysis.realMonomialGram
        (PhysicalMeasure.windowMomentFunctional (50*n) (4*n) (16*n)) (51*n) * C)=1 := by
    rw [← normalizedPhysicalPair_congruence _ _ _ _ p hp]
    exact hortho
  have hGc := congrArg (fun M : Matrix (Fin (51*n)) (Fin (51*n)) ℝ => M.map Complex.ofRealHom) hGr
  rw [map_normalized_real_congruence,← complexPhysicalGram_eq_monomial,
    Matrix.map_one _ (map_zero _) (map_one _)] at hGc
  have hBr : realWindowCoefficientMatrix (50*n) (4*n) (16*n) (51*n) p=
      (physicalWeightScale (50*n) (4*n) (16*n))⁻¹ •
        (C.transpose * Zeta3.Transfer.realHankelLinear n * C) := by
    rw [realHankelLinear_eq_windowMonomialGram]
    exact realWindowCoefficientPair_congruence _ _ _ _ p hp
  have hBc := congrArg (fun M : Matrix (Fin (51*n)) (Fin (51*n)) ℝ => M.map Complex.ofRealHom) hBr
  rw [map_normalized_real_congruence,← complexHankelLinear_eq_real_map,
    ← normalizedComplexWindowMatrix_real] at hBc
  exact (determinant_response_eq_of_congruence
    (complexPhysicalGram n) (complexHankelLinear n) (C.map Complex.ofRealHom)
    (normalizedComplexWindowMatrix (50*n) (4*n) (16*n) (fun i => (p i).map Complex.ofRealHom))
    (physicalWeightScale (50*n) (4*n) (16*n)) h (complexPhysicalGram_det_ne_zero n) hGc hBc).symm

/-- The actual response bound in any physical-orthonormal tuple. -/
theorem determinantResponse_majorant_of_physical_orthonormal (n : ℕ) (hn : 0<n)
    (p : Fin (51*n) → ℝ[X])
    (hp : ∀i,(physicalRescalePolynomial (50*n) (p i)).natDegree<51*n)
    (hortho : normalizedPhysicalMatrix (50*n) (4*n) (16*n) (51*n) p=1)
    (u : ℝ) (hu : 1<u) (h : ℂ) :
    ‖determinantResponse n h‖ ≤ (Nat.factorial (51*n):ℝ) *
      ∏ i,(1+‖h‖*positiveContourNorm (50*n) (4*n) (16*n) u (p i)) := by
  rw [determinantResponse_eq_contour_matrix n p hp hortho]
  simpa only [Fintype.card_fin,positiveContourNorm] using
    normalizedComplexWindowCoefficient_response_majorant (50*n) (4*n) (16*n)
      (fun i => (p i).map Complex.ofRealHom) u (by omega) hu h

end Zeta3.Analysis

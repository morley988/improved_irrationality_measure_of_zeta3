import Zeta3.Analysis.ContourBilinear
import Zeta3.Analysis.ContourUniformNorm
import Zeta3.Analysis.SpectralMinmaxOperator
import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.Analysis.Normed.Module.FiniteDimension

/-!
# The actual finite-dimensional physical Hilbert space and contour operator

The inner product is the genuine normalized cubic Gram form on polynomials
of bounded degree.  Riesz representation constructs the actual positive
contour operator from the proved integral bilinear form.  Its eigenvalues
therefore have the usual minmax meaning for these two concrete norms.
-/

noncomputable section
open Set MeasureTheory Polynomial
namespace Zeta3.Analysis

instance realDegreeLT_finiteDimensional (r : ℕ) : FiniteDimensional ℝ (Polynomial.degreeLT ℝ r) :=
  FiniteDimensional.of_injective (Polynomial.degreeLTEquiv ℝ r).toLinearMap
    (Polynomial.degreeLTEquiv ℝ r).injective

theorem realDegreeLT_finrank (r : ℕ) : Module.finrank ℝ (Polynomial.degreeLT ℝ r)=r := by
  simpa using (Polynomial.degreeLTEquiv ℝ r).finrank_eq

@[instance_reducible]
def physicalPolynomialInnerCore (N m₁ m₂ r : ℕ) (hN : 0 < N) :
    InnerProductSpace.Core ℝ (Polynomial.degreeLT ℝ r) where
  inner p q := normalizedPhysicalPair N m₁ m₂ p q
  conj_inner_symm p q := by
    simpa using normalizedPhysicalPair_symm N m₁ m₂ (q:ℝ[X]) (p:ℝ[X])
  re_inner_nonneg p := by
    change 0 ≤ normalizedPhysicalPair N m₁ m₂ (p:ℝ[X]) p
    rw [normalizedPhysicalPair_self]
    exact normalizedPhysicalNorm_nonneg N m₁ m₂ hN p
  add_left p q r := normalizedPhysicalPair_add_left N m₁ m₂ p q r
  smul_left p q a := by
    simpa using normalizedPhysicalPair_smul_left N m₁ m₂ a (p:ℝ[X]) q
  definite p hp := by
    apply Subtype.ext
    change (p:ℝ[X])=0
    by_contra hn
    have hpos := normalizedPhysicalNorm_pos N m₁ m₂ hN hn
    change normalizedPhysicalPair N m₁ m₂ (p:ℝ[X]) p=0 at hp
    rw [normalizedPhysicalPair_self] at hp
    linarith

@[instance_reducible]
def physicalPolynomialNormed (N m₁ m₂ r : ℕ) (hN : 0 < N) :
    NormedAddCommGroup (Polynomial.degreeLT ℝ r) := by
  letI := physicalPolynomialInnerCore N m₁ m₂ r hN
  exact InnerProductSpace.Core.toNormedAddCommGroup (𝕜 := ℝ) (F := Polynomial.degreeLT ℝ r)

@[instance_reducible]
def physicalPolynomialInner (N m₁ m₂ r : ℕ) (hN : 0 < N) :
    @InnerProductSpace ℝ (Polynomial.degreeLT ℝ r) _ (physicalPolynomialNormed N m₁ m₂ r hN).toSeminormedAddCommGroup := by
  letI := physicalPolynomialInnerCore N m₁ m₂ r hN
  exact InnerProductSpace.ofCore (inferInstance : PreInnerProductSpace.Core ℝ (Polynomial.degreeLT ℝ r))

/-- A type synonym retaining the parameters that select the physical norm. -/
def PhysicalPolynomialSpace (N m₁ m₂ r : ℕ) (_hN : 0 < N) : Type := Polynomial.degreeLT ℝ r

instance (N m₁ m₂ r : ℕ) (hN : 0 < N) : NormedAddCommGroup (PhysicalPolynomialSpace N m₁ m₂ r hN) :=
  physicalPolynomialNormed N m₁ m₂ r hN

instance (N m₁ m₂ r : ℕ) (hN : 0 < N) : InnerProductSpace ℝ (PhysicalPolynomialSpace N m₁ m₂ r hN) :=
  physicalPolynomialInner N m₁ m₂ r hN

instance (N m₁ m₂ r : ℕ) (hN : 0 < N) : FiniteDimensional ℝ (PhysicalPolynomialSpace N m₁ m₂ r hN) :=
  inferInstanceAs (FiniteDimensional ℝ (Polynomial.degreeLT ℝ r))

instance (N m₁ m₂ r : ℕ) (hN : 0 < N) : CoeOut (PhysicalPolynomialSpace N m₁ m₂ r hN) ℝ[X] :=
  ⟨fun p => (show Polynomial.degreeLT ℝ r from p).val⟩

instance (N m₁ m₂ r : ℕ) (hN : 0 < N) : CompleteSpace (PhysicalPolynomialSpace N m₁ m₂ r hN) :=
  FiniteDimensional.complete ℝ _

section Operator
variable (N m₁ m₂ r : ℕ) (hN : 0 < N) (u : ℝ) (hu : 1 < u)

theorem physicalPolynomial_inner (p q : PhysicalPolynomialSpace N m₁ m₂ r hN) :
    inner ℝ p q=normalizedPhysicalPair N m₁ m₂ (p:ℝ[X]) q := rfl

theorem physicalPolynomial_inner_self (p : PhysicalPolynomialSpace N m₁ m₂ r hN) :
    inner ℝ p p=normalizedPhysicalNorm N m₁ m₂ (p:ℝ[X]) :=
  normalizedPhysicalPair_self N m₁ m₂ p

def contourPolynomialBilinForm : LinearMap.BilinForm ℝ (PhysicalPolynomialSpace N m₁ m₂ r hN) :=
  (positiveContourBilinForm N m₁ m₂ hN u hu).restrict (Polynomial.degreeLT ℝ r)

def contourPolynomialOperator : (PhysicalPolynomialSpace N m₁ m₂ r hN) →ₗ[ℝ] (PhysicalPolynomialSpace N m₁ m₂ r hN) :=
  (InnerProductSpace.toDual ℝ (PhysicalPolynomialSpace N m₁ m₂ r hN)).symm.toLinearEquiv.toLinearMap.comp
    (LinearMap.toContinuousLinearMap.toLinearMap.comp (contourPolynomialBilinForm N m₁ m₂ r hN u hu))

theorem contourPolynomialOperator_inner (p q : PhysicalPolynomialSpace N m₁ m₂ r hN) :
    inner ℝ (contourPolynomialOperator N m₁ m₂ r hN u hu p) q=
      positiveContourPair N m₁ m₂ u (p:ℝ[X]) q := by
  change inner ℝ ((InnerProductSpace.toDual ℝ (PhysicalPolynomialSpace N m₁ m₂ r hN)).symm
    (LinearMap.toContinuousLinearMap (contourPolynomialBilinForm N m₁ m₂ r hN u hu p))) q=_
  rw [InnerProductSpace.toDual_symm_apply]
  rfl

theorem contourPolynomialOperator_inner_self (p : PhysicalPolynomialSpace N m₁ m₂ r hN) :
    inner ℝ (contourPolynomialOperator N m₁ m₂ r hN u hu p) p=
      positiveContourNorm N m₁ m₂ u (p:ℝ[X]) := by
  rw [contourPolynomialOperator_inner,positiveContourPair_self]

theorem contourPolynomialOperator_isSymmetric :
    (contourPolynomialOperator N m₁ m₂ r hN u hu).IsSymmetric := by
  intro p q
  calc
    inner ℝ (contourPolynomialOperator N m₁ m₂ r hN u hu p) q =
        positiveContourPair N m₁ m₂ u (p:ℝ[X]) q := contourPolynomialOperator_inner _ _ _ _ _ _ _ p q
    _ = positiveContourPair N m₁ m₂ u (q:ℝ[X]) p := positiveContourPair_symm N m₁ m₂ u p q
    _ = inner ℝ (contourPolynomialOperator N m₁ m₂ r hN u hu q) p := (contourPolynomialOperator_inner _ _ _ _ _ _ _ q p).symm
    _ = inner ℝ p (contourPolynomialOperator N m₁ m₂ r hN u hu q) := real_inner_comm _ _

theorem contourPolynomialOperator_nonneg (p : PhysicalPolynomialSpace N m₁ m₂ r hN) :
    0 ≤ inner ℝ (contourPolynomialOperator N m₁ m₂ r hN u hu p) p := by
  rw [contourPolynomialOperator_inner_self]
  exact positiveContourNorm_nonneg N m₁ m₂ hN u p

/-- Intrinsic minmax applied to the two genuine polynomial norms. -/
theorem positiveContour_eigenvalue_le_of_subspace
    (k : Fin r) (S : Submodule ℝ (PhysicalPolynomialSpace N m₁ m₂ r hN))
    (hcodim : Module.finrank ℝ ((PhysicalPolynomialSpace N m₁ m₂ r hN) ⧸ S) ≤ k.val) (A : ℝ)
    (hbound : ∀ p ∈ S, positiveContourNorm N m₁ m₂ u (p:ℝ[X]) ≤
      A*normalizedPhysicalNorm N m₁ m₂ (p:ℝ[X])) :
    (contourPolynomialOperator_isSymmetric N m₁ m₂ r hN u hu).eigenvalues (realDegreeLT_finrank r) k≤A := by
  apply symmetric_eigenvalue_le_of_codimension
    (contourPolynomialOperator N m₁ m₂ r hN u hu)
    (contourPolynomialOperator_isSymmetric N m₁ m₂ r hN u hu)
    (realDegreeLT_finrank r) k S hcodim A
  intro p hp
  rw [contourPolynomialOperator_inner_self,physicalPolynomial_inner_self]
  exact hbound p hp

end Operator
end Zeta3.Analysis

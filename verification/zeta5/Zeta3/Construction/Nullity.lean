import Zeta3.Construction.KernelCancellation
import Zeta3.Construction.HankelAdjoint
import Zeta3.Transfer.KernelPositivity

/-!
# Nullity at most two for the actual cubic Hankel pencil

The least kernel polynomial, its rank-forced extension, the actual cubic
Pearson operators, integer-root propagation, and physical positivity are
assembled here. No Pearson identity, kernel rank, root-integrality, or
positivity conclusion is assumed in the final concrete theorem.
-/

noncomputable section
namespace Zeta3.Construction.Rational
open Polynomial Matrix Module
open Zeta3.Analysis.PhysicalMeasure
open Zeta3.Transfer

theorem concretePearson_momentHankel_nullity_le_two
    (ξ : ℝ) (n : ℕ) (hn : 0 < n) (m : ℕ) (hsize : 34 * n + 1 ≤ m) :
    finrank ℝ (Hankel.momentHankel (concretePearsonFunctional ξ n) m).mulVecLin.ker ≤ 2 := by
  classical
  let L := concretePearsonFunctional ξ n
  let H := Hankel.momentHankel L m
  have hdim : H.rank + finrank ℝ H.mulVecLin.ker = m + 1 := by
    simpa [H, Matrix.rank] using LinearMap.finrank_range_add_finrank_ker H.mulVecLin
  change finrank ℝ H.mulVecLin.ker ≤ 2
  by_contra hnull
  have hnull' : 3 ≤ finrank ℝ H.mulVecLin.ker := by omega
  have hm : 2 ≤ m := by omega
  have hrank : H.rank ≤ m - 2 := by omega
  obtain ⟨p, hp, hpdeg, hpann, hmin, hann⟩ :=
    Hankel.hankel_minimal_monic_kernel_extended L m (m - 2) (by omega) hrank
  have hdiv := Pearson.minimal_kernel_cubic_divisibilities
    (cubicLiftedFunctional ξ (50 * n) (4 * n - 1) (16 * n - 1))
    (50 * n) (4 * n - 1 + 1) (16 * n - 1 + 1) m (2 * m - (m - 2)) p
    (cubicLiftedFunctional_pearson ξ (50 * n) (4 * n - 1) (16 * n - 1))
    (cubicLiftedFunctional_even ξ (50 * n) (4 * n - 1) (16 * n - 1))
    hp (by omega) hpann hmin hann (by omega)
  have hpos : ∀ t : ℝ, 0 < t → 0 < p.eval t :=
    monic_eval_pos_of_cubic_divisibilities (50 * n) (4 * n - 1 + 1) (16 * n - 1 + 1)
      p hp hdiv.1 hdiv.2
  have hpositive := concretePearsonFunctional_remainingPole_pos ξ n hn p hpos
  have hzero : L (p * (remainingPolePolynomial n).map (Rat.castHom ℝ)) = 0 := by
    apply Hankel.recurrence_relations_span L p m hpann
    exact Polynomial.natDegree_map_le.trans (by rw [remainingPolePolynomial_natDegree]; exact hsize)
  exact (ne_of_gt hpositive) hzero

def concreteMomentMatrix (ξ : ℝ) (n r : ℕ) : Matrix (Fin r) (Fin r) ℝ :=
  fun i j => concretePearsonFunctional ξ n (X ^ (i.val + j.val))

theorem concreteMomentMatrix_nullity_le_two (ξ : ℝ) (n : ℕ) (hn : 0 < n)
    (r : ℕ) (hsize : 34 * n + 1 < r) :
    finrank ℝ (concreteMomentMatrix ξ n r).mulVecLin.ker ≤ 2 := by
  cases r with
  | zero => omega
  | succ m =>
    exact concretePearson_momentHankel_nullity_le_two ξ n hn m (by omega)

theorem realHankel_eq_concreteMomentMatrix (ξ : ℝ) (n : ℕ) (hn : 0 < n) :
    realHankelConstant n + ξ • realHankelLinear n = concreteMomentMatrix ξ n (51 * n) := by
  ext i j
  have h := concretePearsonFunctional_monomial ξ n hn (i.val + j.val)
  rw [numeratorFunctional_affine] at h
  simp only [eval₂_add, eval₂_C, eval₂_mul, eval₂_X, Rat.coe_castHom] at h
  change (numeratorConstant (50 * n)
    (positiveFactor (4 * n) * positiveFactor (16 * n) * X ^ (i.val + j.val)) : ℝ) +
      ξ * (numeratorLinear (50 * n)
        (positiveFactor (4 * n) * positiveFactor (16 * n) * X ^ (i.val + j.val)) : ℝ) =
    concretePearsonFunctional ξ n (X ^ (i.val + j.val))
  exact h.symm

/-- The actual evaluated symmetric Hankel pencil has nullity at most two,
for every real candidate value and every stage, including the empty stage. -/
theorem realHankel_nullity_le_two (n : ℕ) (ξ : ℝ) :
    finrank ℝ (realHankelConstant n + ξ • realHankelLinear n).mulVecLin.ker ≤ 2 := by
  by_cases hn : n = 0
  · subst n
    have h := Submodule.finrank_le
      (realHankelConstant 0 + ξ • realHankelLinear 0).mulVecLin.ker
    have hzero : finrank ℝ (Fin (51 * 0) → ℝ) = 0 := by simp
    rw [hzero] at h
    omega
  · have hn' : 0 < n := Nat.pos_of_ne_zero hn
    rw [realHankel_eq_concreteMomentMatrix ξ n hn']
    exact concreteMomentMatrix_nullity_le_two ξ n hn' (51 * n) (by omega)

/-- The actual primitive integer determinant has no real root of multiplicity
greater than two. Both the physical definiteness and nullity inputs are closed. -/
theorem windowIntegerPolynomial_rootMultiplicity_le_two (n : ℕ) (x : ℝ) :
    ((windowIntegerPolynomial n).map (Int.castRingHom ℝ)).rootMultiplicity x ≤ 2 := by
  rw [windowIntegerPolynomial_rootMultiplicity_eq_hankel_nullity n
    (Zeta5.Endpoint.realZeta 3) x (realHankel_realZetaThree_posDef n)]
  exact realHankel_nullity_le_two n x

/-- Closed bounded-jet input for the quantitative irrationality-measure transfer. -/
theorem windowIntegerPolynomial_hasBoundedRationalJets_two :
    HasBoundedRationalJets windowIntegerPolynomial 2 := by
  apply windowIntegerPolynomial_hasBoundedRationalJets (Zeta5.Endpoint.realZeta 3) 2
    realHankel_realZetaThree_posDef
  intro n p q hq
  exact realHankel_nullity_le_two n ((p : ℝ) / (q : ℝ))

end Zeta3.Construction.Rational

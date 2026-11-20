import Zeta3.Analysis.NormRowRate
import Zeta5.Analysis.GramBound

/-! # The actual asymmetric determinant is bounded by monic trial norms -/

noncomputable section
namespace Zeta3.Analysis
open Polynomial Zeta3.Construction
open scoped BigOperators

def windowValue (n : ℕ) : ℝ :=
  (windowDeterminant n).eval₂ (Rat.castHom ℝ) (Zeta5.Endpoint.realZeta 3)

theorem windowValue_eq_physicalGram (n : ℕ) :
    windowValue n = (factorialPrefactor (50 * n) (4 * n) (16 * n) (51 * n) : ℚ) *
      (Zeta5.Analysis.realMonomialGram
        (PhysicalMeasure.windowMomentFunctional (50 * n) (4 * n) (16 * n)) (51 * n)).det := by
  unfold windowValue
  rw [concrete_windowDeterminant_change_of_basis, eval₂_mul, eval₂_C,
    hankelPencil_det_eval_real]
  change _ * (Zeta3.Transfer.realHankelConstant n + Zeta5.Endpoint.realZeta 3 •
    Zeta3.Transfer.realHankelLinear n).det = _
  rw [PhysicalMeasure.realHankel_eq_physicalGram]
  rfl

theorem windowValue_pos (n : ℕ) : 0 < windowValue n := by
  unfold windowValue
  rw [concrete_windowDeterminant_change_of_basis, eval₂_mul, eval₂_C,
    hankelPencil_det_eval_real]
  exact mul_pos (by
    change (0 : ℝ) < (factorialPrefactor (50 * n) (4 * n) (16 * n) (51 * n) : ℝ)
    exact_mod_cast factorialPrefactor_pos (50 * n) (4 * n) (16 * n) (51 * n))
    (PhysicalMeasure.realHankel_realZetaThree_posDef n).det_pos

theorem factorialPrefactor_eq_prod (N m₁ m₂ r : ℕ) :
    (factorialPrefactor N m₁ m₂ r : ℝ) = ∏ k : Fin r, gramNormFactor N m₁ m₂ k.val := by
  simp only [factorialPrefactor, Rat.cast_mul, Rat.cast_pow, Rat.cast_natCast, Rat.cast_prod,
    Rat.cast_inv, gramNormFactor, div_eq_mul_inv, mul_inv_rev,
    Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin, ← pow_mul]
  ring

theorem windowValue_le_trial_norms (n : ℕ) (p : Fin (51 * n) → ℝ[X])
    (hpm : ∀ i, (p i).Monic) (hpd : ∀ i, (p i).natDegree = i.val) :
    windowValue n ≤ (Nat.factorial (51 * n) : ℝ) *
      ∏ i : Fin (51 * n), gramNormFactor (50 * n) (4 * n) (16 * n) i.val *
        windowSquaredNorm (50 * n) (4 * n) (16 * n) (p i) := by
  have h := Zeta5.Analysis.realMonomialGram_det_le_trial_product
    (PhysicalMeasure.windowMomentFunctional (50 * n) (4 * n) (16 * n))
    (PhysicalMeasure.windowMomentFunctional_square_pos (50 * n) (4 * n) (16 * n))
    (51 * n) p hpm hpd
  rw [windowValue_eq_physicalGram]
  apply (mul_le_mul_of_nonneg_left h
    (by exact_mod_cast (factorialPrefactor_pos (50 * n) (4 * n) (16 * n) (51 * n)).le)).trans_eq
  rw [factorialPrefactor_eq_prod, Finset.prod_mul_distrib]
  dsimp only [windowSquaredNorm]
  ring

end Zeta3.Analysis

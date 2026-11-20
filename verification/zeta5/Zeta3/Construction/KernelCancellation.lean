import Zeta3.Construction.CubicWeightCompatibility
import Zeta3.Construction.SharpDegree
import Zeta3.Analysis.CubicPositivity

/-!
# Positive cancellation in the cubic kernel argument

The remaining-pole polynomial cancels the actual denominator. The resulting
functional is the already proved physical cubic moment integral, for every
real polynomial and every candidate ξ, not just at ζ(3).
-/

noncomputable section
namespace Zeta3.Construction.Rational
open Polynomial Zeta5.Construction MeasureTheory Set Filter
open Zeta3.Analysis.PhysicalMeasure
open scoped Topology
variable {K : Type*} [Field K] [CharZero K]

theorem positiveFactor_mul_nodeTail (m d : ℕ) :
    positiveFactor m * nodeTail m d = positiveFactor (m + d) := by
  exact (Finset.prod_range_add (fun a : ℕ => (X : ℚ[X]) + C ((a : ℚ) ^ 2)) m d).symm

theorem positiveFactor_eq_X_mul_denominator (N : ℕ) :
    positiveFactor (N + 1) = X * denominator N := by
  rw [positiveFactor, Finset.prod_range_succ']
  simp only [Nat.cast_zero, zero_pow (by norm_num : 2 ≠ 0), map_zero, add_zero]
  rw [mul_comm]
  rfl

theorem remainingPole_cancellation (n : ℕ) :
    positiveFactor (16 * n) * remainingPolePolynomial n = X * denominator (50 * n) := by
  rw [remainingPolePolynomial, positiveFactor_mul_nodeTail,
    show 16 * n + (34 * n + 1) = 50 * n + 1 by omega,
    positiveFactor_eq_X_mul_denominator]

theorem weighted_remainingPole_cancellation (n : ℕ) (p : ℚ[X]) :
    positiveFactor (4 * n) * positiveFactor (16 * n) * (p * remainingPolePolynomial n) =
      (p * X * positiveFactor (4 * n)) * denominator (50 * n) := by
  calc
    _ = p * positiveFactor (4 * n) *
        (positiveFactor (16 * n) * remainingPolePolynomial n) := by ring
    _ = _ := by rw [remainingPole_cancellation]; ring

theorem concretePearsonFunctional_remainingPole_rational (ξ : K) (n : ℕ) (hn : 0 < n)
    (p : ℚ[X]) :
    concretePearsonFunctional ξ n
        (p.map (Rat.castHom K) * (remainingPolePolynomial n).map (Rat.castHom K)) =
      (polynomialMoment (p * X * positiveFactor (4 * n)) : K) := by
  rw [← Polynomial.map_mul, concretePearsonFunctional_rational ξ n hn,
    weighted_remainingPole_cancellation, numeratorFunctional_mul_denominator, eval₂_C]
  rfl

theorem concretePearsonFunctional_remainingPole_real (ξ : ℝ) (n : ℕ) (hn : 0 < n)
    (p : ℝ[X]) :
    concretePearsonFunctional ξ n (p * (remainingPolePolynomial n).map (Rat.castHom ℝ)) =
      momentFunctional 0 (p * X * realPositiveFactor (4 * n)) := by
  let F : ℝ[X] →ₗ[ℝ] ℝ := (concretePearsonFunctional ξ n).comp
    (LinearMap.mulRight ℝ ((remainingPolePolynomial n).map (Rat.castHom ℝ)))
  let G : ℝ[X] →ₗ[ℝ] ℝ := (momentFunctional 0).comp
    (LinearMap.mulRight ℝ (X * realPositiveFactor (4 * n)))
  have hpow (k : ℕ) : F (X ^ k) = G (X ^ k) := by
    have h := concretePearsonFunctional_remainingPole_rational ξ n hn (X ^ k)
    have hI := momentFunctional_zero_rational (X ^ k * X * positiveFactor (4 * n))
    simp only [Polynomial.map_mul, Polynomial.map_pow, Polynomial.map_X] at h hI
    dsimp only [F, G, LinearMap.comp_apply, LinearMap.mulRight_apply]
    rw [h]
    simpa only [realPositiveFactor, mul_assoc] using hI.symm
  have hmono (H : ℝ[X] →ₗ[ℝ] ℝ) (k : ℕ) (a : ℝ) :
      H (monomial k a) = a * H (X ^ k) := by
    rw [← C_mul_X_pow_eq_monomial, ← smul_eq_C_mul, map_smul, smul_eq_mul]
  have hFG : F = G := by
    apply Polynomial.lhom_ext' (f := F) (g := G)
    intro k
    apply LinearMap.ext
    intro a
    change F (monomial k a) = G (monomial k a)
    rw [hmono F k a, hmono G k a, hpow k]
  have h := LinearMap.congr_fun hFG p
  simpa only [F, G, LinearMap.comp_apply, LinearMap.mulRight_apply, mul_assoc] using h

/-- Positivity after cancellation holds for every candidate value ξ. -/
theorem concretePearsonFunctional_remainingPole_pos (ξ : ℝ) (n : ℕ) (hn : 0 < n)
    (p : ℝ[X]) (hp : ∀ t : ℝ, 0 < t → 0 < p.eval t) :
    0 < concretePearsonFunctional ξ n (p * (remainingPolePolynomial n).map (Rat.castHom ℝ)) := by
  rw [concretePearsonFunctional_remainingPole_real ξ n hn]
  let q := p * X * realPositiveFactor (4 * n)
  have hpos : ∀ᵐ x ∂volume.restrict (Ioi (0 : ℝ)),
      0 < q.eval (x ^ 2) * weightedDensity 0 x := by
    filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with x hx
    simp only [q, eval_mul, eval_X]
    exact mul_pos (mul_pos (mul_pos (hp (x ^ 2) (sq_pos_of_pos hx)) (sq_pos_of_pos hx))
      (realPositiveFactor_eval_pos _ (sq_pos_of_pos hx))) (weightedDensity_pos 0 hx)
  have hnq : 0 ≤ᵐ[volume.restrict (Ioi (0 : ℝ))]
      (fun x => q.eval (x ^ 2) * weightedDensity 0 x) := hpos.mono (fun _ h => h.le)
  have hi := weighted_polynomial_integrable 0 q
  change 0 < momentFunctional 0 q
  have hnonneg : 0 ≤ momentFunctional 0 q := integral_nonneg_of_ae hnq
  apply lt_of_le_of_ne hnonneg
  intro hz
  have hzero := (integral_eq_zero_iff_of_nonneg_ae hnq hi).mp hz.symm
  have hfalse : ∀ᵐ x ∂volume.restrict (Ioi (0 : ℝ)), False := by
    filter_upwards [hpos, hzero] with x hx hz'
    exact (ne_of_gt hx) hz'
  have hvol : volume (Ioi (0 : ℝ)) ≠ 0 := by simp
  haveI : (ae (volume.restrict (Ioi (0 : ℝ)))).NeBot := ae_restrict_neBot.mpr hvol
  obtain ⟨_, hx⟩ := Filter.Eventually.exists hfalse
  exact hx

end Zeta3.Construction.Rational

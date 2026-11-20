import Zeta3.Arithmetic.BernoulliMoments
import Zeta5.Arithmetic.BernoulliDistribution

/-! The exact one-derivative residue-class distribution formula for the
cubic moment functional. This is an identity over the rationals, before
any modular reduction or precision estimate. -/
noncomputable section
namespace Zeta3.Arithmetic
open Polynomial Finset Zeta5.Arithmetic

theorem derivative_comp_localAffine (P : ℚ[X]) (p : ℕ) (c : ℤ) :
    (P.comp (localAffine p c)).derivative =
      C (p : ℚ) * P.derivative.comp (localAffine p c) := by
  rw [derivative_comp]
  simp only [localAffine, derivative_add, derivative_C, derivative_mul,
    derivative_X, zero_mul, mul_one, zero_add]

theorem polynomialMoment_distribution (p : ℕ) (hp : 0 < p) (P : ℚ[X]) :
    (p : ℚ) ^ 2 * Zeta3.Construction.polynomialMoment P =
      (1 / 2 : ℚ) * ∑ c ∈ range p,
        bernoulliFunctional (((bernoulliMomentNumerator P).comp
          (localAffine p (c : ℤ))).derivative) := by
  rw [polynomialMoment_eq_bernoulliFunctional,
    bernoulliFunctional_distribution p hp (bernoulliMomentNumerator P).derivative]
  simp only [derivative_comp_localAffine, bernoulliFunctional_C_mul]
  rw [← mul_sum]
  have hp0 : (p : ℚ) ≠ 0 := by exact_mod_cast hp.ne'
  field_simp
  <;> ring

theorem polynomialMoment_scaled_distribution (p e : ℕ) (hp : 0 < p) (P : ℚ[X]) :
    (p : ℚ) ^ (2 + e) * Zeta3.Construction.polynomialMoment P =
      (1 / 2 : ℚ) * ∑ c ∈ range p,
        bernoulliFunctional ((C ((p : ℚ) ^ e) *
          (bernoulliMomentNumerator P).comp (localAffine p (c : ℤ))).derivative) := by
  simp only [derivative_C_mul, bernoulliFunctional_C_mul]
  rw [← mul_sum, ← mul_assoc, mul_comm (1 / 2 : ℚ) ((p : ℚ) ^ e), mul_assoc,
    ← polynomialMoment_distribution p hp, ← mul_assoc, ← pow_add]
  ring

theorem bernoulliMomentNumerator_comp_localAffine (P : ℚ[X]) (p : ℕ) (c : ℤ) :
    (bernoulliMomentNumerator P).comp (localAffine p c) =
      (localAffine p c) ^ 3 * P.comp (-((localAffine p c) ^ 2)) := by
  simp only [bernoulliMomentNumerator, mul_comp, pow_comp, X_comp, comp_assoc, neg_comp]

end Zeta3.Arithmetic

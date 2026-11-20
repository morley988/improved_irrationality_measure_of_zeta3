import Zeta3.Arithmetic.LocalDeterminant
import Zeta3.Arithmetic.SecondKernelDeterminant
import Zeta3.Construction.FeatureComplete

/-! The first layer with the exact, fully proved feature rank, rather
than the dimension of the ambient restriction target. -/
noncomputable section
namespace Zeta3.Arithmetic
open Polynomial Matrix Module OddZeta.FourValue Zeta5.Construction
open Zeta5.Arithmetic Zeta3.Construction.Features
variable {p : ℕ} [Fact p.Prime]

theorem reducedRestriction_kernel_padic (N m r : ℕ) (hp2 : p ≠ 2)
    (hsmall : 2 * (m + r) - 2 < p ^ 2)
    (x : Fin r → padicIntegralSubring p)
    (hx : (reducedRestrictionMatrix N m r hp2 hsmall).mulVecLin
      (fun i => padicReduction p (x i)) = 0) :
    ∀ a, PadicLower p 1 (∑ i, centralRestrictionMatrix N m r p a i * (x i : ℚ)) := by
  intro a
  let z : padicIntegralSubring p := ∑ i,
    ⟨centralRestrictionMatrix N m r p a i, centralRestrictionMatrix_integral N m r hp2 hsmall a i⟩ * x i
  have hz : padicReduction p z = 0 := by
    simp only [z, map_sum, map_mul]
    exact congrFun hx a
  have h := (padicReduction_eq_zero z).mp hz
  simpa [z] using h

theorem scaledCentralPencil_feature_rank_lower (N m₁ m₂ r : ℕ) (hp : 2 < p)
    (hN : N ≤ max (m₁ + r) (m₂ + r))
    (hsmall : 4 * max (m₁ + r) (m₂ + r) + 4 < p ^ 2)
    (hm : 0 < m₁) (hmJ : m₁ ≤ featureStart m₁ r p) :
    PolynomialPadicLower p ((r : ℤ) - featureRankBound N m₁ r p)
      (scaledCentralPencil N m₁ m₂ r p).det := by
  have h₁ : 2 * (m₁ + r) - 2 < p ^ 2 := by have := le_max_left (m₁+r) (m₂+r); omega
  let R := reducedRestrictionMatrix N m₁ r (by omega : p ≠ 2) h₁
  have h := polynomialPadicLower_det_of_residue_kernel
    (scaledCentralPencil N m₁ m₂ r p) R.mulVecLin
    (scaledCentralPencil_integral N m₁ m₂ r hp hN hsmall) (by
      intro x hx j
      exact scaledCentralPencil_restriction_radical N m₁ m₂ r hp hN hsmall
        (fun i => (x i : ℚ)) (fun i => (x i).property)
        (reducedRestriction_kernel_padic N m₁ r (by omega) h₁ x hx) j)
  change PolynomialPadicLower p ((Fintype.card (Fin r) : ℤ) - R.rank) _ at h
  rw [Fintype.card_fin, reducedRestrictionMatrix_rank N m₁ r (by omega) h₁ hm hmJ] at h
  exact h

theorem unscaledCentralPencil_feature_rank_bound_left (N m₁ m₂ r : ℕ) (hp : 2 < p)
    (hN : N ≤ max (m₁ + r) (m₂ + r))
    (hsmall : 4 * max (m₁ + r) (m₂ + r) + 4 < p ^ 2)
    (hm : 0 < m₁) (hmJ : m₁ ≤ featureStart m₁ r p) :
    PolynomialPadicLower p
      (-(2 + ((2 * (N % p) / p : ℕ) : ℤ)) * (r : ℤ) - featureRankBound N m₁ r p)
      (unscaledCentralPencil N m₁ m₂ r).det := by
  have hdet := scaledCentralPencil_feature_rank_lower N m₁ m₂ r hp hN hsmall hm hmJ
  have h := (PolynomialPadicLower.constant
    (inverse_prime_power_padicLower (p := p) (localPencilScale N p * r))).mul hdet
  rw [scaledCentralPencil_det, ← mul_assoc, ← C_mul] at h
  have hp0 : (p : ℚ) ≠ 0 := by exact_mod_cast (Fact.out : p.Prime).ne_zero
  rw [inv_mul_cancel₀ (pow_ne_zero _ hp0), C_1, one_mul] at h
  convert h using 1
  simp only [localPencilScale, Nat.cast_mul, Nat.cast_add, Nat.cast_ofNat]
  ring

theorem unscaledCentralPencil_feature_rank_bound (N m₁ m₂ r : ℕ) (hp : 2 < p)
    (hN : N ≤ max (m₁ + r) (m₂ + r))
    (hsmall : 4 * max (m₁ + r) (m₂ + r) + 4 < p ^ 2)
    (hm₁ : 0 < m₁) (hm₂ : 0 < m₂)
    (hmJ₁ : m₁ ≤ featureStart m₁ r p) (hmJ₂ : m₂ ≤ featureStart m₂ r p) :
    PolynomialPadicLower p
      (-(2 + ((2 * (N % p) / p : ℕ) : ℤ)) * (r : ℤ) -
        min (featureRankBound N m₁ r p) (featureRankBound N m₂ r p))
      (unscaledCentralPencil N m₁ m₂ r).det := by
  by_cases hh : featureRankBound N m₁ r p ≤ featureRankBound N m₂ r p
  · simpa only [min_eq_left hh] using
      unscaledCentralPencil_feature_rank_bound_left N m₁ m₂ r hp hN hsmall hm₁ hmJ₁
  · have h := unscaledCentralPencil_feature_rank_bound_left N m₂ m₁ r hp
      (by simpa only [max_comm] using hN) (by simpa only [max_comm] using hsmall) hm₂ hmJ₂
    rw [← unscaledCentralPencil_transpose, Matrix.det_transpose] at h
    simpa only [min_eq_right (Nat.le_of_lt (Nat.lt_of_not_ge hh))] using h

end Zeta3.Arithmetic

import Zeta3.Arithmetic.RestrictionPencil
import Zeta5.Arithmetic.RestrictionDeterminant

/-!
# First local arithmetic layer for the actual cubic determinant

The estimate uses the smaller of the two actual restriction spaces. At
N=50n, m₁=4n, m₂=16n and r=51n, this is the first window, whose local degree
is floor((110n-2)/p). This is the first layer only; the second reduction of
the bilinear form modulo p² is a separate obligation.
-/

noncomputable section
namespace Zeta3.Arithmetic
open Polynomial OddZeta.FourValue Zeta5.Construction
open Zeta5.Arithmetic

variable {p : ℕ} [Fact p.Prime]

def unscaledCentralPencil (N m₁ m₂ r : ℕ) : Matrix (Fin r) (Fin r) ℚ[X] :=
  fun i j => Zeta3.Construction.entry N (m₁ + i.val) (m₂ + j.val)

theorem scaledCentralPencil_det (N m₁ m₂ r p : ℕ) :
    (scaledCentralPencil N m₁ m₂ r p).det =
      C ((p : ℚ) ^ (localPencilScale N p * r)) *
        (unscaledCentralPencil N m₁ m₂ r).det := by
  change (C ((p : ℚ) ^ localPencilScale N p) • unscaledCentralPencil N m₁ m₂ r).det = _
  rw [Matrix.det_smul, Fintype.card_fin, ← C_pow, ← pow_mul]

theorem unscaledCentralPencil_lower_of_scaled (N m₁ m₂ r d : ℕ)
    (hdet : PolynomialPadicLower p ((r : ℤ) - (min r d : ℕ))
      (scaledCentralPencil N m₁ m₂ r p).det) :
    PolynomialPadicLower p
      (-(2 + ((2 * (N % p) / p : ℕ) : ℤ)) * (r : ℤ) - (min r d : ℕ))
      (unscaledCentralPencil N m₁ m₂ r).det := by
  have h := (PolynomialPadicLower.constant
    (inverse_prime_power_padicLower (p := p) (localPencilScale N p * r))).mul hdet
  rw [scaledCentralPencil_det, ← mul_assoc, ← C_mul] at h
  have hp0 : (p : ℚ) ≠ 0 := by exact_mod_cast (Fact.out : p.Prime).ne_zero
  rw [inv_mul_cancel₀ (pow_ne_zero _ hp0), C_1, one_mul] at h
  convert h using 1
  simp only [localPencilScale, Nat.cast_mul, Nat.cast_add, Nat.cast_ofNat]
  ring

theorem unscaledCentralPencil_transpose (N m₁ m₂ r : ℕ) :
    (unscaledCentralPencil N m₁ m₂ r).transpose = unscaledCentralPencil N m₂ m₁ r := by
  ext i j : 2
  simp only [Matrix.transpose_apply, unscaledCentralPencil,
    Zeta3.Construction.entry_eq_numeratorFunctional]
  rw [mul_comm (windowBasis (m₁ + j.val)) (windowBasis (m₂ + i.val))]

theorem unscaledCentralPencil_restriction_bound_left (N m₁ m₂ r : ℕ) (hp : 2 < p)
    (hN : N ≤ max (m₁ + r) (m₂ + r))
    (hsmall : 4 * max (m₁ + r) (m₂ + r) + 4 < p ^ 2) :
    PolynomialPadicLower p
      (-(2 + ((2 * (N % p) / p : ℕ) : ℤ)) * (r : ℤ) -
        (min r ((restrictionDepth m₁ r p + 1) * (maximalReflectedClasses N p).card) : ℕ))
      (unscaledCentralPencil N m₁ m₂ r).det := by
  have hm₁ := le_max_left (m₁ + r) (m₂ + r)
  have h := polynomialPadicLower_det_of_restriction_kernel
    (scaledCentralPencil N m₁ m₂ r p) (centralRestrictionMatrix N m₁ r p)
    (scaledCentralPencil_integral N m₁ m₂ r hp hN hsmall)
    (centralRestrictionMatrix_integral N m₁ r (by omega) (by omega))
    (scaledCentralPencil_restriction_radical N m₁ m₂ r hp hN hsmall)
  rw [Fintype.card_fin, windowRestrictionIndex_card] at h
  exact unscaledCentralPencil_lower_of_scaled N m₁ m₂ r _ h

theorem unscaledCentralPencil_restriction_bound (N m₁ m₂ r : ℕ) (hp : 2 < p)
    (hN : N ≤ max (m₁ + r) (m₂ + r))
    (hsmall : 4 * max (m₁ + r) (m₂ + r) + 4 < p ^ 2) :
    PolynomialPadicLower p
      (-(2 + ((2 * (N % p) / p : ℕ) : ℤ)) * (r : ℤ) -
        (min r ((min (restrictionDepth m₁ r p) (restrictionDepth m₂ r p) + 1) *
          (maximalReflectedClasses N p).card) : ℕ))
      (unscaledCentralPencil N m₁ m₂ r).det := by
  by_cases h : restrictionDepth m₁ r p ≤ restrictionDepth m₂ r p
  · simpa only [min_eq_left h] using
      unscaledCentralPencil_restriction_bound_left N m₁ m₂ r hp hN hsmall
  · have hright := unscaledCentralPencil_restriction_bound_left N m₂ m₁ r hp
      (by simpa only [max_comm] using hN) (by simpa only [max_comm] using hsmall)
    rw [← unscaledCentralPencil_transpose, Matrix.det_transpose] at hright
    simpa only [min_eq_right (Nat.le_of_lt (Nat.lt_of_not_ge h))] using hright

theorem windowDeterminant_local_restriction_bound (n : ℕ) (hp : 2 < p)
    (hsmall : 268 * n + 4 < p ^ 2) :
    PolynomialPadicLower p
      (-(2 + ((2 * ((50 * n) % p) / p : ℕ) : ℤ)) * (51 * n : ℕ) -
        (min (51 * n) (((110 * n - 2) / p + 1) *
          (if 2 * ((50 * n) % p) < p then (50 * n) % p
           else (50 * n) % p - (p - 1) / 2)) : ℕ))
      (Zeta3.Construction.windowDeterminant n) := by
  have h := unscaledCentralPencil_restriction_bound_left (p := p)
    (50 * n) (4 * n) (16 * n) (51 * n) hp (by omega) (by omega)
  rw [maximalReflectedClasses_card (50 * n) p
    ((Fact.out : p.Prime).mod_two_eq_one_iff_ne_two.mpr (by omega))] at h
  have he : unscaledCentralPencil (50 * n) (4 * n) (16 * n) (51 * n) =
      Zeta3.Construction.windowPencil n := rfl
  rw [he] at h
  simpa only [restrictionDepth, show 2 * (4 * n + 51 * n) = 110 * n by omega,
    Zeta3.Construction.windowDeterminant] using h

end Zeta3.Arithmetic

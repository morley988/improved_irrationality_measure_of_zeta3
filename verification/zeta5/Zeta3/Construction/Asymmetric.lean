import Zeta3.Construction.Determinant
import Zeta5.Construction.BasisChange

/-!
# Unequal factorial windows and the actual symmetric Hankel pencil

The row and column windows are different.  The algebraic bridge therefore is
a two-sided equivalence, not a congruence using one basis matrix.  This module
proves the required mixed change of basis, including the exact prefactor.

At the concrete parameters `m₁=4n` and `m₂=16n`, the common factors have even
sign, so the Hankel numerator is exactly `C_(4n) C_(16n)` with positive square
root factors.  No positivity or physical-measure identity is postulated.
-/

noncomputable section
namespace Zeta3.Construction

open Polynomial
open Zeta5.Construction

/-- The manuscript's positive-root product `C_m(t)`. -/
def positiveFactor (m : ℕ) : ℚ[X] :=
  ∏ a ∈ Finset.range m, (X + C ((a : ℚ) ^ 2))

theorem positiveFactor_monic (m : ℕ) : (positiveFactor m).Monic := by
  exact monic_prod_of_monic _ _ (fun a _ => monic_X_add_C _)

theorem positiveFactor_natDegree (m : ℕ) : (positiveFactor m).natDegree = m := by
  rw [positiveFactor, natDegree_prod_of_monic]
  · simp only [natDegree_X_add_C, Finset.sum_const, Finset.card_range, smul_eq_mul, mul_one]
  · intro a ha
    exact monic_X_add_C _

theorem positiveFactor_eval_neg_square_eq_zero {i m : ℕ} (him : i < m) :
    (positiveFactor m).eval (-((i : ℚ) ^ 2)) = 0 := by
  rw [positiveFactor, eval_prod]
  apply Finset.prod_eq_zero (Finset.mem_range.mpr him)
  simp

theorem commonFactor_eq_signed_positiveFactor (m : ℕ) :
    commonFactor m = C ((-1 : ℚ) ^ m) * positiveFactor m := by
  simp only [commonFactor, rootPolynomial, prod_comp, sub_comp, X_comp, C_comp]
  calc
    (∏ a ∈ Finset.range m, (-X - C ((a : ℚ) ^ 2) : ℚ[X])) =
        ∏ a ∈ Finset.range m, C (-1 : ℚ) * (X + C ((a : ℚ) ^ 2)) := by
      apply Finset.prod_congr rfl
      intro a ha
      simp only [C_neg, C_1]
      ring
    _ = C ((-1 : ℚ) ^ m) * positiveFactor m := by
      rw [Finset.prod_mul_distrib]
      simp only [Finset.prod_const, Finset.card_range, ← map_pow, positiveFactor]

theorem commonFactor_even (m : ℕ) :
    commonFactor (2 * m) = positiveFactor (2 * m) := by
  rw [commonFactor_eq_signed_positiveFactor, pow_mul]
  norm_num

/-- Mixed-family polynomial-valued Gram change of basis. -/
theorem polynomialValuedMixedGram_change_of_basis
    (L : ℚ[X] →ₗ[ℚ] ℚ[X]) (r : ℕ)
    (p q : Fin r → ℚ[X]) (hp : ∀ i, (p i).natDegree < r)
    (hq : ∀ i, (q i).natDegree < r) :
    (fun i j => L (p i * q j) : Matrix (Fin r) (Fin r) ℚ[X]) =
      (coefficientMatrix r p).transpose * monomialGram L r * coefficientMatrix r q := by
  ext i j : 2
  conv_lhs => rw [polynomial_finite_expansion r (p i) (hp i),
    polynomial_finite_expansion r (q j) (hq j)]
  simp only [Matrix.mul_apply, Matrix.transpose_apply, monomialGram, coefficientMatrix,
    Finset.sum_mul, Finset.mul_sum, map_sum]
  apply Finset.sum_congr rfl
  intro b _
  apply Finset.sum_congr rfl
  intro a _
  rw [show (C ((p i).coeff a.val) * X ^ a.val) *
        (C ((q j).coeff b.val) * X ^ b.val) =
      (((p i).coeff a.val) * ((q j).coeff b.val)) • X ^ (a.val + b.val) by
        rw [Polynomial.smul_eq_C_mul, map_mul, pow_add]; ring,
    map_smul, Polynomial.smul_eq_C_mul, map_mul]
  ring

def weightedNumeratorFunctional (N m₁ m₂ : ℕ) : ℚ[X] →ₗ[ℚ] ℚ[X] :=
  (numeratorFunctional N).comp
    (LinearMap.mulLeft ℚ (commonFactor m₁ * commonFactor m₂))

def monomialPencil (N m₁ m₂ r : ℕ) : Matrix (Fin r) (Fin r) ℚ[X] :=
  monomialGram (weightedNumeratorFunctional N m₁ m₂) r

theorem unscaledWindow_equivalence (N m₁ m₂ r : ℕ) :
    (fun i j : Fin r => numeratorFunctional N
      (windowBasis (m₁ + i.val) * windowBasis (m₂ + j.val))) =
      (windowTailMatrix m₁ r).transpose * monomialPencil N m₁ m₂ r *
        windowTailMatrix m₂ r := by
  have h := polynomialValuedMixedGram_change_of_basis
    (weightedNumeratorFunctional N m₁ m₂) r
    (fun k => windowTail m₁ k.val) (fun k => windowTail m₂ k.val)
    (fun k => by rw [windowTail_natDegree]; exact k.isLt)
    (fun k => by rw [windowTail_natDegree]; exact k.isLt)
  change _ = (coefficientMatrix r (fun k => windowTail m₁ k.val)).transpose *
    monomialGram (weightedNumeratorFunctional N m₁ m₂) r *
      coefficientMatrix r (fun k => windowTail m₂ k.val)
  rw [← h]
  funext i j
  simp only [windowBasis_eq_commonFactor_mul_tail, weightedNumeratorFunctional,
    LinearMap.comp_apply, LinearMap.mulLeft_apply]
  congr 1
  ring

theorem windowTailMatrix_det_ne_zero (m r : ℕ) :
    (windowTailMatrix m r).det ≠ 0 := by
  rw [windowTailMatrix_det]
  apply Finset.prod_ne_zero_iff.mpr
  intro k hk
  apply C_ne_zero.mpr
  apply mul_ne_zero
  · exact inv_ne_zero (factorial_cast_ne_zero _)
  · exact pow_ne_zero _ (by norm_num)

/-- In the two-sided basis change, the alternating leading signs cancel. -/
theorem windowTailMatrix_det_mul (m₁ m₂ r : ℕ) :
    (windowTailMatrix m₁ r).det * (windowTailMatrix m₂ r).det =
      C (∏ k : Fin r, (Nat.factorial (2 * (m₁ + k.val)) : ℚ)⁻¹ *
        (Nat.factorial (2 * (m₂ + k.val)) : ℚ)⁻¹) := by
  rw [windowTailMatrix_det, windowTailMatrix_det, ← Finset.prod_mul_distrib, map_prod]
  apply Finset.prod_congr rfl
  intro k hk
  rw [← map_mul]
  congr 1
  have hs : ((-1 : ℚ) ^ k.val) ^ 2 = 1 := by
    rw [← pow_mul, Nat.mul_comm k.val 2, pow_mul]
    norm_num
  calc
    _ = ((Nat.factorial (2 * (m₁ + k.val)) : ℚ)⁻¹ *
        (Nat.factorial (2 * (m₂ + k.val)) : ℚ)⁻¹) * ((-1 : ℚ) ^ k.val) ^ 2 := by ring
    _ = _ := by rw [hs, mul_one]

def factorialPrefactor (N m₁ m₂ r : ℕ) : ℚ :=
  (Nat.factorial N : ℚ) ^ (2 * r) *
    ∏ k : Fin r, (Nat.factorial (2 * (m₁ + k.val)) : ℚ)⁻¹ *
      (Nat.factorial (2 * (m₂ + k.val)) : ℚ)⁻¹

theorem factorialPrefactor_pos (N m₁ m₂ r : ℕ) :
    0 < factorialPrefactor N m₁ m₂ r := by
  unfold factorialPrefactor
  apply mul_pos
  · exact pow_pos (by exact_mod_cast Nat.factorial_pos N) _
  · apply Finset.prod_pos
    intro k hk
    apply mul_pos <;> apply inv_pos.mpr <;> exact_mod_cast Nat.factorial_pos _

/-- Exact change of determinant for two arbitrary factorial windows. -/
theorem windowDeterminant_change_of_basis (N m₁ m₂ r : ℕ) :
    Matrix.det (fun i j : Fin r => entry N (m₁ + i.val) (m₂ + j.val)) =
      C (factorialPrefactor N m₁ m₂ r) * (monomialPencil N m₁ m₂ r).det := by
  have heq : (fun i j : Fin r => entry N (m₁ + i.val) (m₂ + j.val)) =
      C ((Nat.factorial N : ℚ) ^ 2) •
        ((windowTailMatrix m₁ r).transpose * monomialPencil N m₁ m₂ r *
          windowTailMatrix m₂ r) := by
    rw [← unscaledWindow_equivalence]
    funext i j
    exact entry_eq_numeratorFunctional N (m₁ + i.val) (m₂ + j.val)
  rw [heq, Matrix.det_smul, Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose]
  rw [show (windowTailMatrix m₁ r).det * (monomialPencil N m₁ m₂ r).det *
      (windowTailMatrix m₂ r).det =
      ((windowTailMatrix m₁ r).det * (windowTailMatrix m₂ r).det) *
        (monomialPencil N m₁ m₂ r).det by ring]
  rw [windowTailMatrix_det_mul, ← mul_assoc, ← map_pow, ← map_mul]
  simp only [Fintype.card_fin, ← pow_mul, factorialPrefactor]

/-- The actual unsigned weighted numerator functional at stage `n`. -/
def hankelFunctional (n : ℕ) : ℚ[X] →ₗ[ℚ] ℚ[X] :=
  (numeratorFunctional (50 * n)).comp
    (LinearMap.mulLeft ℚ (positiveFactor (4 * n) * positiveFactor (16 * n)))

/-- The actual symmetric Hankel pencil, with unsigned products `C_m`. -/
def hankelPencil (n : ℕ) : Matrix (Fin (51 * n)) (Fin (51 * n)) ℚ[X] :=
  fun i j => numeratorFunctional (50 * n)
    (positiveFactor (4 * n) * positiveFactor (16 * n) * X ^ (i.val + j.val))

theorem hankelPencil_eq_monomialGram (n : ℕ) :
    hankelPencil n = monomialGram (hankelFunctional n) (51 * n) := rfl

def hankelConstant (n : ℕ) : Matrix (Fin (51 * n)) (Fin (51 * n)) ℚ :=
  fun i j => numeratorConstant (50 * n)
    (positiveFactor (4 * n) * positiveFactor (16 * n) * X ^ (i.val + j.val))

def hankelLinear (n : ℕ) : Matrix (Fin (51 * n)) (Fin (51 * n)) ℚ :=
  fun i j => numeratorLinear (50 * n)
    (positiveFactor (4 * n) * positiveFactor (16 * n) * X ^ (i.val + j.val))

theorem hankelPencil_eq_affinePencil (n : ℕ) :
    hankelPencil n = Zeta5.Analysis.affinePencil (hankelConstant n) (hankelLinear n) := by
  funext i j
  exact numeratorFunctional_affine (50 * n)
    (positiveFactor (4 * n) * positiveFactor (16 * n) * X ^ (i.val + j.val))

theorem hankelConstant_isSymm (n : ℕ) : (hankelConstant n).IsSymm := by
  ext i j
  simp only [Matrix.transpose_apply, hankelConstant, Nat.add_comm]

theorem hankelLinear_isSymm (n : ℕ) : (hankelLinear n).IsSymm := by
  ext i j
  simp only [Matrix.transpose_apply, hankelLinear, Nat.add_comm]

theorem hankelPencil_det_eval_real (n : ℕ) (x : ℝ) :
    ((hankelPencil n).det).eval₂ (Rat.castHom ℝ) x =
      ((hankelConstant n).map (Rat.castHom ℝ) + x •
        (hankelLinear n).map (Rat.castHom ℝ)).det := by
  rw [hankelPencil_eq_affinePencil]
  exact Zeta5.Analysis.eval₂_affineDet (hankelConstant n) (hankelLinear n) (Rat.castHom ℝ) x

theorem concrete_monomialPencil_eq_hankelPencil (n : ℕ) :
    monomialPencil (50 * n) (4 * n) (16 * n) (51 * n) = hankelPencil n := by
  funext i j
  simp only [monomialPencil, monomialGram, weightedNumeratorFunctional,
    LinearMap.comp_apply, LinearMap.mulLeft_apply, hankelPencil]
  rw [show 4 * n = 2 * (2 * n) by omega,
    show 16 * n = 2 * (8 * n) by omega, commonFactor_even, commonFactor_even]

theorem hankelPencil_isSymm (n : ℕ) : (hankelPencil n).IsSymm := by
  ext i j
  simp only [Matrix.transpose_apply, hankelPencil, Nat.add_comm]

/-- The actual cubic determinant is a nonzero rational constant times the
determinant of its actual symmetric Hankel pencil. -/
theorem concrete_windowDeterminant_change_of_basis (n : ℕ) :
    windowDeterminant n =
      C (factorialPrefactor (50 * n) (4 * n) (16 * n) (51 * n)) *
        (hankelPencil n).det := by
  change Matrix.det (fun i j : Fin (51 * n) =>
    entry (50 * n) (4 * n + i.val) (16 * n + j.val)) = _
  rw [windowDeterminant_change_of_basis, concrete_monomialPencil_eq_hankelPencil]

theorem windowDeterminant_ne_zero_iff_hankel (n : ℕ) :
    windowDeterminant n ≠ 0 ↔ (hankelPencil n).det ≠ 0 := by
  rw [concrete_windowDeterminant_change_of_basis]
  have hc : (C (factorialPrefactor (50 * n) (4 * n) (16 * n) (51 * n)) : ℚ[X]) ≠ 0 :=
    C_ne_zero.mpr (factorialPrefactor_pos _ _ _ _).ne'
  constructor
  · intro h hzero
    apply h
    rw [hzero, mul_zero]
  · intro h
    exact mul_ne_zero hc h

end Zeta3.Construction

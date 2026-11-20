import Zeta3.Construction.Functional
import Zeta5.Endpoint.PrimitiveNormalization

/-!
# The concrete asymmetric cubic determinant and its primitive normalization

The stage index is exact: `N=50n`, `m₁=4n`, `m₂=16n`, `r=51n`.
This module proves the affine evaluation identity and the matrix-size degree
bound.  The sharper degree `34n+1`, physical positivity, and the analytic and
arithmetic rates are separate obligations, not assumptions hidden here.
-/

noncomputable section
namespace Zeta3.Construction

open Polynomial
open Zeta5.Construction

def numerator (j k : ℕ) : ℚ[X] := windowBasis j * windowBasis k

def residueWeight (N j k i : ℕ) : ℚ :=
  (numerator j k).eval (pole i) / (denominator N).derivative.eval (pole i)

def entryConstant (N j k : ℕ) : ℚ :=
  (Nat.factorial N : ℚ) ^ 2 *
    (polynomialMoment (numerator j k / denominator N) +
      ∑ i ∈ Finset.range N, residueWeight N j k (i + 1) * stieltjesConstant (i + 1))

def entryLinear (N j k : ℕ) : ℚ :=
  (Nat.factorial N : ℚ) ^ 2 *
    ∑ i ∈ Finset.range N, residueWeight N j k (i + 1) * ((i + 1 : ℕ) : ℚ) ^ 2

def entry (N j k : ℕ) : ℚ[X] :=
  C (entryConstant N j k) + X * C (entryLinear N j k)

theorem entry_eq_numeratorFunctional (N j k : ℕ) :
    entry N j k = C ((Nat.factorial N : ℚ) ^ 2) *
      numeratorFunctional N (windowBasis j * windowBasis k) := by
  rw [numeratorFunctional_apply]
  simp only [entry, entryConstant, entryLinear, residueWeight, numerator,
    stieltjes, map_add, map_mul, map_sum]
  simp only [Finset.mul_sum, Finset.sum_mul, mul_add, Finset.sum_add_distrib]
  ring

theorem residueWeight_eq_zero_of_lt_left {N j k i : ℕ} (hij : i < j) :
    residueWeight N j k i = 0 := by
  simp [residueWeight, numerator, pole, windowBasis_eval_neg_square_eq_zero hij]

theorem residueWeight_eq_zero_of_lt_right {N j k i : ℕ} (hik : i < k) :
    residueWeight N j k i = 0 := by
  simp [residueWeight, numerator, pole, windowBasis_eval_neg_square_eq_zero hik]

def windowPencil (n : ℕ) : Matrix (Fin (51 * n)) (Fin (51 * n)) ℚ[X] :=
  fun j k => entry (50 * n) (4 * n + j.val) (16 * n + k.val)

def windowConstant (n : ℕ) : Matrix (Fin (51 * n)) (Fin (51 * n)) ℚ :=
  fun j k => entryConstant (50 * n) (4 * n + j.val) (16 * n + k.val)

def windowLinear (n : ℕ) : Matrix (Fin (51 * n)) (Fin (51 * n)) ℚ :=
  fun j k => entryLinear (50 * n) (4 * n + j.val) (16 * n + k.val)

/-- The actual `F_(50n)` of the zeta(3) manuscript. -/
def windowDeterminant (n : ℕ) : ℚ[X] := (windowPencil n).det

theorem windowDeterminant_eq_affineDet (n : ℕ) :
    windowDeterminant n = Zeta5.Analysis.affineDet (windowConstant n) (windowLinear n) := rfl

theorem windowDeterminant_natDegree_le_size (n : ℕ) :
    (windowDeterminant n).natDegree ≤ 51 * n := by
  rw [windowDeterminant_eq_affineDet]
  simpa using Zeta5.Analysis.affineDet_natDegree_le (windowConstant n) (windowLinear n)

theorem windowDeterminant_eval_real (n : ℕ) (x : ℝ) :
    (windowDeterminant n).eval₂ (Rat.castHom ℝ) x =
      ((windowConstant n).map (Rat.castHom ℝ) + x •
        (windowLinear n).map (Rat.castHom ℝ)).det := by
  rw [windowDeterminant_eq_affineDet, Zeta5.Analysis.eval₂_affineDet]

def windowNormalizer (n : ℕ) : ℚ :=
  Zeta5.Endpoint.primitiveNormalizer (windowDeterminant n)

def windowIntegerPolynomial (n : ℕ) : ℤ[X] :=
  Zeta5.Endpoint.normalizedPolynomial (windowDeterminant n)

theorem windowNormalizer_pos (n : ℕ) : 0 < windowNormalizer n :=
  Zeta5.Endpoint.primitiveNormalizer_pos _

theorem windowIntegerPolynomial_map (n : ℕ) :
    (windowIntegerPolynomial n).map (algebraMap ℤ ℚ) =
      C (windowNormalizer n) * windowDeterminant n :=
  Zeta5.Endpoint.normalizedPolynomial_map _

theorem windowIntegerPolynomial_natDegree (n : ℕ) :
    (windowIntegerPolynomial n).natDegree = (windowDeterminant n).natDegree :=
  Zeta5.Endpoint.normalizedPolynomial_natDegree _

theorem windowIntegerPolynomial_natDegree_le_size (n : ℕ) :
    (windowIntegerPolynomial n).natDegree ≤ 51 * n := by
  rw [windowIntegerPolynomial_natDegree]
  exact windowDeterminant_natDegree_le_size n

theorem windowIntegerPolynomial_isPrimitive (n : ℕ)
    (hF : windowDeterminant n ≠ 0) :
    (windowIntegerPolynomial n).IsPrimitive :=
  Zeta5.Endpoint.normalizedPolynomial_isPrimitive _ hF

theorem windowIntegerPolynomial_eval_real (n : ℕ) (x : ℝ) :
    (windowIntegerPolynomial n).eval₂ (Int.castRingHom ℝ) x =
      (windowNormalizer n : ℝ) * (windowDeterminant n).eval₂ (Rat.castHom ℝ) x :=
  Zeta5.Endpoint.normalizedPolynomial_eval_real _ _

end Zeta3.Construction

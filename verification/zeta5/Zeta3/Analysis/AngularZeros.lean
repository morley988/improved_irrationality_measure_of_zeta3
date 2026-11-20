import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.Algebra.Polynomial.Degree.SmallDegree
import Mathlib.Analysis.Complex.Basic
import Mathlib.LinearAlgebra.Dimension.RankNullity
import Mathlib.LinearAlgebra.Dimension.DivisionRing
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.RingTheory.Polynomial.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# The finite algebra of distributed angular zeros

The real quadratic `Q_h(z) = z² + 2 a (1-h) z + a²` is bounded below by
`a²` on the nonnegative real axis, while its modulus on `|z| = a` is
exactly the angular zero factor used in the manuscript.  Multiplication
by a product of `m` such quadratics defines a subspace of codimension
`2*m` in the relevant truncated polynomial space.

These are finite algebraic statements.  No angular equilibrium,
quantile discretization, contour norm bound, or spectral estimate is
assumed or asserted in this file.
-/

noncomputable section
open Polynomial
open scoped BigOperators

namespace Zeta3.Analysis

def angularZeroFactor (a h : ℝ) : ℝ[X] :=
  X ^ 2 + C (2*a*(1-h))*X + C (a^2)

@[simp] theorem angularZeroFactor_eval (a h x : ℝ) :
    (angularZeroFactor a h).eval x = x^2 + 2*a*(1-h)*x + a^2 := by
  simp [angularZeroFactor]

@[simp] theorem angularZeroFactor_eval₂ (a h : ℝ) (z : ℂ) :
    (angularZeroFactor a h).eval₂ Complex.ofRealHom z =
      z^2 + (2*a*(1-h) : ℝ)*z + (a^2 : ℝ) := by
  simp [angularZeroFactor, Polynomial.eval₂_pow]

theorem angularZeroFactor_monic (a h : ℝ) :
    (angularZeroFactor a h).Monic := by
  have hq := Polynomial.leadingCoeff_quadratic (R := ℝ)
    (a := 1) (b := 2*a*(1-h)) (c := a^2) (by norm_num : (1:ℝ) ≠ 0)
  simpa [angularZeroFactor, Polynomial.Monic] using hq

@[simp] theorem angularZeroFactor_natDegree (a h : ℝ) :
    (angularZeroFactor a h).natDegree = 2 := by
  have hq := Polynomial.natDegree_quadratic (R := ℝ)
    (a := 1) (b := 2*a*(1-h)) (c := a^2) (by norm_num : (1:ℝ) ≠ 0)
  simpa [angularZeroFactor] using hq

theorem angularZeroFactor_physical_lower (a h x : ℝ)
    (ha : 0 ≤ a) (hh : h ≤ 1) (hx : 0 ≤ x) :
    a^2 ≤ (angularZeroFactor a h).eval x := by
  rw [angularZeroFactor_eval]
  have hp : 0 ≤ 2*a*(1-h)*x := mul_nonneg
    (mul_nonneg (mul_nonneg (by norm_num) ha) (sub_nonneg.mpr hh)) hx
  nlinarith [sq_nonneg x]

/-- On the circle, the quadratic is a real scalar multiple of `z`.
This avoids any trigonometric choice of an argument. -/
theorem angularZeroFactor_circle_factor (a h : ℝ) (z : ℂ)
    (hz : Complex.normSq z = a^2) :
    (angularZeroFactor a h).eval₂ Complex.ofRealHom z =
      (2*(z.re+a*(1-h)) : ℝ)*z := by
  rw [angularZeroFactor_eval₂]
  have hz' : z.re^2 + z.im^2 = a^2 := by
    simpa only [Complex.normSq_apply, pow_two] using hz
  apply Complex.ext <;> simp only [Complex.add_re, Complex.add_im,
    Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
    pow_two, zero_mul, mul_zero, add_zero, sub_zero]
  · nlinarith
  · ring

theorem angularZeroFactor_normSq_circle (a h : ℝ) (z : ℂ)
    (hz : Complex.normSq z = a^2) :
    Complex.normSq ((angularZeroFactor a h).eval₂ Complex.ofRealHom z) =
      4*a^2*(z.re+a*(1-h))^2 := by
  rw [angularZeroFactor_circle_factor a h z hz, Complex.normSq_mul,
    Complex.normSq_ofReal, hz]
  ring

/-- The literal normalized factor `a⁴ (2 |y-h|)²`, where
`y = 1 + Re(z)/a`, used in the angular logarithmic potential. -/
theorem angularZeroFactor_normSq_normalized (a h : ℝ) (z : ℂ)
    (ha : a ≠ 0) (hz : Complex.normSq z = a^2) :
    Complex.normSq ((angularZeroFactor a h).eval₂ Complex.ofRealHom z) =
      a^4 * (2*|1+z.re/a-h|)^2 := by
  rw [angularZeroFactor_normSq_circle a h z hz, mul_pow, sq_abs]
  field_simp
  <;> ring

def angularZeroProduct {m : ℕ} (a : ℝ) (h : Fin m → ℝ) : ℝ[X] :=
  ∏ j, angularZeroFactor a (h j)

theorem angularZeroProduct_monic {m : ℕ} (a : ℝ) (h : Fin m → ℝ) :
    (angularZeroProduct a h).Monic := by
  exact Polynomial.monic_prod_of_monic _ _ (fun j _ => angularZeroFactor_monic a (h j))

@[simp] theorem angularZeroProduct_natDegree {m : ℕ} (a : ℝ) (h : Fin m → ℝ) :
    (angularZeroProduct a h).natDegree = 2*m := by
  unfold angularZeroProduct
  rw [Polynomial.natDegree_prod_of_monic _ _
    (fun j _ => angularZeroFactor_monic a (h j))]
  simp [Nat.mul_comm]

theorem angularZeroProduct_eval {m : ℕ} (a : ℝ) (h : Fin m → ℝ) (x : ℝ) :
    (angularZeroProduct a h).eval x = ∏ j, (angularZeroFactor a (h j)).eval x := by
  exact map_prod (Polynomial.evalRingHom x) _ _

theorem angularZeroProduct_physical_lower {m : ℕ} (a : ℝ) (h : Fin m → ℝ)
    (x : ℝ) (ha : 0 ≤ a) (hh : ∀ j, h j ≤ 1) (hx : 0 ≤ x) :
    a^(2*m) ≤ (angularZeroProduct a h).eval x := by
  rw [angularZeroProduct_eval]
  have hp := Finset.prod_le_prod (fun (j : Fin m) (_ : j ∈ Finset.univ) => sq_nonneg a)
    (fun j _ => angularZeroFactor_physical_lower a (h j) x ha (hh j) hx)
  simpa [← pow_mul] using hp

theorem angularZeroProduct_physical_square_lower {m : ℕ} (a : ℝ) (h : Fin m → ℝ)
    (x : ℝ) (ha : 0 ≤ a) (hh : ∀ j, h j ≤ 1) (hx : 0 ≤ x) :
    a^(4*m) ≤ ((angularZeroProduct a h).eval x)^2 := by
  have hp := angularZeroProduct_physical_lower a h x ha hh hx
  have hsq : (a^(2*m))^2 ≤ ((angularZeroProduct a h).eval x)^2 :=
    (sq_le_sq₀ (pow_nonneg ha (2*m)) (le_trans (pow_nonneg ha _) hp)).mpr hp
  simpa only [← pow_mul, show 2*m*2 = 4*m by omega] using hsq

theorem angularZeroProduct_normSq_normalized {m : ℕ} (a : ℝ) (h : Fin m → ℝ)
    (z : ℂ) (ha : a ≠ 0) (hz : Complex.normSq z = a^2) :
    Complex.normSq ((angularZeroProduct a h).eval₂ Complex.ofRealHom z) =
      a^(4*m) * ∏ j, (2*|1+z.re/a-h j|)^2 := by
  have heval : (angularZeroProduct a h).eval₂ Complex.ofRealHom z =
      ∏ j, (angularZeroFactor a (h j)).eval₂ Complex.ofRealHom z :=
    map_prod (Polynomial.eval₂RingHom Complex.ofRealHom z) _ _
  rw [heval, map_prod]
  simp_rw [angularZeroFactor_normSq_normalized a _ z ha hz]
  rw [Finset.prod_mul_distrib]
  simp [← pow_mul]

section DegreeSubspace

variable {K : Type*} [Field K]

private theorem mul_mem_degreeLT (p : K[X]) (n : ℕ)
    (q : Polynomial.degreeLT K n) :
    p*q.val ∈ Polynomial.degreeLT K (n+p.natDegree) := by
  apply Polynomial.mem_degreeLT.mpr
  by_cases hp : p=0
  · simp [hp]
  by_cases hq : q.val=0
  · simp [hq]
  apply (Polynomial.natDegree_lt_iff_degree_lt (mul_ne_zero hp hq)).mp
  rw [Polynomial.natDegree_mul hp hq]
  have hqd := (Polynomial.natDegree_lt_iff_degree_lt hq).mpr
    (Polynomial.mem_degreeLT.mp q.property)
  omega

/-- Multiplication by `p`, with the exact source and target degree bounds. -/
def polynomialMultiplyTruncated (p : K[X]) (n : ℕ) :
    Polynomial.degreeLT K n →ₗ[K] Polynomial.degreeLT K (n+p.natDegree) where
  toFun q := ⟨p*q.val, mul_mem_degreeLT p n q⟩
  map_add' := by
    intro q r
    apply Subtype.ext
    simp [mul_add]
  map_smul' := by
    intro c q
    apply Subtype.ext
    simp [mul_smul_comm]

theorem polynomialMultiplyTruncated_injective (p : K[X]) (n : ℕ) (hp : p ≠ 0) :
    Function.Injective (polynomialMultiplyTruncated p n) := by
  intro q r h
  apply Subtype.ext
  exact mul_left_cancel₀ hp (congrArg Subtype.val h)

theorem polynomialMultiplyTruncated_range_finrank (p : K[X]) (n : ℕ) (hp : p ≠ 0) :
    Module.finrank K (LinearMap.range (polynomialMultiplyTruncated p n)) = n := by
  rw [LinearMap.finrank_range_of_inj (polynomialMultiplyTruncated_injective p n hp)]
  have he := (Polynomial.degreeLTEquiv K n).finrank_eq
  simpa using he

/-- Exact codimension of a prescribed polynomial factor. -/
theorem polynomialMultiplyTruncated_codimension (p : K[X]) (n : ℕ) (hp : p ≠ 0) :
    Module.finrank K
      ((Polynomial.degreeLT K (n+p.natDegree)) ⧸
        LinearMap.range (polynomialMultiplyTruncated p n)) = p.natDegree := by
  letI : FiniteDimensional K (Polynomial.degreeLT K (n+p.natDegree)) :=
    FiniteDimensional.of_injective (Polynomial.degreeLTEquiv K (n+p.natDegree)).toLinearMap
      (Polynomial.degreeLTEquiv K (n+p.natDegree)).injective
  have hr := (LinearMap.range (polynomialMultiplyTruncated p n)).finrank_quotient_add_finrank
  rw [polynomialMultiplyTruncated_range_finrank p n hp] at hr
  have he : Module.finrank K (Polynomial.degreeLT K (n+p.natDegree)) = n+p.natDegree := by
    simpa using (Polynomial.degreeLTEquiv K (n+p.natDegree)).finrank_eq
  rw [he] at hr
  omega

end DegreeSubspace

theorem angularZeroProduct_codimension {m : ℕ} (a : ℝ) (h : Fin m → ℝ) (n : ℕ) :
    Module.finrank ℝ
      ((Polynomial.degreeLT ℝ (n+(angularZeroProduct a h).natDegree)) ⧸
        LinearMap.range (polynomialMultiplyTruncated (angularZeroProduct a h) n)) = 2*m := by
  rw [polynomialMultiplyTruncated_codimension _ _ (angularZeroProduct_monic a h).ne_zero]
  exact angularZeroProduct_natDegree a h

end Zeta3.Analysis

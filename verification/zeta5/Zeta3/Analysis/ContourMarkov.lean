import Mathlib.Analysis.SpecialFunctions.Trigonometric.Chebyshev.Extremal
import Mathlib.Analysis.Calculus.Deriv.Polynomial
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Algebra.Polynomial.Degree.SmallDegree
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# A polynomial Markov bound for the contour norm argument

Mathlib proves the Chebyshev extremal derivative inequality at the endpoint
`1`.  Affine changes of variable turn it into the nonsharp, but sufficient,
uniform bound `|p'(x)| ≤ 4 n² M / (b-a)` on any nondegenerate interval on
which `|p| ≤ M`.  The constant is immaterial for the subexponential loss in
the manuscript.  This file proves the finite analytic estimate directly;
it does not assume a polynomial norm-comparison asymptotic.
-/

noncomputable section
open Polynomial Set

namespace Zeta3.Analysis

theorem polynomial_derivative_one_le (p : ℝ[X]) (n : ℕ)
    (hd : p.natDegree ≤ n)
    (hb : ∀ x ∈ Icc (-1 : ℝ) 1, |p.eval x| ≤ 1) :
    |p.derivative.eval 1| ≤ (n : ℝ)^2 := by
  have hu := Polynomial.Chebyshev.eval_iterate_derivative_le_of_forall_abs_le_one
    (P := p) (n := n) (k := 1) (x := 1) (le_refl _)
    (Polynomial.degree_le_of_natDegree_le hd) hb
  have hl := Polynomial.Chebyshev.eval_iterate_derivative_le_of_forall_abs_le_one
    (P := -p) (n := n) (k := 1) (x := 1) (le_refl _)
    (by simpa using Polynomial.degree_le_of_natDegree_le hd)
    (by simpa using hb)
  simp only [Function.iterate_one, Polynomial.Chebyshev.derivative_T_eval_one,
    Int.cast_natCast] at hu hl
  simp only [Polynomial.derivative_neg, Polynomial.eval_neg] at hl
  exact abs_le.mpr ⟨by linarith, hu⟩

theorem polynomial_derivative_one_le_scaled (p : ℝ[X]) (n : ℕ) (M : ℝ)
    (hd : p.natDegree ≤ n) (hM : 0 < M)
    (hb : ∀ x ∈ Icc (-1 : ℝ) 1, |p.eval x| ≤ M) :
    |p.derivative.eval 1| ≤ (n : ℝ)^2*M := by
  let q := C M⁻¹ * p
  have hqd : q.natDegree ≤ n := (Polynomial.natDegree_C_mul_le _ _).trans hd
  have hqb : ∀ x ∈ Icc (-1 : ℝ) 1, |q.eval x| ≤ 1 := by
    intro x hx
    change |(C M⁻¹*p).eval x| ≤ 1
    rw [Polynomial.eval_mul, Polynomial.eval_C, abs_mul, abs_inv, abs_of_pos hM]
    rw [← div_eq_inv_mul]
    exact (div_le_one hM).mpr (hb x hx)
  have h := polynomial_derivative_one_le q n hqd hqb
  change |(C M⁻¹*p).derivative.eval 1| ≤ _ at h
  rw [Polynomial.derivative_C_mul, Polynomial.eval_mul, Polynomial.eval_C,
    abs_mul, abs_inv, abs_of_pos hM, ← div_eq_inv_mul] at h
  exact (div_le_iff₀ hM).mp h

/-- Endpoint derivative bound after an arbitrary affine change of variable. -/
theorem polynomial_affine_endpoint_bound (p : ℝ[X]) (n : ℕ) (M α β : ℝ)
    (hd : p.natDegree ≤ n) (hM : 0 < M)
    (hb : ∀ x ∈ Icc (-1 : ℝ) 1, |p.eval (α*x+β)| ≤ M) :
    |α| * |p.derivative.eval (α+β)| ≤ (n : ℝ)^2*M := by
  let q := p.comp (C α*X+C β)
  have hlin : (C α*X+C β : ℝ[X]).natDegree ≤ 1 := Polynomial.natDegree_linear_le
  have hqd : q.natDegree ≤ n := calc
    _ ≤ p.natDegree * (C α*X+C β : ℝ[X]).natDegree := Polynomial.natDegree_comp_le
    _ ≤ p.natDegree * 1 := Nat.mul_le_mul_left _ hlin
    _ ≤ n := by simpa using hd
  have hqb : ∀ x ∈ Icc (-1 : ℝ) 1, |q.eval x| ≤ M := by
    simpa only [q, Polynomial.eval_comp, Polynomial.eval_add, Polynomial.eval_mul,
      Polynomial.eval_C, Polynomial.eval_X] using hb
  have h := polynomial_derivative_one_le_scaled q n M hqd hM hqb
  simpa [q, Polynomial.derivative_comp, abs_mul] using h

theorem polynomial_derivative_right_endpoint (p : ℝ[X]) (n : ℕ) (M a b : ℝ)
    (hd : p.natDegree ≤ n) (hM : 0 < M) (hab : a < b)
    (hb : ∀ x ∈ Icc a b, |p.eval x| ≤ M) :
    |p.derivative.eval b| ≤ 2*(n : ℝ)^2*M/(b-a) := by
  have hlen : 0 < (b-a)/2 := by linarith
  have hmap (x : ℝ) (hx : x ∈ Icc (-1 : ℝ) 1) :
      (b-a)/2*x+(b+a)/2 ∈ Icc a b := by
    constructor <;> nlinarith [mul_nonneg (sub_nonneg.mpr hab.le) (sub_nonneg.mpr hx.2),
      mul_nonneg (sub_nonneg.mpr hab.le) (by linarith [hx.1] : 0 ≤ x+1)]
  have h := polynomial_affine_endpoint_bound p n M ((b-a)/2) ((b+a)/2) hd hM
    (fun x hx => hb _ (hmap x hx))
  rw [abs_of_pos hlen, show (b-a)/2+(b+a)/2=b by ring] at h
  apply (le_div_iff₀ (sub_pos.mpr hab)).mpr
  nlinarith

theorem polynomial_derivative_left_endpoint (p : ℝ[X]) (n : ℕ) (M a b : ℝ)
    (hd : p.natDegree ≤ n) (hM : 0 < M) (hab : a < b)
    (hb : ∀ x ∈ Icc a b, |p.eval x| ≤ M) :
    |p.derivative.eval a| ≤ 2*(n : ℝ)^2*M/(b-a) := by
  have hlen : (a-b)/2 < 0 := by linarith
  have hmap (x : ℝ) (hx : x ∈ Icc (-1 : ℝ) 1) :
      (a-b)/2*x+(b+a)/2 ∈ Icc a b := by
    constructor <;> nlinarith [mul_nonneg (sub_nonneg.mpr hab.le) (sub_nonneg.mpr hx.2),
      mul_nonneg (sub_nonneg.mpr hab.le) (by linarith [hx.1] : 0 ≤ x+1)]
  have h := polynomial_affine_endpoint_bound p n M ((a-b)/2) ((b+a)/2) hd hM
    (fun x hx => hb _ (hmap x hx))
  rw [abs_of_neg hlen, show (a-b)/2+(b+a)/2=a by ring] at h
  apply (le_div_iff₀ (sub_pos.mpr hab)).mpr
  nlinarith

/-- A uniform Markov bound with constant `4` on an arbitrary interval. -/
theorem polynomial_markov_interval (p : ℝ[X]) (n : ℕ) (M a b : ℝ)
    (hd : p.natDegree ≤ n) (hM : 0 < M) (hab : a < b)
    (hb : ∀ x ∈ Icc a b, |p.eval x| ≤ M)
    (x : ℝ) (hx : x ∈ Icc a b) :
    |p.derivative.eval x| ≤ 4*(n : ℝ)^2*M/(b-a) := by
  have hc : 0 ≤ 2*(n : ℝ)^2*M := by positivity
  by_cases hmid : (a+b)/2 ≤ x
  · have hax : a < x := by linarith
    have h := polynomial_derivative_right_endpoint p n M a x hd hM hax
      (fun y hy => hb y ⟨hy.1, hy.2.trans hx.2⟩)
    apply h.trans
    apply (div_le_div_iff₀ (sub_pos.mpr hax) (sub_pos.mpr hab)).mpr
    nlinarith [mul_nonneg hc (by linarith : 0 ≤ 2*x-a-b)]
  · have hxb : x < b := by linarith
    have h := polynomial_derivative_left_endpoint p n M x b hd hM hxb
      (fun y hy => hb y ⟨hx.1.trans hy.1, hy.2⟩)
    apply h.trans
    apply (div_le_div_iff₀ (sub_pos.mpr hxb) (sub_pos.mpr hab)).mpr
    nlinarith [mul_nonneg hc (by linarith : 0 ≤ a+b-2*x)]

theorem polynomial_markov_lipschitz (p : ℝ[X]) (n : ℕ) (M a b : ℝ)
    (hd : p.natDegree ≤ n) (hM : 0 < M) (hab : a < b)
    (hb : ∀ x ∈ Icc a b, |p.eval x| ≤ M)
    (x y : ℝ) (hx : x ∈ Icc a b) (hy : y ∈ Icc a b) :
    |p.eval y-p.eval x| ≤ (4*(n : ℝ)^2*M/(b-a)) * |y-x| := by
  have h := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
    (f := fun x => p.eval x) (f' := fun x => p.derivative.eval x)
    (fun x _ => (p.hasDerivAt x).hasDerivWithinAt)
    (fun x hx => by simpa only [Real.norm_eq_abs] using
      polynomial_markov_interval p n M a b hd hM hab hb x hx)
    (convex_Icc a b) hx hy
  simpa only [Real.norm_eq_abs] using h

/-- A quantitative neighborhood on which a nonzero value cannot halve.
This is the finite persistence step needed in the weighted L² comparison. -/
theorem polynomial_value_persists (p : ℝ[X]) (n : ℕ) (M a b : ℝ)
    (hd : p.natDegree ≤ n) (hM : 0 < M) (hab : a < b)
    (hb : ∀ x ∈ Icc a b, |p.eval x| ≤ M)
    (x y : ℝ) (hx : x ∈ Icc a b) (hy : y ∈ Icc a b)
    (hnear : (4*(n : ℝ)^2*M/(b-a)) * |y-x| ≤ |p.eval x|/2) :
    |p.eval x|/2 ≤ |p.eval y| := by
  have h := polynomial_markov_lipschitz p n M a b hd hM hab hb x y hx hy
  have ht : |p.eval x| ≤ |p.eval y-p.eval x|+|p.eval y| := by
    have ht := abs_sub_le (p.eval y) (p.eval x) 0
    have ht' := abs_sub_le (p.eval x) (p.eval y) 0
    simpa only [sub_zero, abs_sub_comm] using ht'
  linarith

end Zeta3.Analysis

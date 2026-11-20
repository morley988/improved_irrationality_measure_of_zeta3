import Zeta3.Analysis.ContourMarkov
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

/-!
# A quantitative local weighted L² comparison

The polynomial Markov estimate produces an actual interval of length `ρ/2`
on which the polynomial retains at least half its value at a selected point.
The interval lies at distance at least `ρ/2` from zero.  Consequently a
positive weight that vanishes only as a fixed power at zero still gives an
explicit weighted integral lower bound.

The statements are finite inequalities for genuine polynomial evaluations
and Lebesgue integrals.  They neither assume nor assert a subexponential
norm-comparison rate.
-/

noncomputable section
open Polynomial Set MeasureTheory

namespace Zeta3.Analysis

/-- A short interval inside a nonnegative interval, close to `x`, and
uniformly separated from the origin. -/
theorem exists_nearby_interval_away_from_zero (a b x ρ : ℝ)
    (ha : 0 ≤ a) (hab : a < b) (hx : x ∈ Icc a b)
    (hρ : 0 < ρ) (hlen : 2*ρ ≤ b-a) :
    ∃ l r : ℝ, a ≤ l ∧ l < r ∧ r ≤ b ∧ r-l=ρ/2 ∧ ρ/2 ≤ l ∧
      ∀ y ∈ Icc l r, |y-x| ≤ ρ := by
  by_cases hm : x ≤ (a+b)/2
  · refine ⟨x+ρ/2, x+ρ, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · linarith [hx.1]
    · linarith
    · linarith
    · ring
    · linarith [hx.1]
    · intro y hy
      exact abs_le.mpr ⟨by linarith [hy.1], by linarith [hy.2]⟩
  · refine ⟨x-ρ/2, x, ?_, ?_, hx.2, ?_, ?_, ?_⟩
    · linarith
    · linarith
    · ring
    · linarith
    · intro y hy
      exact abs_le.mpr ⟨by linarith [hy.1], by linarith [hy.2]⟩

/-- An actual interval on which the polynomial's selected value persists. -/
theorem polynomial_persistence_interval (p : ℝ[X]) (n : ℕ) (M a b x ρ : ℝ)
    (hd : p.natDegree ≤ n) (hM : 0 < M) (ha : 0 ≤ a) (hab : a < b)
    (hb : ∀ y ∈ Icc a b, |p.eval y| ≤ M) (hx : x ∈ Icc a b)
    (hρ : 0 < ρ) (hlen : 2*ρ ≤ b-a)
    (hscale : (4*(n : ℝ)^2*M/(b-a))*ρ ≤ |p.eval x|/2) :
    ∃ l r : ℝ, a ≤ l ∧ l < r ∧ r ≤ b ∧ r-l=ρ/2 ∧ ρ/2 ≤ l ∧
      ∀ y ∈ Icc l r, |p.eval x|/2 ≤ |p.eval y| := by
  obtain ⟨l,r,hal,hlr,hrb,hlen',haway,hclose⟩ :=
    exists_nearby_interval_away_from_zero a b x ρ ha hab hx hρ hlen
  refine ⟨l,r,hal,hlr,hrb,hlen',haway,?_⟩
  intro y hy
  apply polynomial_value_persists p n M a b hd hM hab hb x y hx
    ⟨hal.trans hy.1,hy.2.trans hrb⟩
  exact (mul_le_mul_of_nonneg_left (hclose y hy) (by positivity)).trans hscale

/-- The finite weighted L² estimate, allowing the weight to vanish at zero.
Only the portion `y ≥ ρ/2` needs the positive lower bound `c`. -/
theorem polynomial_weighted_integral_lower (p : ℝ[X]) (n : ℕ)
    (M a b x ρ c : ℝ) (w : ℝ → ℝ)
    (hd : p.natDegree ≤ n) (hM : 0 < M) (ha : 0 ≤ a) (hab : a < b)
    (hb : ∀ y ∈ Icc a b, |p.eval y| ≤ M) (hx : x ∈ Icc a b)
    (hρ : 0 < ρ) (hlen : 2*ρ ≤ b-a)
    (hscale : (4*(n : ℝ)^2*M/(b-a))*ρ ≤ |p.eval x|/2)
    (hc : 0 ≤ c) (hw : ∀ y ∈ Icc a b, 0 ≤ w y)
    (hwlower : ∀ y ∈ Icc a b, ρ/2 ≤ y → c ≤ w y)
    (hfi : IntervalIntegrable (fun y => w y*(p.eval y)^2) volume a b) :
    ρ*c*(p.eval x)^2/8 ≤ ∫ y in a..b, w y*(p.eval y)^2 := by
  obtain ⟨l,r,hal,hlr,hrb,hlen',haway,hp⟩ :=
    polynomial_persistence_interval p n M a b x ρ hd hM ha hab hb hx hρ hlen hscale
  have hsub : Icc l r ⊆ Icc a b := Icc_subset_Icc hal hrb
  have hfi' : IntervalIntegrable (fun y => w y*(p.eval y)^2) volume l r :=
    hfi.mono_set (by simpa only [uIcc_of_le hlr.le, uIcc_of_le hab.le] using hsub)
  have hpoint (y : ℝ) (hy : y ∈ Icc l r) :
      c*(|p.eval x|/2)^2 ≤ w y*(p.eval y)^2 := by
    have hs : (|p.eval x|/2)^2 ≤ (p.eval y)^2 := by
      have h := (sq_le_sq₀ (by positivity : 0 ≤ |p.eval x|/2) (abs_nonneg (p.eval y))).mpr
        (hp y hy)
      simpa only [sq_abs] using h
    exact mul_le_mul (hwlower y (hsub hy) (haway.trans hy.1)) hs
      (sq_nonneg _) (hw y (hsub hy))
  have hi := intervalIntegral.integral_mono_on hlr.le intervalIntegrable_const hfi' hpoint
  have hconst : (∫ _ in l..r, c*(|p.eval x|/2)^2) = ρ*c*(p.eval x)^2/8 := by
    rw [intervalIntegral.integral_const, hlen']
    simp only [smul_eq_mul, div_pow, sq_abs]
    ring
  rw [hconst] at hi
  refine hi.trans (intervalIntegral.integral_mono_interval hal hlr.le hrb ?_ hfi)
  filter_upwards [self_mem_ae_restrict measurableSet_Ioc] with y hy
  exact mul_nonneg (hw y ⟨hy.1.le,hy.2⟩) (sq_nonneg _)

/-- A canonical positive persistence radius, valid even for constant polynomials. -/
def polynomialPersistenceRadius (n : ℕ) (M a b Q : ℝ) : ℝ :=
  (b-a)*Q/(8*((n : ℝ)+1)^2*M)

theorem polynomialPersistenceRadius_pos (n : ℕ) (M a b Q : ℝ)
    (hM : 0 < M) (hab : a < b) (hQ : 0 < Q) :
    0 < polynomialPersistenceRadius n M a b Q := by
  unfold polynomialPersistenceRadius
  positivity

theorem polynomialPersistenceRadius_length (n : ℕ) (M a b Q : ℝ)
    (hM : 0 < M) (hab : a < b) (hQ : Q ≤ M) :
    2*polynomialPersistenceRadius n M a b Q ≤ b-a := by
  have hn : (1 : ℝ) ≤ ((n : ℝ)+1)^2 := by
    have hn : (0 : ℝ) ≤ n := by positivity
    nlinarith
  have hden : 0 < 8*((n : ℝ)+1)^2*M := by positivity
  unfold polynomialPersistenceRadius
  rw [← mul_div_assoc]
  apply (div_le_iff₀ hden).mpr
  have h1 := mul_le_mul_of_nonneg_left hQ (sub_pos.mpr hab).le
  have h2 := mul_le_mul_of_nonneg_left hn (by positivity : 0 ≤ (b-a)*M)
  nlinarith

theorem polynomialPersistenceRadius_scale (n : ℕ) (M a b Q : ℝ)
    (hM : 0 < M) (hab : a < b) (hQ : 0 ≤ Q) :
    (4*(n : ℝ)^2*M/(b-a))*polynomialPersistenceRadius n M a b Q ≤ Q/2 := by
  have hn : (n : ℝ)^2 ≤ ((n : ℝ)+1)^2 := by
    have hn : (0 : ℝ) ≤ n := by positivity
    nlinarith
  have hden : 0 < ((n : ℝ)+1)^2 := by positivity
  have heq : (4*(n : ℝ)^2*M/(b-a))*polynomialPersistenceRadius n M a b Q =
      (n : ℝ)^2*Q/(2*((n : ℝ)+1)^2) := by
    unfold polynomialPersistenceRadius
    field_simp [hM.ne', (sub_pos.mpr hab).ne']
    <;> ring
  rw [heq]
  apply (div_le_iff₀ (by positivity : 0 < 2*((n : ℝ)+1)^2)).mpr
  nlinarith [mul_le_mul_of_nonneg_right hn hQ]

end Zeta3.Analysis

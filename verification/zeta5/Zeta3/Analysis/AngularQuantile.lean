import Zeta3.Analysis.AngularPotential
import Zeta3.Analysis.AngularZeros

/-!
# Actual angular zero sets with a uniform finite error

Equal-mass quantiles of the constructed angular measure produce real zeros
in its support.  The finite logarithmic quadrature theorem proves the
uniform exponential envelope, including an explicit polynomial loss.
-/

noncomputable section
namespace Zeta3.Analysis
open Real Set MeasureTheory Polynomial
open scoped BigOperators
variable {n : ℕ}

theorem exists_angular_quantile_zeros (c : ℝ) (K e : Fin n → ℝ)
    (hc : 0 < c) (hK : ∀ j, 0 ≤ K j) (he : ∀ j, 0 < e j)
    {b N : ℝ} (hb : 0 ≤ b) (hN : 1 ≤ N) (m : ℕ) (hm : 0 < m)
    (hmass : angularMass c K e (b ^ 2) = 2 * (m : ℝ) / N) :
    ∃ h : Fin m → ℝ, (∀ j, h j ∈ Icc 0 (b ^ 2)) ∧ ∀ y : ℝ, 0 ≤ y →
      (∏ j, (2 * |y - h j|) ^ 2) ≤
        Real.exp (8 * (angularRadialData c K e hc hK he b hb).smallBallConstant) *
          (1 + b ^ 2) ^ 4 * N ^ 16 *
          Real.exp (N * (angularField c K e y +
            angularProfile c K e hc hK he (2 * (m : ℝ) / N))) := by
  let d := angularRadialData c K e hc hK he b hb
  have hNpos : 0 < N := lt_of_lt_of_le zero_lt_one hN
  have hmass' : d.squaredMeasure.real (Ioc 0 (b ^ 2)) = (m : ℝ) / N := by
    rw [angularRadialData_mass c K e hc hK he b hb, hmass]
    ring
  obtain ⟨a, ha0, ham, hamem, ha, hcells⟩ := Zeta5.Analysis.exists_equalMass_partition
    d.squaredMeasure hNpos (sq_nonneg b) m hm hmass'
  let sample : ℕ → ℝ := fun j => (a j + a (j + 1)) / 2
  have hs (j : ℕ) (hj : j < m) : sample j ∈ Icc (a j) (a (j + 1)) := by
    have h := ha j hj
    dsimp [sample]
    constructor <;> linarith
  refine ⟨fun j => sample j.val, ?_, ?_⟩
  · intro j
    have h := hs j.val j.isLt
    have hlo := hamem j.val j.isLt.le
    have hhi := hamem (j.val + 1) j.isLt
    exact ⟨hlo.1.trans h.1, h.2.trans hhi.2⟩
  · intro y hy
    have hp := Zeta5.Analysis.quantilePolynomial_sq_bound d.squaredMeasure hN
      d.smallBallConstant_nonneg (sq_nonneg b) m a sample ha0 ham
      (fun j hj => (ha j hj).le) hs hcells (fun ρ hρ => d.squaredMeasure_smallBall y hρ)
    have hprod : (∏ j : Fin m, (2 * |y - sample j.val|) ^ 2) =
        (2 : ℝ) ^ (2 * m) * |(Zeta5.Analysis.quantilePolynomial m sample).eval y| ^ 2 := by
      simp_rw [mul_pow]
      rw [Finset.prod_mul_distrib]
      simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin, ← pow_mul]
      rw [Zeta5.Analysis.quantilePolynomial_eval, Finset.abs_prod, ← Finset.prod_pow]
      congr 1
      exact Fin.prod_univ_eq_prod_range (fun j => |y - sample j| ^ 2) m
    have hpotential := angularMeasure_equilibrium_profile c K e hc hK he hb hy
    rw [hmass] at hpotential
    have hscaled := mul_le_mul_of_nonneg_left hpotential hNpos.le
    have hinterval : (∫ w in 0..b ^ 2, Real.log |y - w| ∂d.squaredMeasure) =
        ∫ w, Real.log |y - w| ∂d.squaredMeasure := by
      rw [intervalIntegral.integral_of_le (sq_nonneg b)]
      change (∫ w, Real.log |y - w| ∂d.squaredMeasure.restrict (Ioc 0 (d.radius ^ 2))) = _
      rw [d.squaredMeasure_restrict_Ioc]
    rw [hinterval] at hp
    have hexp : (2 : ℝ) ^ (2 * m) *
        Real.exp (2 * N * (∫ w, Real.log |y - w| ∂d.squaredMeasure)) ≤
        Real.exp (N * (angularField c K e y +
          angularProfile c K e hc hK he (2 * (m : ℝ) / N))) := by
      have htwo : (2 : ℝ) ^ (2 * m) = Real.exp (((2 * m : ℕ) : ℝ) * Real.log 2) := by
        rw [Real.exp_nat_mul, Real.exp_log (by norm_num : (0 : ℝ) < 2)]
      rw [htwo, ← Real.exp_add]
      apply Real.exp_le_exp.2
      have hcancel : N * (2 * (m : ℝ) / N) = 2 * (m : ℝ) := by field_simp
      rw [mul_add, mul_sub] at hscaled
      rw [← mul_assoc N (2 * (m : ℝ) / N) (Real.log 2), hcancel] at hscaled
      push_cast
      linarith
    rw [hprod]
    have hpre : 0 ≤ Real.exp (8 * d.smallBallConstant) * (1 + b ^ 2) ^ 4 * N ^ 16 := by positivity
    calc
      _ ≤ (2 : ℝ) ^ (2 * m) *
          (Real.exp (8 * d.smallBallConstant) * (1 + b ^ 2) ^ 4 * N ^ 16 *
            Real.exp (2 * N * (∫ w, Real.log |y - w| ∂d.squaredMeasure))) :=
        mul_le_mul_of_nonneg_left hp (by positivity)
      _ = (Real.exp (8 * d.smallBallConstant) * (1 + b ^ 2) ^ 4 * N ^ 16) *
          ((2 : ℝ) ^ (2 * m) * Real.exp (2 * N * (∫ w, Real.log |y - w| ∂d.squaredMeasure))) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hexp hpre

def angularQuantileConstant (c : ℝ) (K e : Fin n → ℝ) : ℝ :=
  16 * Real.exp (24 * angularRadialBound c K e)

theorem angularQuantileConstant_pos (c : ℝ) (K e : Fin n → ℝ) :
    0 < angularQuantileConstant c K e := by unfold angularQuantileConstant; positivity

theorem exists_uniform_angular_quantile_zeros (c : ℝ) (K e : Fin n → ℝ)
    (hc : 0 < c) (hK : ∀ j, 0 ≤ K j) (he : ∀ j, 0 < e j)
    {b N : ℝ} (hb : 0 ≤ b) (hb1 : b ≤ 1) (hN : 1 ≤ N) (m : ℕ) (hm : 0 < m)
    (hmass : angularMass c K e (b ^ 2) = 2 * (m : ℝ) / N) :
    ∃ h : Fin m → ℝ, (∀ j, h j ∈ Icc 0 1) ∧ ∀ y : ℝ, 0 ≤ y →
      (∏ j, (2 * |y - h j|) ^ 2) ≤
        angularQuantileConstant c K e * N ^ 16 *
          Real.exp (N * (angularField c K e y +
            angularProfile c K e hc hK he (2 * (m : ℝ) / N))) := by
  obtain ⟨h, hh, hbound⟩ := exists_angular_quantile_zeros c K e hc hK he hb hN m hm hmass
  have hb2 : b ^ 2 ≤ 1 := by nlinarith
  have hC := (angularRadialBound_pos hc hK he).le
  have hsmall : (angularRadialData c K e hc hK he b hb).smallBallConstant ≤
      3 * angularRadialBound c K e := by
    change (2 + b) * (b * angularRadialBound c K e) ≤ 3 * angularRadialBound c K e
    have hbb : (2 + b) * b ≤ 3 := by nlinarith
    nlinarith [mul_le_mul_of_nonneg_right hbb hC]
  have hpow : (1 + b ^ 2) ^ 4 ≤ (16 : ℝ) := by
    have h := pow_le_pow_left₀ (by positivity : (0 : ℝ) ≤ 1 + b ^ 2)
      (by linarith : 1 + b ^ 2 ≤ 2) 4
    norm_num at h
    exact h
  have hpre : Real.exp (8 * (angularRadialData c K e hc hK he b hb).smallBallConstant) *
      (1 + b ^ 2) ^ 4 ≤ angularQuantileConstant c K e := by
    have heq : 8 * (angularRadialData c K e hc hK he b hb).smallBallConstant ≤
        24 * angularRadialBound c K e := by linarith
    have h := mul_le_mul (Real.exp_le_exp.2 heq) hpow (by positivity) (Real.exp_pos _).le
    simpa only [angularQuantileConstant, mul_comm] using h
  refine ⟨h, fun j => ⟨(hh j).1, (hh j).2.trans hb2⟩, ?_⟩
  intro y hy
  apply (hbound y hy).trans
  exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hpre (by positivity))
    (Real.exp_pos _).le

end Zeta3.Analysis

import Zeta3.Analysis.AngularMass
import Mathlib.Analysis.SpecialFunctions.Log.Deriv

/-!
# The finite-charge angular response

This file defines the angular response using the actual inverse mass endpoint,
proves its derivative on positive inputs, and proves that it is decreasing
while the endpoint stays below two.  The certificate uses the stronger cap
below one.  This is the comparison needed for an upper left Riemann sum; it
does not assert the logarithmic-potential interpretation of the response.
-/

namespace Zeta3.Analysis

open scoped BigOperators

noncomputable section

variable {n : ℕ}

def angularPenalty (c : ℝ) (K e : Fin n → ℝ) (B : ℝ) : ℝ :=
  c * B / 2 + ∑ j, 2 * K j * Real.log ((1 + Real.sqrt (1 + B / e j)) / 2)

def angularProfile (c : ℝ) (K e : Fin n → ℝ)
    (hc : 0 < c) (hK : ∀ j, 0 ≤ K j) (he : ∀ j, 0 < e j) (t : ℝ) : ℝ :=
  t * Real.log (angularEndpoint c K e hc hK he t / 2) -
    angularPenalty c K e (angularEndpoint c K e hc hK he t)

/-- The literal finite expression used by the external certificate. -/
theorem angularProfile_formula (c : ℝ) (K e : Fin n → ℝ)
    (hc : 0 < c) (hK : ∀ j, 0 ≤ K j) (he : ∀ j, 0 < e j) (t : ℝ) :
    angularProfile c K e hc hK he t =
      t * Real.log (angularEndpoint c K e hc hK he t / 2) -
      c * angularEndpoint c K e hc hK he t / 2 -
      2 * ∑ j, K j * Real.log
        ((1 + Real.sqrt (1 + angularEndpoint c K e hc hK he t / e j)) / 2) := by
  have hsum : (∑ j, 2 * K j * Real.log
      ((1 + Real.sqrt (1 + angularEndpoint c K e hc hK he t / e j)) / 2)) =
      2 * ∑ j, K j * Real.log
        ((1 + Real.sqrt (1 + angularEndpoint c K e hc hK he t / e j)) / 2) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    ring
  unfold angularProfile angularPenalty
  rw [hsum]
  ring

theorem angular_charge_cancellation {e B : ℝ} (he : 0 < e) (hB : 0 ≤ B) :
    1 - 1 / Real.sqrt (1 + B / e) =
      B / (e * Real.sqrt (1 + B / e) * (1 + Real.sqrt (1 + B / e))) := by
  let s := Real.sqrt (1 + B / e)
  have hs : 0 < s := angular_sqrt_pos he hB
  have hs1 : 0 < 1 + s := by positivity
  have harg : 0 ≤ 1 + B / e := by positivity
  have hsq : e * s ^ 2 - e = B := by
    dsimp [s]
    rw [Real.sq_sqrt harg]
    field_simp
    ring
  have hden : e * s * (1 + s) ≠ 0 := by positivity
  change 1 - 1 / s = B / (e * s * (1 + s))
  calc
    _ = (s - 1) / s := by field_simp
    _ = _ := by
      apply (div_eq_div_iff hs.ne' hden).2
      calc
        (s - 1) * (e * s * (1 + s)) = s * (e * s ^ 2 - e) := by ring
        _ = B * s := by rw [hsq]; ring

theorem angularMass_factorization {c : ℝ} {K e : Fin n → ℝ}
    (he : ∀ j, 0 < e j) {B : ℝ} (hB : 0 ≤ B) :
    angularMass c K e B = B * (c / 2 +
      ∑ j, K j / (e j * Real.sqrt (1 + B / e j) * (1 + Real.sqrt (1 + B / e j)))) := by
  have hsum : (∑ j, K j * (1 - 1 / Real.sqrt (1 + B / e j))) =
      B * ∑ j, K j / (e j * Real.sqrt (1 + B / e j) * (1 + Real.sqrt (1 + B / e j))) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    rw [angular_charge_cancellation (he j) hB]
    ring
  dsimp [angularMass]
  rw [hsum]
  ring

theorem angular_log_charge_hasDerivAt {K e B : ℝ} (he : 0 < e) (hB : 0 ≤ B) :
    HasDerivAt (fun x : ℝ => 2 * K * Real.log ((1 + Real.sqrt (1 + x / e)) / 2))
      (K / (e * Real.sqrt (1 + B / e) * (1 + Real.sqrt (1 + B / e)))) B := by
  have harg : 1 + B / e ≠ 0 := by
    have h := div_nonneg hB he.le
    linarith
  have hs := angular_sqrt_pos he hB
  have hp : 0 < (1 + Real.sqrt (1 + B / e)) / 2 := by positivity
  have ds := (((hasDerivAt_id B).div_const e).const_add 1).sqrt harg
  have d := (((ds.const_add 1).div_const 2).log hp.ne').const_mul (2 * K)
  convert! d using 1
  simp only [id_eq]
  field_simp

theorem angularPenalty_hasDerivAt {c : ℝ} {K e : Fin n → ℝ}
    (he : ∀ j, 0 < e j) {B : ℝ} (hB : 0 < B) :
    HasDerivAt (angularPenalty c K e) (angularMass c K e B / B) B := by
  have ds := HasDerivAt.fun_sum (u := Finset.univ)
    (fun j _ => angular_log_charge_hasDerivAt (K := K j) (he j) hB.le)
  have dl := ((hasDerivAt_id B).const_mul c).div_const 2
  have d := dl.add ds
  convert! d using 1
  rw [angularMass_factorization he hB.le]
  simp [hB.ne', mul_div_cancel_left₀]

theorem angularProfile_hasDerivAt (c : ℝ) (K e : Fin n → ℝ)
    (hc : 0 < c) (hK : ∀ j, 0 ≤ K j) (he : ∀ j, 0 < e j)
    {t : ℝ} (ht : 0 < t) :
    HasDerivAt (angularProfile c K e hc hK he)
      (Real.log (angularEndpoint c K e hc hK he t / 2)) t := by
  have hB := angularEndpoint_pos c K e hc hK he ht
  have hD := angularMassSlope_pos hc hK he hB.le
  have db := angularEndpoint_hasDerivAt c K e hc hK he ht
  have dlog := (db.div_const 2).log (show angularEndpoint c K e hc hK he t / 2 ≠ 0 by positivity)
  have dpen := (angularPenalty_hasDerivAt (c := c) (K := K) he hB).comp t db
  have d := ((hasDerivAt_id t).mul dlog).sub dpen
  convert! d using 1
  rw [angularMass_endpoint c K e hc hK he ht.le]
  simp only [id_eq, one_mul]
  field_simp
  ring

@[simp] theorem angularPenalty_zero (c : ℝ) (K e : Fin n → ℝ) :
    angularPenalty c K e 0 = 0 := by
  simp [angularPenalty]

@[simp] theorem angularProfile_zero (c : ℝ) (K e : Fin n → ℝ)
    (hc : 0 < c) (hK : ∀ j, 0 ≤ K j) (he : ∀ j, 0 < e j) :
    angularProfile c K e hc hK he 0 = 0 := by
  simp [angularProfile]

theorem angularPenalty_nonneg {c : ℝ} {K e : Fin n → ℝ}
    (hc : 0 < c) (hK : ∀ j, 0 ≤ K j) (he : ∀ j, 0 < e j)
    {B : ℝ} (hB : 0 ≤ B) :
    0 ≤ angularPenalty c K e B := by
  have hsum : 0 ≤ ∑ j, 2 * K j * Real.log ((1 + Real.sqrt (1 + B / e j)) / 2) := by
    apply Finset.sum_nonneg
    intro j _
    have hs : 1 ≤ Real.sqrt (1 + B / e j) := by
      apply Real.one_le_sqrt.2
      have h := div_nonneg hB (he j).le
      linarith
    have hlog : 0 ≤ Real.log ((1 + Real.sqrt (1 + B / e j)) / 2) :=
      Real.log_nonneg (by linarith)
    exact mul_nonneg (mul_nonneg (by norm_num) (hK j)) hlog
  dsimp [angularPenalty]
  have hlin : 0 ≤ c * B / 2 := by positivity
  linarith

theorem angularProfile_neg (c : ℝ) (K e : Fin n → ℝ)
    (hc : 0 < c) (hK : ∀ j, 0 ≤ K j) (he : ∀ j, 0 < e j)
    {t : ℝ} (ht : 0 < t) (hcap : angularEndpoint c K e hc hK he t < 2) :
    angularProfile c K e hc hK he t < 0 := by
  have hB := angularEndpoint_pos c K e hc hK he ht
  have hlog : Real.log (angularEndpoint c K e hc hK he t / 2) < 0 :=
    Real.log_neg (by positivity) (by linarith)
  have hfirst := mul_neg_of_pos_of_neg ht hlog
  have hpen := angularPenalty_nonneg hc hK he hB.le
  dsimp [angularProfile]
  linarith

theorem angularProfile_strictAntiOn (c : ℝ) (K e : Fin n → ℝ)
    (hc : 0 < c) (hK : ∀ j, 0 ≤ K j) (he : ∀ j, 0 < e j)
    {cap : ℝ} (hcap0 : 0 < cap) (hcap : angularEndpoint c K e hc hK he cap < 2) :
    StrictAntiOn (angularProfile c K e hc hK he) (Set.Icc 0 cap) := by
  have hbound {t : ℝ} (ht : 0 ≤ t) (htcap : t ≤ cap) :
      angularEndpoint c K e hc hK he t < 2 := by
    exact lt_of_le_of_lt
      ((angularEndpoint_strictMonoOn c K e hc hK he).monotoneOn ht hcap0.le htcap) hcap
  have hpos : StrictAntiOn (angularProfile c K e hc hK he) (Set.Ioc 0 cap) := by
    apply strictAntiOn_of_deriv_neg (convex_Ioc 0 cap)
    · intro t ht
      exact (angularProfile_hasDerivAt c K e hc hK he ht.1).continuousAt.continuousWithinAt
    · intro t ht
      have ht' : t ∈ Set.Ioc 0 cap := interior_subset ht
      rw [(angularProfile_hasDerivAt c K e hc hK he ht'.1).deriv]
      apply Real.log_neg
      · exact div_pos (angularEndpoint_pos c K e hc hK he ht'.1) (by norm_num)
      · have hh := hbound ht'.1.le ht'.2
        linarith
  intro s hs t ht hst
  by_cases hs0 : s = 0
  · subst s
    rw [angularProfile_zero]
    exact angularProfile_neg c K e hc hK he hst (hbound ht.1 ht.2)
  · have hspos : 0 < s := lt_of_le_of_ne hs.1 (Ne.symm hs0)
    exact hpos ⟨hspos, hs.2⟩ ⟨lt_trans hspos hst, ht.2⟩ hst

end

end Zeta3.Analysis

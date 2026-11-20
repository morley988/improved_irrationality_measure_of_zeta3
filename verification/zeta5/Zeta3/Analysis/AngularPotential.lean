import Zeta3.Analysis.AngularEquilibrium
import Zeta3.Analysis.AngularProfile

/-! Identification of the actual angular contact constant with the finite
logarithmic expression used by the Arb replay. -/

noncomputable section
namespace Zeta3.Analysis
open Real Set MeasureTheory
open scoped BigOperators
variable {n : ℕ}

def angularContactAtRadius (c : ℝ) (K e : Fin n → ℝ) (b : ℝ) : ℝ :=
  angularMass c K e (b ^ 2) * Real.log (b ^ 2 / 4) - angularPenalty c K e (b ^ 2)

theorem angularContactAtRadius_zero (c : ℝ) (K e : Fin n → ℝ) :
    angularContactAtRadius c K e 0 = 0 := by
  simp [angularContactAtRadius]

theorem angularContactAtRadius_continuous {c : ℝ} {K e : Fin n → ℝ}
    (he : ∀ j, 0 < e j) : Continuous (angularContactAtRadius c K e) := by
  let H : ℝ → ℝ := fun b => c / 2 + ∑ j,
    K j / (e j * Real.sqrt (1 + b ^ 2 / e j) * (1 + Real.sqrt (1 + b ^ 2 / e j)))
  have hH : Continuous H := by
    apply continuous_const.add
    apply continuous_finsetSum
    intro j _
    apply Continuous.div continuous_const (by fun_prop)
    intro b
    have hs := angular_sqrt_pos (he j) (sq_nonneg b)
    have hj := he j
    positivity
  have hlog : Continuous (fun b : ℝ => (b ^ 2 / 4) * Real.log (b ^ 2 / 4)) :=
    Real.continuous_mul_log.comp ((continuous_id.pow 2).div_const 4)
  have hmasslog : Continuous (fun b => angularMass c K e (b ^ 2) * Real.log (b ^ 2 / 4)) := by
    convert! (hH.const_mul 4).mul hlog using 1
    ext b
    rw [angularMass_factorization he (sq_nonneg b)]
    dsimp [H]
    ring
  have hpen : Continuous (fun b => angularPenalty c K e (b ^ 2)) := by
    unfold angularPenalty
    apply Continuous.add (by fun_prop)
    apply continuous_finsetSum
    intro j _
    apply continuous_const.mul
    apply Continuous.log (by fun_prop)
    intro b
    have hs := angular_sqrt_pos (he j) (sq_nonneg b)
    positivity
  exact hmasslog.sub hpen

theorem angularContactAtRadius_hasDerivAt {c : ℝ} {K e : Fin n → ℝ}
    (he : ∀ j, 0 < e j) {b : ℝ} (hb : 0 < b) :
    HasDerivAt (angularContactAtRadius c K e)
      (4 * (angularRadialWeight c K e b * Real.log (b / 2))) b := by
  have dsq : HasDerivAt (fun x : ℝ => x ^ 2) (2 * b) b := by
    convert! (hasDerivAt_id b).pow 2 using 1 <;> simp
  have dm := (angularMass_hasDerivAt (c := c) (K := K) he (sq_nonneg b)).comp
    (h := fun x : ℝ => x ^ 2) b dsq
  have dl := (dsq.div_const 4).log (by positivity : b ^ 2 / 4 ≠ 0)
  have dp := (angularPenalty_hasDerivAt (c := c) (K := K) he (sq_pos_of_pos hb)).comp
    (h := fun x : ℝ => x ^ 2) b dsq
  convert! (dm.mul dl).sub dp using 1
  have hlog : Real.log (b ^ 2 / 4) = 2 * Real.log (b / 2) := by
    rw [show b ^ 2 / 4 = (b / 2) ^ 2 by ring, Real.log_pow]
    norm_num
  rw [hlog]
  unfold angularRadialWeight
  dsimp only [Function.comp_apply]
  field_simp
  ring

theorem angularBasePotential_eq_contact (c : ℝ) (K e : Fin n → ℝ)
    (hc : 0 < c) (hK : ∀ j, 0 ≤ K j) (he : ∀ j, 0 < e j)
    {b : ℝ} (hb : 0 ≤ b) :
    4 * (angularRadialData c K e hc hK he b hb).basePotential =
      angularContactAtRadius c K e b := by
  let d := angularRadialData c K e hc hK he b hb
  have hi := d.basePotential_intervalIntegrable.const_mul 4
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hb
    (angularContactAtRadius_continuous he).continuousOn
    (fun a ha => angularContactAtRadius_hasDerivAt he ha.1) hi
  rw [intervalIntegral.integral_const_mul, angularContactAtRadius_zero, sub_zero] at h
  exact h

theorem angularContactAtRadius_eq_profile (c : ℝ) (K e : Fin n → ℝ)
    (hc : 0 < c) (hK : ∀ j, 0 ≤ K j) (he : ∀ j, 0 < e j)
    {b : ℝ} (hb : 0 ≤ b) :
    angularContactAtRadius c K e b =
      angularProfile c K e hc hK he (angularMass c K e (b ^ 2)) -
        angularMass c K e (b ^ 2) * Real.log 2 := by
  by_cases hb0 : b = 0
  · simp [hb0, angularContactAtRadius_zero]
  have hbpos : 0 < b := lt_of_le_of_ne hb (Ne.symm hb0)
  unfold angularContactAtRadius angularProfile
  rw [angularEndpoint_mass c K e hc hK he (sq_nonneg b)]
  have hlog : Real.log (b ^ 2 / 4) = Real.log (b ^ 2 / 2) - Real.log 2 := by
    rw [← Real.log_div (by positivity : b ^ 2 / 2 ≠ 0) (by norm_num)]
    congr 1
    ring
  rw [hlog]
  ring

theorem angularMeasure_equilibrium_profile (c : ℝ) (K e : Fin n → ℝ)
    (hc : 0 < c) (hK : ∀ j, 0 ≤ K j) (he : ∀ j, 0 < e j)
    {b y : ℝ} (hb : 0 ≤ b) (hy : 0 ≤ y) :
    2 * (∫ w, Real.log |y - w| ∂(angularRadialData c K e hc hK he b hb).squaredMeasure) -
      angularField c K e y + angularMass c K e (b ^ 2) * Real.log 2 ≤
      angularProfile c K e hc hK he (angularMass c K e (b ^ 2)) := by
  have h := angularMeasure_equilibrium_le c K e hc hK he hb hy
  rw [angularBasePotential_eq_contact c K e hc hK he hb,
    angularContactAtRadius_eq_profile c K e hc hK he hb] at h
  linarith

theorem angularProfile_continuousOn (c : ℝ) (K e : Fin n → ℝ)
    (hc : 0 < c) (hK : ∀ j, 0 ≤ K j) (he : ∀ j, 0 < e j) :
    ContinuousOn (angularProfile c K e hc hK he) (Ici 0) := by
  have hcand : Continuous (fun t =>
      angularContactAtRadius c K e (Real.sqrt (angularEndpoint c K e hc hK he t)) + t * Real.log 2) :=
    ((angularContactAtRadius_continuous he).comp
      (angularEndpoint_continuous c K e hc hK he).sqrt).add (continuous_id.mul continuous_const)
  apply hcand.continuousOn.congr
  intro t ht
  have h := angularContactAtRadius_eq_profile c K e hc hK he
    (Real.sqrt_nonneg (angularEndpoint c K e hc hK he t))
  rw [Real.sq_sqrt (angularEndpoint_nonneg c K e hc hK he t),
    angularMass_endpoint c K e hc hK he ht] at h
  linarith

end Zeta3.Analysis

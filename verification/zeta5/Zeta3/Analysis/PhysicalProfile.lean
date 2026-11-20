import Zeta3.Analysis.PhysicalEquilibrium
import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog

/-!
# The actual two-window saving profile

The definition is the equilibrium constant after factorial normalization.
Its explicit square-root/logarithm formula agrees with the expression used
by the external finite checker. Monotonicity justifies left Riemann sums;
it is a mathematical theorem, not an external numerical assumption.
-/

open Set

namespace Zeta3.Analysis
noncomputable section

def physicalSaving (s₁ s₂ : ℝ) (h₁ : 0 < s₁) (h₂ : 0 < s₂) (v : ℝ) : ℝ :=
  -physicalEquilibrium s₁ s₂ h₁ h₂ v + 2 - 2 * (s₁ + s₂) - 4 * v +
    2 * (s₁ + v) * Real.log (2 * (s₁ + v)) +
    2 * (s₂ + v) * Real.log (2 * (s₂ + v))

def physicalSavingFormula (s₁ s₂ b v : ℝ) : ℝ :=
  2 * (s₁ + v) * Real.log (4 * (s₁ + v)) +
    2 * (s₂ + v) * Real.log (4 * (s₂ + v)) -
    2 * s₁ * Real.log (s₁ + Real.sqrt (s₁ ^ 2 + b ^ 2)) -
    2 * s₂ * Real.log (s₂ + Real.sqrt (s₂ ^ 2 + b ^ 2)) -
    4 * v * Real.log b + 2 * Real.log ((1 + Real.sqrt (1 + b ^ 2)) / 2)

def physicalSavingSlope (s₁ s₂ : ℝ) (h₁ : 0 < s₁) (h₂ : 0 < s₂) (v : ℝ) : ℝ :=
  2 * Real.log (16 * (s₁ + v) * (s₂ + v) / (physicalEndpoint s₁ s₂ h₁ h₂ v) ^ 2)

theorem physicalEquilibriumAtEndpoint_continuousOn (s₁ s₂ : ℝ)
    (h₁ : 0 < s₁) (h₂ : 0 < s₂) :
    ContinuousOn (physicalEquilibriumAtEndpoint s₁ s₂ h₁ h₂) (Ici 0) := by
  have hc₁ := (Zeta5.Analysis.profileEquilibrium_continuousOn s₁ h₁).comp
    (Zeta5.Analysis.profileMass_continuous h₁).continuousOn
    (fun b (hb : b ∈ Ici (0 : ℝ)) => Zeta5.Analysis.profileMass_nonneg h₁ hb)
  have hc₂ := (Zeta5.Analysis.profileEquilibrium_continuousOn s₂ h₂).comp
    (Zeta5.Analysis.profileMass_continuous h₂).continuousOn
    (fun b (hb : b ∈ Ici (0 : ℝ)) => Zeta5.Analysis.profileMass_nonneg h₂ hb)
  exact (hc₁.add hc₂).div_const 2

theorem physicalEquilibrium_continuousOn (s₁ s₂ : ℝ)
    (h₁ : 0 < s₁) (h₂ : 0 < s₂) :
    ContinuousOn (physicalEquilibrium s₁ s₂ h₁ h₂) (Ici 0) := by
  exact (physicalEquilibriumAtEndpoint_continuousOn s₁ s₂ h₁ h₂).comp
    (physicalEndpoint_continuous s₁ s₂ h₁ h₂).continuousOn
    (fun v _ => physicalEndpoint_nonneg s₁ s₂ h₁ h₂ v)

theorem physicalSaving_continuousOn (s₁ s₂ : ℝ) (h₁ : 0 < s₁) (h₂ : 0 < s₂) :
    ContinuousOn (physicalSaving s₁ s₂ h₁ h₂) (Ici 0) := by
  have hc₁ : Continuous (fun v : ℝ => 2 * (s₁ + v) * Real.log (2 * (s₁ + v))) :=
    Real.continuous_mul_log.comp (by fun_prop)
  have hc₂ : Continuous (fun v : ℝ => 2 * (s₂ + v) * Real.log (2 * (s₂ + v))) :=
    Real.continuous_mul_log.comp (by fun_prop)
  exact (((((physicalEquilibrium_continuousOn s₁ s₂ h₁ h₂).neg.add
    continuousOn_const).sub continuousOn_const).sub
    (continuous_id.const_mul 4).continuousOn).add hc₁.continuousOn).add hc₂.continuousOn

theorem physicalSaving_zero (s₁ s₂ : ℝ) (h₁ : 0 < s₁) (h₂ : 0 < s₂) :
    physicalSaving s₁ s₂ h₁ h₂ 0 = 2 * (s₁ + s₂) * Real.log 2 := by
  unfold physicalSaving physicalEquilibrium physicalEquilibriumAtEndpoint
  rw [physicalEndpoint_zero, Zeta5.Analysis.profileMass_zero h₁.le,
    Zeta5.Analysis.profileMass_zero h₂.le,
    Zeta5.Analysis.profileEquilibrium_zero, Zeta5.Analysis.profileEquilibrium_zero]
  simp only [add_zero, mul_zero, sub_zero]
  rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) h₁.ne',
    Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) h₂.ne']
  ring

private theorem profileEquilibrium_at_mass_formula (s : ℝ) (hs : 0 < s)
    {b : ℝ} (hb : 0 ≤ b) :
    Zeta5.Analysis.profileEquilibrium s hs (Zeta5.Analysis.profileMass s b) =
      4 * Zeta5.Analysis.profileMass s b * Real.log b +
        4 * s * Real.log (s + Real.sqrt (s ^ 2 + b ^ 2)) -
        2 * Real.log ((1 + Real.sqrt (1 + b ^ 2)) / 2) + 2 -
        4 * (s + Zeta5.Analysis.profileMass s b) -
        4 * (s + Zeta5.Analysis.profileMass s b) * Real.log 2 := by
  have hz : 0 < s + Zeta5.Analysis.profileMass s b :=
    add_pos_of_pos_of_nonneg hs (Zeta5.Analysis.profileMass_nonneg hs hb)
  unfold Zeta5.Analysis.profileEquilibrium Zeta5.Analysis.analyticProfile
  rw [Zeta5.Analysis.profileEndpoint_mass s hs hb,
    Real.log_mul (by norm_num : (4 : ℝ) ≠ 0) hz.ne',
    Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) hz.ne']
  have h4 : Real.log (4 : ℝ) = 2 * Real.log 2 := by
    rw [show (4 : ℝ) = 2 * 2 by norm_num, Real.log_mul (by norm_num) (by norm_num)]
    ring
  rw [h4]
  ring

/-- The exact formula evaluated in the external certificate is the normalized
equilibrium constant, including at the zero endpoint. -/
theorem physicalSaving_eq_formula (s₁ s₂ : ℝ) (h₁ : 0 < s₁) (h₂ : 0 < s₂)
    {v : ℝ} (hv : 0 ≤ v) :
    physicalSaving s₁ s₂ h₁ h₂ v =
      physicalSavingFormula s₁ s₂ (physicalEndpoint s₁ s₂ h₁ h₂ v) v := by
  let b := physicalEndpoint s₁ s₂ h₁ h₂ v
  have hb : 0 ≤ b := physicalEndpoint_nonneg s₁ s₂ h₁ h₂ v
  have hm : (Zeta5.Analysis.profileMass s₁ b + Zeta5.Analysis.profileMass s₂ b) / 2 = v := by
    rw [← physicalMass_eq_average]
    exact physicalMass_endpoint s₁ s₂ h₁ h₂ hv
  have hz₁ : 0 < s₁ + v := add_pos_of_pos_of_nonneg h₁ hv
  have hz₂ : 0 < s₂ + v := add_pos_of_pos_of_nonneg h₂ hv
  have h4 : Real.log (4 : ℝ) = 2 * Real.log 2 := by
    rw [show (4 : ℝ) = 2 * 2 by norm_num, Real.log_mul (by norm_num) (by norm_num)]
    ring
  change -((Zeta5.Analysis.profileEquilibrium s₁ h₁ (Zeta5.Analysis.profileMass s₁ b) +
      Zeta5.Analysis.profileEquilibrium s₂ h₂ (Zeta5.Analysis.profileMass s₂ b)) / 2) +
    2 - 2 * (s₁ + s₂) - 4 * v + 2 * (s₁ + v) * Real.log (2 * (s₁ + v)) +
    2 * (s₂ + v) * Real.log (2 * (s₂ + v)) = physicalSavingFormula s₁ s₂ b v
  rw [profileEquilibrium_at_mass_formula s₁ h₁ hb,
    profileEquilibrium_at_mass_formula s₂ h₂ hb]
  unfold physicalSavingFormula
  rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) hz₁.ne',
    Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) hz₂.ne',
    Real.log_mul (by norm_num : (4 : ℝ) ≠ 0) hz₁.ne',
    Real.log_mul (by norm_num : (4 : ℝ) ≠ 0) hz₂.ne', h4]
  have hm' : Zeta5.Analysis.profileMass s₂ b = 2 * v - Zeta5.Analysis.profileMass s₁ b := by
    linarith
  rw [hm']
  ring

theorem physicalSaving_hasDerivAt (s₁ s₂ : ℝ) (h₁ : 0 < s₁) (h₂ : 0 < s₂)
    {v : ℝ} (hv : 0 < v) :
    HasDerivAt (physicalSaving s₁ s₂ h₁ h₂) (physicalSavingSlope s₁ s₂ h₁ h₂ v) v := by
  have hz₁ : 0 < s₁ + v := by positivity
  have hz₂ : 0 < s₂ + v := by positivity
  have hb := physicalEndpoint_pos s₁ s₂ h₁ h₂ hv
  have d₁ := (Real.hasDerivAt_mul_log (show 2 * (s₁ + v) ≠ 0 by positivity)).comp v
    (((hasDerivAt_id v).const_add s₁).const_mul 2)
  have d₂ := (Real.hasDerivAt_mul_log (show 2 * (s₂ + v) ≠ 0 by positivity)).comp v
    (((hasDerivAt_id v).const_add s₂).const_mul 2)
  have d := (((((physicalEquilibrium_hasDerivAt s₁ s₂ h₁ h₂ hv).neg.add_const 2).sub_const
    (2 * (s₁ + s₂))).sub ((hasDerivAt_id v).const_mul 4)).add d₁).add d₂
  convert! d using 1
  dsimp only [physicalSavingSlope, id_eq]
  rw [Real.log_div (show 16 * (s₁ + v) * (s₂ + v) ≠ 0 by positivity) (pow_ne_zero 2 hb.ne'),
    Real.log_mul (show 16 * (s₁ + v) ≠ 0 by positivity) hz₂.ne',
    Real.log_mul (by norm_num : (16 : ℝ) ≠ 0) hz₁.ne', Real.log_pow,
    Real.log_div hb.ne' (by norm_num),
    Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) hz₁.ne',
    Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) hz₂.ne']
  have h16 : Real.log (16 : ℝ) = 4 * Real.log 2 := by
    rw [show (16 : ℝ) = 2 ^ 4 by norm_num, Real.log_pow]
    norm_num
  rw [h16]
  ring

theorem physicalSavingSlope_pos (s₁ s₂ : ℝ) (h₁ : 0 < s₁) (h₂ : 0 < s₂)
    (h₁one : s₁ ≤ 1) {v : ℝ} (hv : 0 < v) :
    0 < physicalSavingSlope s₁ s₂ h₁ h₂ v := by
  have hb := physicalEndpoint_pos s₁ s₂ h₁ h₂ hv
  have hbu := physicalEndpoint_le_twice s₁ s₂ h₁ h₂ h₁one hv.le
  have hsq : (physicalEndpoint s₁ s₂ h₁ h₂ v) ^ 2 ≤ 4 * v ^ 2 := by nlinarith
  have hprod : v ^ 2 < (s₁ + v) * (s₂ + v) := by
    nlinarith [mul_pos h₁ h₂, mul_pos h₁ hv, mul_pos h₂ hv]
  unfold physicalSavingSlope
  apply mul_pos (by norm_num)
  apply Real.log_pos
  apply (one_lt_div (sq_pos_of_pos hb)).mpr
  nlinarith [sq_nonneg v]

theorem physicalSaving_strictMonoOn (s₁ s₂ : ℝ) (h₁ : 0 < s₁) (h₂ : 0 < s₂)
    (h₁one : s₁ ≤ 1) : StrictMonoOn (physicalSaving s₁ s₂ h₁ h₂) (Ici 0) := by
  apply strictMonoOn_of_deriv_pos (convex_Ici 0) (physicalSaving_continuousOn s₁ s₂ h₁ h₂)
  intro v hv
  have hv' : 0 < v := by simpa only [interior_Ici, mem_Ioi] using hv
  rw [(physicalSaving_hasDerivAt s₁ s₂ h₁ h₂ hv').deriv]
  exact physicalSavingSlope_pos s₁ s₂ h₁ h₂ h₁one hv'

end
end Zeta3.Analysis

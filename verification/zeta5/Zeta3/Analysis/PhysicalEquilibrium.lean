import Zeta3.Analysis.PhysicalMass
import Zeta5.Analysis.ExternalEquilibrium

/-!
# The positive two-window auxiliary measure and its equilibrium

All objects are actual measures, integrals, and explicit potentials. The
two-window objects are obtained by averaging the existing one-window objects
at the same support endpoint, not at the same mass. The average has the cubic
mass from `PhysicalMass` and supplies genuine quantile trial polynomials.
-/

open MeasureTheory Set
open scoped ENNReal NNReal

namespace Zeta3.Analysis
noncomputable section

def physicalSquaredMeasure (s₁ s₂ : ℝ) (h₁ : 0 < s₁) (h₂ : 0 < s₂)
    (b : ℝ) : Measure ℝ :=
  (1 / 2 : ℝ≥0) • (Zeta5.Analysis.squaredAuxiliaryMeasure s₁ h₁ b +
    Zeta5.Analysis.squaredAuxiliaryMeasure s₂ h₂ b)

instance physicalSquaredMeasure_isFinite (s₁ s₂ : ℝ) (h₁ : 0 < s₁) (h₂ : 0 < s₂)
    (b : ℝ) : IsFiniteMeasure (physicalSquaredMeasure s₁ s₂ h₁ h₂ b) := by
  unfold physicalSquaredMeasure
  infer_instance

def physicalPotential (s₁ s₂ : ℝ) (h₁ : 0 < s₁) (h₂ : 0 < s₂)
    (b y : ℝ) : ℝ :=
  (Zeta5.Analysis.auxiliaryPotential s₁ h₁ b y +
    Zeta5.Analysis.auxiliaryPotential s₂ h₂ b y) / 2

def physicalField (s₁ s₂ y : ℝ) : ℝ :=
  2 * Real.pi * y + Zeta5.Analysis.externalIntegral 1 y -
    Zeta5.Analysis.externalIntegral s₁ y - Zeta5.Analysis.externalIntegral s₂ y

def physicalEquilibriumAtEndpoint (s₁ s₂ : ℝ) (h₁ : 0 < s₁) (h₂ : 0 < s₂)
    (b : ℝ) : ℝ :=
  (Zeta5.Analysis.profileEquilibrium s₁ h₁ (Zeta5.Analysis.profileMass s₁ b) +
    Zeta5.Analysis.profileEquilibrium s₂ h₂ (Zeta5.Analysis.profileMass s₂ b)) / 2

def physicalEquilibrium (s₁ s₂ : ℝ) (h₁ : 0 < s₁) (h₂ : 0 < s₂)
    (v : ℝ) : ℝ :=
  physicalEquilibriumAtEndpoint s₁ s₂ h₁ h₂ (physicalEndpoint s₁ s₂ h₁ h₂ v)

theorem physicalField_eq_average (s₁ s₂ y : ℝ) :
    physicalField s₁ s₂ y =
      (Zeta5.Analysis.externalField s₁ y + Zeta5.Analysis.externalField s₂ y) / 2 := by
  unfold physicalField Zeta5.Analysis.externalField
  ring

theorem physicalSquaredMeasure_real_Ioc (s₁ s₂ : ℝ) (h₁ : 0 < s₁) (h₂ : 0 < s₂)
    {b : ℝ} (hb : 0 ≤ b) :
    (physicalSquaredMeasure s₁ s₂ h₁ h₂ b).real (Ioc 0 (b ^ 2)) =
      physicalMass s₁ s₂ b := by
  rw [physicalSquaredMeasure, measureReal_nnreal_smul_apply, measureReal_add_apply,
    Zeta5.Analysis.squaredAuxiliaryMeasure_real_Ioc s₁ h₁ hb,
    Zeta5.Analysis.squaredAuxiliaryMeasure_real_Ioc s₂ h₂ hb,
    physicalMass_eq_average]
  norm_num
  ring

theorem physicalSquaredMeasure_log_integrable (s₁ s₂ : ℝ)
    (h₁ : 0 < s₁) (h₂ : 0 < s₂) {b : ℝ} (hb : 0 ≤ b) (v : ℝ) :
    Integrable (fun w : ℝ => Real.log |v - w|) (physicalSquaredMeasure s₁ s₂ h₁ h₂ b) := by
  exact ((Zeta5.Analysis.squaredAuxiliaryMeasure_log_integrable s₁ h₁ hb v).add_measure
    (Zeta5.Analysis.squaredAuxiliaryMeasure_log_integrable s₂ h₂ hb v)).smul_measure_nnreal

theorem physicalSquaredMeasure_restrict_Ioc (s₁ s₂ : ℝ)
    (h₁ : 0 < s₁) (h₂ : 0 < s₂) {b : ℝ} (hb : 0 ≤ b) :
    (physicalSquaredMeasure s₁ s₂ h₁ h₂ b).restrict (Ioc 0 (b ^ 2)) =
      physicalSquaredMeasure s₁ s₂ h₁ h₂ b := by
  simp only [physicalSquaredMeasure, Measure.restrict_smul, Measure.restrict_add,
    Zeta5.Analysis.squaredAuxiliaryMeasure_restrict_Ioc s₁ h₁ hb,
    Zeta5.Analysis.squaredAuxiliaryMeasure_restrict_Ioc s₂ h₂ hb]

/-- The mean potential is the genuine logarithmic potential of the positive
averaged measure. Integrability is proved before using additivity. -/
theorem physicalPotential_integral (s₁ s₂ : ℝ)
    (h₁ : 0 < s₁) (h₂ : 0 < s₂) {b : ℝ} (hb : 0 ≤ b) (y : ℝ) :
    physicalPotential s₁ s₂ h₁ h₂ b y =
      (1 / 2 : ℝ) * ∫ w, Real.log |y ^ 2 - w| ∂physicalSquaredMeasure s₁ s₂ h₁ h₂ b := by
  rw [physicalSquaredMeasure, integral_smul_nnreal_measure,
    integral_add_measure
      (Zeta5.Analysis.squaredAuxiliaryMeasure_log_integrable s₁ h₁ hb (y ^ 2))
      (Zeta5.Analysis.squaredAuxiliaryMeasure_log_integrable s₂ h₂ hb (y ^ 2))]
  simp only [NNReal.smul_def, smul_eq_mul]
  norm_num
  unfold physicalPotential Zeta5.Analysis.auxiliaryPotential
  simp only [Real.log_abs]
  ring

theorem physicalPotential_equilibrium_le (s₁ s₂ : ℝ)
    (h₁ : 0 < s₁) (h₂ : 0 < s₂) {b y : ℝ} (hb : 0 ≤ b) (hy : 0 ≤ y) :
    4 * physicalPotential s₁ s₂ h₁ h₂ b y - physicalField s₁ s₂ y ≤
      physicalEquilibriumAtEndpoint s₁ s₂ h₁ h₂ b := by
  have ha := Zeta5.Analysis.auxiliaryPotential_equilibrium_le s₁ h₁ hb hy
  have hb' := Zeta5.Analysis.auxiliaryPotential_equilibrium_le s₂ h₂ hb hy
  rw [physicalField_eq_average]
  unfold physicalPotential physicalEquilibriumAtEndpoint
  linarith

theorem physicalPotential_equilibrium_eq (s₁ s₂ : ℝ)
    (h₁ : 0 < s₁) (h₂ : 0 < s₂) {b y : ℝ} (hy : 0 ≤ y) (hyb : y ≤ b) :
    4 * physicalPotential s₁ s₂ h₁ h₂ b y - physicalField s₁ s₂ y =
      physicalEquilibriumAtEndpoint s₁ s₂ h₁ h₂ b := by
  have ha := Zeta5.Analysis.auxiliaryPotential_equilibrium_eq s₁ h₁ hy hyb
  have hb' := Zeta5.Analysis.auxiliaryPotential_equilibrium_eq s₂ h₂ hy hyb
  rw [physicalField_eq_average]
  unfold physicalPotential physicalEquilibriumAtEndpoint
  linarith

theorem physicalSquaredMeasure_smallBall (s₁ s₂ : ℝ)
    (h₁ : 0 < s₁) (h₂ : 0 < s₂) {b : ℝ} (hb : 0 ≤ b) (v ρ : ℝ) (hρ : 0 < ρ) :
    physicalSquaredMeasure s₁ s₂ h₁ h₂ b {w : ℝ | |v - w| < ρ ^ 4} ≤
      ENNReal.ofReal ((3 + (3 / 2 : ℝ) * b) * ρ) := by
  have hleft := Zeta5.Analysis.squaredAuxiliaryMeasure_smallBall s₁ h₁ hb v hρ
  have hright := Zeta5.Analysis.squaredAuxiliaryMeasure_smallBall s₂ h₂ hb v hρ
  simp only [physicalSquaredMeasure, Measure.smul_apply, Measure.add_apply, smul_eq_mul]
  have hsum := add_le_add hleft hright
  calc
    _ ≤ (1 / 2 : ℝ≥0) • (ENNReal.ofReal ((3 + (3 / 2 : ℝ) * b) * ρ) +
        ENNReal.ofReal ((3 + (3 / 2 : ℝ) * b) * ρ)) :=
      smul_le_smul_left (1 / 2 : ℝ≥0) hsum
    _ = _ := by
      change (((1 / 2 : ℝ≥0) : ℝ≥0∞) * (_ + _)) = _
      rw [← two_mul, ← mul_assoc]
      norm_num
      rw [ENNReal.inv_mul_cancel (by norm_num) (by norm_num), one_mul]

/-- Actual monic trial polynomials for the two-window auxiliary measure. -/
theorem physicalPotential_trial_polynomial (s₁ s₂ : ℝ)
    (h₁ : 0 < s₁) (h₂ : 0 < s₂) {b N : ℝ}
    (hb : 0 ≤ b) (hN : 1 ≤ N) (n : ℕ) (hn : 0 < n)
    (hmass : physicalMass s₁ s₂ b = (n : ℝ) / N) :
    ∃ p : Polynomial ℝ, p.Monic ∧ p.natDegree = n ∧ ∀ y : ℝ,
      |p.eval (N ^ 2 * y ^ 2)| ^ 2 ≤
        Real.exp (8 * (3 + (3 / 2 : ℝ) * b)) * (1 + b ^ 2) ^ 4 * N ^ (4 * n + 16) *
          Real.exp (4 * N * physicalPotential s₁ s₂ h₁ h₂ b y) := by
  obtain ⟨p, hpm, hpd, hp⟩ := Zeta5.Analysis.exists_monic_scaled_trial_polynomial
    (physicalSquaredMeasure s₁ s₂ h₁ h₂ b) hN (by positivity) (sq_nonneg b) n hn
    ((physicalSquaredMeasure_real_Ioc s₁ s₂ h₁ h₂ hb).trans hmass)
    (fun v ρ hρ => physicalSquaredMeasure_smallBall s₁ s₂ h₁ h₂ hb v ρ hρ)
  refine ⟨p, hpm, hpd, ?_⟩
  intro y
  have hpy := hp (y ^ 2)
  rw [intervalIntegral.integral_of_le (sq_nonneg b),
    physicalSquaredMeasure_restrict_Ioc s₁ s₂ h₁ h₂ hb] at hpy
  rw [physicalPotential_integral s₁ s₂ h₁ h₂ hb]
  convert! hpy using 1 <;> ring

theorem physicalEquilibriumAtEndpoint_hasDerivAt (s₁ s₂ : ℝ)
    (h₁ : 0 < s₁) (h₂ : 0 < s₂) {b : ℝ} (hb : 0 < b) :
    HasDerivAt (physicalEquilibriumAtEndpoint s₁ s₂ h₁ h₂)
      (4 * physicalMassSlope s₁ s₂ b * Real.log (b / 2)) b := by
  have h := ((Zeta5.Analysis.profileEquilibrium_at_mass_hasDerivAt s₁ h₁ hb).add
    (Zeta5.Analysis.profileEquilibrium_at_mass_hasDerivAt s₂ h₂ hb)).div_const 2
  convert! h using 1
  rw [physicalMassSlope_eq_average]
  ring

theorem physicalEquilibrium_hasDerivAt (s₁ s₂ : ℝ)
    (h₁ : 0 < s₁) (h₂ : 0 < s₂) {v : ℝ} (hv : 0 < v) :
    HasDerivAt (physicalEquilibrium s₁ s₂ h₁ h₂)
      (4 * Real.log (physicalEndpoint s₁ s₂ h₁ h₂ v / 2)) v := by
  have hb := physicalEndpoint_pos s₁ s₂ h₁ h₂ hv
  have hd := physicalMassSlope_pos h₁ h₂ hb
  have h := (physicalEquilibriumAtEndpoint_hasDerivAt s₁ s₂ h₁ h₂ hb).comp v
    (physicalEndpoint_hasDerivAt s₁ s₂ h₁ h₂ hv)
  convert! h using 1
  field_simp

end
end Zeta3.Analysis

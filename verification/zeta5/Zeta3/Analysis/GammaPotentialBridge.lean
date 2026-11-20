import Zeta3.Analysis.ImaginaryPotential
import Zeta3.Analysis.PhysicalGamma

/-!
# The certified Gamma formula is the actual physical contour maximum

The scalar identity is proved by equality of derivatives and the endpoint
constant, with continuity at zero checked explicitly. This connects the
formula replayed by Arb to the actual logarithmic potential of the measure.
-/

noncomputable section
namespace Zeta3.Analysis
open MeasureTheory Set Filter Real

theorem physicalMassSlope_continuous {s₁ s₂ : ℝ} (h₁ : 0 < s₁) (h₂ : 0 < s₂) :
    Continuous (physicalMassSlope s₁ s₂) := by
  have h := ((Zeta5.Analysis.profileMassSlope_continuous h₁).add
    (Zeta5.Analysis.profileMassSlope_continuous h₂)).div_const 2
  simpa only [Pi.add_apply, ← physicalMassSlope_eq_average] using h

theorem physicalMass_mul_log_continuous {s₁ s₂ : ℝ} (h₁ : 0 < s₁) (h₂ : 0 < s₂) :
    Continuous (fun b => physicalMass s₁ s₂ b * Real.log b) := by
  have h := ((Zeta5.Analysis.profileMass_mul_log_continuous s₁ h₁).add
    (Zeta5.Analysis.profileMass_mul_log_continuous s₂ h₂)).div_const 2
  convert! h using 1
  ext b
  rw [physicalMass_eq_average]
  dsimp only [Pi.add_apply]
  ring

theorem gammaArc_continuous {u : ℝ} (hu : 0 < u) : Continuous (gammaArc u) := by
  unfold gammaArc gammaRadical
  apply Continuous.sub _ continuous_const
  apply Continuous.log (by fun_prop)
  intro b
  have hs := Real.sqrt_nonneg (u ^ 2 + b ^ 2)
  have hsq := Real.sq_sqrt (show 0 ≤ u ^ 2 + b ^ 2 by positivity)
  have hpos : 0 < b + Real.sqrt (u ^ 2 + b ^ 2) := by nlinarith [sq_pos_of_pos hu]
  exact hpos.ne'

theorem gammaAuxJ_continuous {u a : ℝ} (hu : 0 < u) (ha : 0 < a) :
    Continuous (gammaAuxJ u a) :=
  continuous_iff_continuousAt.2 (fun _ => (gammaAuxJ_hasDerivAt hu ha).continuousAt)

theorem gammaAuxJ_zero {u a : ℝ} (hu : 0 < u) (ha : 0 < a) : gammaAuxJ u a 0 = 0 := by
  rw [gammaAuxJ_formula hu ha]
  norm_num only [gammaRadical, zero_pow, add_zero, Real.sqrt_sq hu.le, Real.sqrt_sq ha.le]
  have hsum : u + a ≠ 0 := by positivity
  have hrat : (u * a + a * u) / (a * (u + u)) = 1 := by field_simp <;> ring
  rw [div_self hsum, hrat]
  simp

theorem physicalGammaAtEndpoint_continuous {s₁ s₂ u : ℝ}
    (h₁ : 0 < s₁) (h₂ : 0 < s₂) (hu : 0 < u) :
    Continuous (physicalGammaAtEndpoint s₁ s₂ u) := by
  have hlog : Continuous (fun b => Real.log (u + gammaRadical u b)) := by
    apply Continuous.log (by unfold gammaRadical; fun_prop)
    intro b
    have hs := gammaRadical_pos (b := b) hu
    positivity
  have hm := ((physicalMass_continuous h₁ h₂).mul hlog).sub (physicalMass_mul_log_continuous h₁ h₂)
  have haux := (((gammaArc_continuous hu).sub
    (gammaAuxJ_continuous hu (by norm_num : (0 : ℝ) < 1))).add
    (gammaAuxJ_continuous hu h₁)).add (gammaAuxJ_continuous hu h₂)
  have h := ((hm.const_mul 4).const_add (physicalGammaBase s₁ s₂ u)).add (haux.const_mul (2 * u))
  convert! h using 1
  ext b
  unfold physicalGammaAtEndpoint gammaLog
  dsimp only [Pi.add_apply, Pi.sub_apply, Pi.mul_apply]
  ring

theorem physicalGammaAtEndpoint_zero {s₁ s₂ u : ℝ}
    (h₁ : 0 < s₁) (h₂ : 0 < s₂) (hu : 0 < u) :
    physicalGammaAtEndpoint s₁ s₂ u 0 = physicalGammaBase s₁ s₂ u := by
  have ha : gammaArc u 0 = 0 := by simp [gammaArc, gammaRadical, Real.sqrt_sq hu.le]
  simp [physicalGammaAtEndpoint, physicalMass_zero h₁.le h₂.le, ha,
    gammaAuxJ_zero hu h₁, gammaAuxJ_zero hu h₂, gammaAuxJ_zero hu (by norm_num : (0 : ℝ) < 1)]

theorem physicalEquilibriumAtEndpoint_continuousOn {s₁ s₂ : ℝ}
    (h₁ : 0 < s₁) (h₂ : 0 < s₂) :
    ContinuousOn (physicalEquilibriumAtEndpoint s₁ s₂ h₁ h₂) (Ici 0) := by
  have hleft := (Zeta5.Analysis.profileEquilibrium_continuousOn s₁ h₁).comp
    (Zeta5.Analysis.profileMass_continuous h₁).continuousOn
    (fun b hb => Zeta5.Analysis.profileMass_nonneg h₁ hb)
  have hright := (Zeta5.Analysis.profileEquilibrium_continuousOn s₂ h₂).comp
    (Zeta5.Analysis.profileMass_continuous h₂).continuousOn
    (fun b hb => Zeta5.Analysis.profileMass_nonneg h₂ hb)
  exact (hleft.add hright).div_const 2

theorem physicalEquilibriumAtEndpoint_zero {s₁ s₂ : ℝ}
    (h₁ : 0 < s₁) (h₂ : 0 < s₂) :
    physicalEquilibriumAtEndpoint s₁ s₂ h₁ h₂ 0 =
      2 + 2 * s₁ * Real.log s₁ + 2 * s₂ * Real.log s₂ - 2 * s₁ - 2 * s₂ := by
  unfold physicalEquilibriumAtEndpoint
  rw [Zeta5.Analysis.profileMass_zero h₁.le, Zeta5.Analysis.profileMass_zero h₂.le,
    Zeta5.Analysis.profileEquilibrium_zero s₁ h₁, Zeta5.Analysis.profileEquilibrium_zero s₂ h₂]
  ring

theorem imaginaryArcsineValue_sub_log {u b : ℝ} (hu : 0 < u) (hb : 0 < b) :
    imaginaryArcsineValue u b - Real.log (b / 2) = gammaLog u b := by
  unfold imaginaryArcsineValue gammaLog gammaRadical
  rw [Real.log_div (by positivity : u + Real.sqrt (u ^ 2 + b ^ 2) ≠ 0) (by norm_num),
    Real.log_div hb.ne' (by norm_num)]
  ring

theorem physicalGammaAtEndpoint_eq_potential (s₁ s₂ u : ℝ)
    (h₁ : 0 < s₁) (h₂ : 0 < s₂) (hu : 0 < u) {b : ℝ} (hb : 0 ≤ b) :
    physicalGammaAtEndpoint s₁ s₂ u b =
      gammaNegativeIntegral u s₁ + gammaNegativeIntegral u s₂ - gammaNegativeIntegral u 1 +
        4 * physicalImaginaryPotential s₁ s₂ h₁ h₂ b u -
        physicalEquilibriumAtEndpoint s₁ s₂ h₁ h₂ b := by
  let W : ℝ → ℝ := fun a => physicalMassSlope s₁ s₂ a * imaginaryArcsineValue u a
  let J : ℝ → ℝ := fun b => ∫ a in 0..b, W a
  have hW : Continuous W := (physicalMassSlope_continuous h₁ h₂).mul (imaginaryArcsineValue_continuous hu)
  have dJ (x : ℝ) : HasDerivAt J (W x) x :=
    intervalIntegral.integral_hasDerivAt_right (hW.intervalIntegrable 0 x)
      hW.stronglyMeasurable.stronglyMeasurableAtFilter hW.continuousAt
  have hJ : Continuous J := continuous_iff_continuousAt.2 (fun x => (dJ x).continuousAt)
  let F : ℝ → ℝ := fun x => physicalGammaAtEndpoint s₁ s₂ u x - 4 * J x +
    physicalEquilibriumAtEndpoint s₁ s₂ h₁ h₂ x
  have hF : ContinuousOn F (Icc 0 b) :=
    (((physicalGammaAtEndpoint_continuous h₁ h₂ hu).sub (hJ.const_mul 4)).continuousOn.add
      ((physicalEquilibriumAtEndpoint_continuousOn h₁ h₂).mono (fun _ hx => hx.1)))
  have hdF (x : ℝ) (hx : x ∈ Ioo 0 b) : HasDerivAt F 0 x := by
    have hd := ((physicalGammaAtEndpoint_hasDerivAt h₁ h₂ hu hx.1).sub
      ((dJ x).const_mul 4)).add (physicalEquilibriumAtEndpoint_hasDerivAt s₁ s₂ h₁ h₂ hx.1)
    convert! hd using 1
    dsimp [W]
    rw [← imaginaryArcsineValue_sub_log hu hx.1]
    ring
  have hconst := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hb hF hdF intervalIntegrable_const
  simp only [intervalIntegral.integral_zero] at hconst
  have hJ0 : J 0 = 0 := by simp [J]
  have hJb : J b = physicalImaginaryPotential s₁ s₂ h₁ h₂ b u :=
    (physicalImaginaryPotential_eq_mixture s₁ s₂ h₁ h₂ hb hu).symm
  dsimp [F] at hconst
  rw [physicalGammaAtEndpoint_zero h₁ h₂ hu, physicalEquilibriumAtEndpoint_zero h₁ h₂, hJ0, hJb] at hconst
  unfold physicalGammaBase at hconst
  linarith

end Zeta3.Analysis

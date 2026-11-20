import Zeta3.Analysis.ArcsineLinear
import Zeta3.Analysis.GammaPotentialBridge
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts

/-!
# The actual linear angular deficit equals the certified mass integral

The coefficient is integrated against the genuine squared physical measure.
Its arcsine mixture is evaluated exactly, then the physical mass variable
is substituted using its proved derivative and inverse identity.
-/

noncomputable section
namespace Zeta3.Analysis
open MeasureTheory Set Filter
open scoped NNReal

def physicalLinearMeasureKernel (u w : ℝ) : ℝ := 2*u^2*w/(u^2+w)^2

theorem physicalLinearMeasureKernel_bounds {u w : ℝ} (hu : 0 < u) (hw : 0 ≤ w) :
    0 ≤ physicalLinearMeasureKernel u w ∧ physicalLinearMeasureKernel u w ≤ 1/2 := by
  have hd : 0 < (u^2+w)^2 := by positivity
  constructor
  · unfold physicalLinearMeasureKernel
    positivity
  · unfold physicalLinearMeasureKernel
    apply (div_le_iff₀ hd).2
    nlinarith [sq_nonneg (u^2-w)]

theorem physicalLinearMeasureKernel_integrable (μ : Measure ℝ) [IsFiniteMeasure μ]
    {u : ℝ} (hu : 0 < u) (hn : ∀ᵐ w ∂μ, 0 ≤ w) :
    Integrable (physicalLinearMeasureKernel u) μ := by
  apply (integrable_const (1/2 : ℝ)).mono' (by
    apply Measurable.aestronglyMeasurable
    unfold physicalLinearMeasureKernel
    fun_prop)
  filter_upwards [hn] with w hw
  rw [Real.norm_eq_abs, abs_of_nonneg (physicalLinearMeasureKernel_bounds hu hw).1]
  exact (physicalLinearMeasureKernel_bounds hu hw).2

theorem auxiliary_linear_measure_eq_radial (s : ℝ) (hs : 0 < s)
    {b u : ℝ} (hb : 0 ≤ b) (hu : 0 < u) :
    (∫ w, physicalLinearMeasureKernel u w ∂Zeta5.Analysis.squaredAuxiliaryMeasure s hs b) =
      ∫ a in 0..b, Zeta5.Analysis.profileMassSlope s a*physicalLinearKernel u a := by
  have hm : Measurable (physicalLinearMeasureKernel u) := by unfold physicalLinearMeasureKernel; fun_prop
  have hi := physicalLinearMeasureKernel_integrable (Zeta5.Analysis.squaredAuxiliaryMeasure s hs b) hu
    ((Zeta5.Analysis.squaredAuxiliaryMeasure_ae_mem s hs hb).mono (fun _ hw => hw.1))
  have hmapint : Integrable (fun p : ℝ × ℝ => physicalLinearMeasureKernel u ((p.1*Real.cos p.2)^2))
      ((Zeta5.Analysis.radialMeasure s hs b).prod Zeta5.Analysis.angleMeasure) :=
    (integrable_map_measure hm.aestronglyMeasurable Zeta5.Analysis.squaredAuxiliaryMap_measurable.aemeasurable).mp hi
  calc
    _ = ∫ p : ℝ × ℝ, physicalLinearMeasureKernel u ((p.1*Real.cos p.2)^2)
        ∂(Zeta5.Analysis.radialMeasure s hs b).prod Zeta5.Analysis.angleMeasure := by
      rw [Zeta5.Analysis.squaredAuxiliaryMeasure,
        integral_map Zeta5.Analysis.squaredAuxiliaryMap_measurable.aemeasurable hm.aestronglyMeasurable]
    _ = ∫ a, ∫ θ, physicalLinearMeasureKernel u ((a*Real.cos θ)^2)
        ∂Zeta5.Analysis.angleMeasure ∂Zeta5.Analysis.radialMeasure s hs b := integral_prod _ hmapint
    _ = ∫ a, physicalLinearKernel u a ∂Zeta5.Analysis.radialMeasure s hs b := by
      apply integral_congr_ae
      filter_upwards [Zeta5.Analysis.radialMeasure_ae_mem s hs b] with a ha
      exact integral_angle_linear_kernel hu ha.1.le
    _ = _ := by
      rw [Zeta5.Analysis.integral_radialMeasure, intervalIntegral.integral_of_le hb]
      apply setIntegral_congr_fun measurableSet_Ioc
      intro a _
      ring

theorem physical_linear_measure_eq_radial (s₁ s₂ : ℝ)
    (h₁ : 0 < s₁) (h₂ : 0 < s₂) {b u : ℝ} (hb : 0 ≤ b) (hu : 0 < u) :
    (∫ w, physicalLinearMeasureKernel u w ∂physicalSquaredMeasure s₁ s₂ h₁ h₂ b) =
      ∫ a in 0..b, physicalMassSlope s₁ s₂ a*physicalLinearKernel u a := by
  have hi (s : ℝ) (hs : 0 < s) :=
    physicalLinearMeasureKernel_integrable (Zeta5.Analysis.squaredAuxiliaryMeasure s hs b) hu
      ((Zeta5.Analysis.squaredAuxiliaryMeasure_ae_mem s hs hb).mono (fun _ hw => hw.1))
  rw [physicalSquaredMeasure, integral_smul_nnreal_measure, integral_add_measure (hi s₁ h₁) (hi s₂ h₂),
    auxiliary_linear_measure_eq_radial s₁ h₁ hb hu, auxiliary_linear_measure_eq_radial s₂ h₂ hb hu]
  simp only [NNReal.smul_def, smul_eq_mul]
  norm_num only [NNReal.coe_div, NNReal.coe_one, NNReal.coe_ofNat]
  have hi₁ : IntervalIntegrable (fun a => Zeta5.Analysis.profileMassSlope s₁ a*physicalLinearKernel u a) volume 0 b :=
    ((Zeta5.Analysis.profileMassSlope_continuous h₁).mul
    (physicalLinearKernel_continuous hu)).intervalIntegrable (μ := volume) 0 b
  have hi₂ : IntervalIntegrable (fun a => Zeta5.Analysis.profileMassSlope s₂ a*physicalLinearKernel u a) volume 0 b :=
    ((Zeta5.Analysis.profileMassSlope_continuous h₂).mul
    (physicalLinearKernel_continuous hu)).intervalIntegrable (μ := volume) 0 b
  rw [← intervalIntegral.integral_add hi₁ hi₂, ← intervalIntegral.integral_const_mul]
  apply intervalIntegral.integral_congr
  intro a _
  dsimp only
  rw [physicalMassSlope_eq_average]
  ring

theorem physicalLinearIntegral_eq_radial (s₁ s₂ u : ℝ)
    (h₁ : 0 < s₁) (h₂ : 0 < s₂) (hu : 0 < u) {b : ℝ} (hb : 0 ≤ b) :
    physicalLinearIntegral s₁ s₂ u h₁ h₂ (physicalMass s₁ s₂ b) =
      ∫ a in 0..b, physicalMassSlope s₁ s₂ a*physicalLinearKernel u a := by
  have hsub := intervalIntegral.integral_deriv_smul_comp
    (f := physicalMass s₁ s₂) (f' := physicalMassSlope s₁ s₂)
    (g := physicalLinearIntegrand s₁ s₂ u h₁ h₂) (a := 0) (b := b)
    (fun a _ => physicalMass_hasDerivAt h₁ h₂)
    (physicalMassSlope_continuous h₁ h₂).continuousOn
    (physicalLinearIntegrand_continuous s₁ s₂ u h₁ h₂ hu)
  rw [physicalMass_zero h₁.le h₂.le] at hsub
  unfold physicalLinearIntegral
  rw [← hsub]
  apply intervalIntegral.integral_congr
  intro a ha
  have ha' : 0 ≤ a := (show a ∈ Icc 0 b by simpa only [uIcc_of_le hb] using ha).1
  simp only [Function.comp_apply, smul_eq_mul, physicalLinearIntegrand,
    physicalEndpoint_mass s₁ s₂ h₁ h₂ ha']

theorem physicalLinearIntegral_eq_measure (s₁ s₂ u : ℝ)
    (h₁ : 0 < s₁) (h₂ : 0 < s₂) (hu : 0 < u) {v : ℝ} (hv : 0 ≤ v) :
    physicalLinearIntegral s₁ s₂ u h₁ h₂ v =
      ∫ w, physicalLinearMeasureKernel u w
        ∂physicalSquaredMeasure s₁ s₂ h₁ h₂ (physicalEndpoint s₁ s₂ h₁ h₂ v) := by
  have hb := physicalEndpoint_nonneg s₁ s₂ h₁ h₂ v
  have h := physicalLinearIntegral_eq_radial s₁ s₂ u h₁ h₂ hu hb
  rw [physicalMass_endpoint s₁ s₂ h₁ h₂ hv] at h
  exact h.trans (physical_linear_measure_eq_radial s₁ s₂ h₁ h₂ hb hu).symm

end Zeta3.Analysis

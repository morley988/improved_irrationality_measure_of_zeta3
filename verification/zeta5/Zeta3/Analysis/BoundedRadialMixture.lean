import Zeta5.Analysis.AuxiliarySmallBall
import Zeta5.Analysis.AuxiliaryPotential

/-!
# A bounded positive radial mixture of squared arcsine measures

This generalizes the measure-theoretic construction in
`Zeta5.Analysis.AuxiliaryMeasure` and `AuxiliarySmallBall`.  In particular the
angular equilibrium below uses a different radial density, with its actual
mass and logarithmic integrability proved rather than postulated.
-/

open MeasureTheory Set Filter
open scoped ENNReal

namespace Zeta3.Analysis
noncomputable section

structure RadialMixtureData where
  radius : ℝ
  radius_nonneg : 0 ≤ radius
  weight : ℝ → ℝ
  weight_continuous : Continuous weight
  bound : ℝ
  bound_nonneg : 0 ≤ bound
  weight_nonneg : ∀ a ∈ Ioc 0 radius, 0 ≤ weight a
  weight_le_bound : ∀ a ∈ Ioc 0 radius, weight a ≤ bound

namespace RadialMixtureData
variable (d : RadialMixtureData)

def radialMeasure : Measure ℝ :=
  (volume.restrict (Ioc 0 d.radius)).withDensity (fun a => ENNReal.ofReal (d.weight a))

theorem radialMeasure_le :
    d.radialMeasure ≤ ENNReal.ofReal d.bound • volume.restrict (Ioc 0 d.radius) := by
  rw [← withDensity_const]
  apply withDensity_mono
  filter_upwards [self_mem_ae_restrict measurableSet_Ioc] with a ha
  exact ENNReal.ofReal_le_ofReal (d.weight_le_bound a ha)

instance radialMeasure_isFinite : IsFiniteMeasure d.radialMeasure where
  measure_univ_lt_top := by
    apply lt_of_le_of_lt (d.radialMeasure_le univ)
    simp only [Measure.smul_apply, Measure.restrict_apply_univ, Real.volume_Ioc,
      sub_zero, smul_eq_mul]
    exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top ENNReal.ofReal_lt_top

theorem radialMeasure_ae_mem : ∀ᵐ a ∂d.radialMeasure, a ∈ Ioc 0 d.radius :=
  (withDensity_absolutelyContinuous (volume.restrict (Ioc (0 : ℝ) d.radius)) _).ae_le
    (self_mem_ae_restrict measurableSet_Ioc)

theorem integral_radialMeasure (f : ℝ → ℝ) :
    (∫ a, f a ∂d.radialMeasure) = ∫ a in Ioc 0 d.radius, f a * d.weight a := by
  rw [radialMeasure, integral_withDensity_eq_integral_toReal_smul
    d.weight_continuous.measurable.ennreal_ofReal
    (Eventually.of_forall (fun _ => ENNReal.ofReal_lt_top))]
  apply setIntegral_congr_fun measurableSet_Ioc
  intro a ha
  dsimp only
  rw [ENNReal.toReal_ofReal (d.weight_nonneg a ha), smul_eq_mul, mul_comm]

theorem radialMeasure_mass :
    d.radialMeasure univ = ENNReal.ofReal (∫ a in 0..d.radius, d.weight a) := by
  rw [radialMeasure, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
    ← ofReal_integral_eq_lintegral_ofReal (d.weight_continuous.intervalIntegrable 0 d.radius).1]
  · rw [intervalIntegral.integral_of_le d.radius_nonneg]
  · filter_upwards [self_mem_ae_restrict measurableSet_Ioc] with a ha
    exact d.weight_nonneg a ha

theorem radialMeasure_mass_le :
    d.radialMeasure univ ≤ ENNReal.ofReal (d.bound * d.radius) := by
  calc
    _ ≤ (ENNReal.ofReal d.bound • volume.restrict (Ioc 0 d.radius)) univ :=
      d.radialMeasure_le univ
    _ = ENNReal.ofReal (d.bound * d.radius) := by
      simp only [Measure.smul_apply, Measure.restrict_apply_univ, Real.volume_Ioc,
        sub_zero, smul_eq_mul]
      rw [ENNReal.ofReal_mul d.bound_nonneg]

def squaredMeasure : Measure ℝ :=
  Measure.map (fun p : ℝ × ℝ => (p.1 * Real.cos p.2) ^ 2)
    (d.radialMeasure.prod Zeta5.Analysis.angleMeasure)

instance squaredMeasure_isFinite : IsFiniteMeasure d.squaredMeasure := by
  unfold squaredMeasure
  infer_instance

theorem squaredMeasure_mass :
    d.squaredMeasure univ = ENNReal.ofReal (∫ a in 0..d.radius, d.weight a) := by
  rw [squaredMeasure, Measure.map_apply Zeta5.Analysis.squaredAuxiliaryMap_measurable MeasurableSet.univ]
  rw [preimage_univ, ← univ_prod_univ, Measure.prod_prod, Zeta5.Analysis.angleMeasure_mass, mul_one,
    d.radialMeasure_mass]

theorem squaredMeasure_ae_mem : ∀ᵐ v ∂d.squaredMeasure, v ∈ Icc 0 (d.radius ^ 2) := by
  change ∀ᵐ v ∂d.squaredMeasure, 0 ≤ v ∧ v ≤ d.radius ^ 2
  rw [squaredMeasure,
    ae_map_iff Zeta5.Analysis.squaredAuxiliaryMap_measurable.aemeasurable measurableSet_Icc]
  apply (Measure.ae_prod_iff_ae_ae
    (Zeta5.Analysis.squaredAuxiliaryMap_measurable measurableSet_Icc)).mpr
  filter_upwards [d.radialMeasure_ae_mem] with a ha
  apply Eventually.of_forall
  intro θ
  constructor
  · exact sq_nonneg _
  · have hc := Real.abs_cos_le_one θ
    have hab : |a * Real.cos θ| ≤ d.radius := by
      rw [abs_mul, abs_of_pos ha.1]
      exact (mul_le_of_le_one_right ha.1.le hc).trans ha.2
    simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg _) d.radius_nonneg).mpr hab

theorem radialMeasure_square_window_le {c v ρ : ℝ} (hρ : 0 < ρ) (hc : ρ ≤ |c|) :
    d.radialMeasure {a : ℝ | |v - (a * c) ^ 2| < ρ ^ 4} ≤ ENNReal.ofReal (2 * d.bound * ρ) := by
  have hmeas : MeasurableSet {a : ℝ | |v - (a * c) ^ 2| < ρ ^ 4} :=
    measurableSet_lt (by fun_prop) measurable_const
  calc
    _ ≤ (ENNReal.ofReal d.bound • volume.restrict (Ioc 0 d.radius))
        {a : ℝ | |v - (a * c) ^ 2| < ρ ^ 4} := d.radialMeasure_le _
    _ = ENNReal.ofReal d.bound *
        volume ({a : ℝ | |v - (a * c) ^ 2| < ρ ^ 4} ∩ Ioc 0 d.radius) := by
      rw [Measure.smul_apply, Measure.restrict_apply hmeas]
      rfl
    _ ≤ ENNReal.ofReal d.bound * ENNReal.ofReal (2 * ρ) :=
      mul_le_mul_right (Zeta5.Analysis.volume_square_window_le hρ hc) _
    _ = _ := by rw [← ENNReal.ofReal_mul d.bound_nonneg]; congr 1; ring

def smallBallConstant : ℝ := (2 + d.radius) * d.bound

theorem smallBallConstant_nonneg : 0 ≤ d.smallBallConstant := by
  exact mul_nonneg (by linarith [d.radius_nonneg]) d.bound_nonneg

theorem squaredMeasure_smallBall (v : ℝ) {ρ : ℝ} (hρ : 0 < ρ) :
    d.squaredMeasure {w : ℝ | |v - w| < ρ ^ 4} ≤ ENNReal.ofReal (d.smallBallConstant * ρ) := by
  let A : Set ℝ := {θ : ℝ | |Real.cos θ| < ρ}
  let f : ℝ → ℝ≥0∞ := fun θ =>
    d.radialMeasure {a : ℝ | |v - (a * Real.cos θ) ^ 2| < ρ ^ 4}
  have hA : MeasurableSet A := measurableSet_lt (by fun_prop) measurable_const
  have hE : MeasurableSet {w : ℝ | |v - w| < ρ ^ 4} :=
    measurableSet_lt (by fun_prop) measurable_const
  have hlow : (∫⁻ θ in A, f θ ∂Zeta5.Analysis.angleMeasure) ≤
      ENNReal.ofReal (d.bound * d.radius) * ENNReal.ofReal ρ := by
    calc
      _ ≤ ∫⁻ _θ in A, ENNReal.ofReal (d.bound * d.radius) ∂Zeta5.Analysis.angleMeasure := by
        apply lintegral_mono
        intro θ
        exact (measure_mono (subset_univ _)).trans d.radialMeasure_mass_le
      _ = ENNReal.ofReal (d.bound * d.radius) * Zeta5.Analysis.angleMeasure A := by simp
      _ ≤ _ := mul_le_mul_right (Zeta5.Analysis.angleMeasure_abs_cos_lt_le hρ) _
  have hhigh : (∫⁻ θ in Aᶜ, f θ ∂Zeta5.Analysis.angleMeasure) ≤
      ENNReal.ofReal (2 * d.bound * ρ) := by
    calc
      _ ≤ ∫⁻ _θ in Aᶜ, ENNReal.ofReal (2 * d.bound * ρ) ∂Zeta5.Analysis.angleMeasure := by
        apply lintegral_mono_ae
        filter_upwards [self_mem_ae_restrict hA.compl] with θ hθ
        exact d.radialMeasure_square_window_le hρ (le_of_not_gt hθ)
      _ = ENNReal.ofReal (2 * d.bound * ρ) * Zeta5.Analysis.angleMeasure Aᶜ := by simp
      _ ≤ ENNReal.ofReal (2 * d.bound * ρ) * 1 :=
        mul_le_mul_right ((measure_mono (subset_univ _)).trans_eq Zeta5.Analysis.angleMeasure_mass) _
      _ = _ := mul_one _
  rw [squaredMeasure, Measure.map_apply Zeta5.Analysis.squaredAuxiliaryMap_measurable hE,
    Measure.prod_apply_symm (Zeta5.Analysis.squaredAuxiliaryMap_measurable hE)]
  change (∫⁻ θ, f θ ∂Zeta5.Analysis.angleMeasure) ≤ _
  rw [← lintegral_add_compl f hA]
  calc
    _ ≤ ENNReal.ofReal (d.bound * d.radius) * ENNReal.ofReal ρ +
        ENNReal.ofReal (2 * d.bound * ρ) := add_le_add hlow hhigh
    _ = _ := by
      rw [← ENNReal.ofReal_mul (mul_nonneg d.bound_nonneg d.radius_nonneg),
        ← ENNReal.ofReal_add (mul_nonneg (mul_nonneg d.bound_nonneg d.radius_nonneg) hρ.le)
          (mul_nonneg (mul_nonneg (by norm_num) d.bound_nonneg) hρ.le)]
      congr 1
      unfold smallBallConstant
      ring

instance squaredMeasure_nullSingleton : NullSingletonClass d.squaredMeasure :=
  Zeta5.Analysis.nullSingletonClass_of_fourth_power_smallBall _ d.smallBallConstant_nonneg
    (fun v ρ hρ => d.squaredMeasure_smallBall v hρ)

theorem squaredMeasure_ae_mem_Ioc : ∀ᵐ v ∂d.squaredMeasure, v ∈ Ioc 0 (d.radius ^ 2) := by
  filter_upwards [d.squaredMeasure_ae_mem, d.squaredMeasure.ae_ne 0] with v hv hne
  exact ⟨lt_of_le_of_ne hv.1 (Ne.symm hne), hv.2⟩

theorem squaredMeasure_restrict_Ioc :
    d.squaredMeasure.restrict (Ioc 0 (d.radius ^ 2)) = d.squaredMeasure :=
  Measure.restrict_eq_self_of_ae_mem d.squaredMeasure_ae_mem_Ioc

theorem squaredMeasure_real_Ioc :
    d.squaredMeasure.real (Ioc 0 (d.radius ^ 2)) = ∫ a in 0..d.radius, d.weight a := by
  have he : d.squaredMeasure (Ioc 0 (d.radius ^ 2)) = d.squaredMeasure univ := by
    apply measure_congr
    filter_upwards [d.squaredMeasure_ae_mem_Ioc] with v hv
    exact propext (iff_of_true hv (mem_univ v))
  rw [measureReal_def, he, d.squaredMeasure_mass, ENNReal.toReal_ofReal]
  rw [intervalIntegral.integral_of_le d.radius_nonneg]
  apply integral_nonneg_of_ae
  filter_upwards [self_mem_ae_restrict measurableSet_Ioc] with a ha
  exact d.weight_nonneg a ha

theorem squaredMeasure_log_integrable (v : ℝ) :
    Integrable (fun w : ℝ => Real.log |v - w|) d.squaredMeasure := by
  have h := (Zeta5.Analysis.log_integrableOn_and_truncated_integral_le
    d.squaredMeasure (C := d.smallBallConstant) (ε := 1) d.smallBallConstant_nonneg
    (by norm_num) (sq_nonneg d.radius) (fun ρ hρ => d.squaredMeasure_smallBall v hρ)).1
  simpa only [IntegrableOn, d.squaredMeasure_restrict_Ioc] using h

def mixturePotential (y : ℝ) : ℝ :=
  ∫ a in 0..d.radius, d.weight a * Zeta5.Analysis.arcsinePotential a y

theorem squaredMeasure_log_integral {y : ℝ} (hy : 0 ≤ y) :
    (∫ w, Real.log |y ^ 2 - w| ∂d.squaredMeasure) = 2 * d.mixturePotential y := by
  have hm : Measurable (fun w : ℝ => Real.log |y ^ 2 - w|) := by fun_prop
  have hmapint : Integrable (fun p : ℝ × ℝ => Real.log |y ^ 2 - (p.1 * Real.cos p.2) ^ 2|)
      (d.radialMeasure.prod Zeta5.Analysis.angleMeasure) := by
    exact (integrable_map_measure hm.aestronglyMeasurable
      Zeta5.Analysis.squaredAuxiliaryMap_measurable.aemeasurable).mp
        (d.squaredMeasure_log_integrable (y ^ 2))
  calc
    _ = ∫ p : ℝ × ℝ, Real.log |y ^ 2 - (p.1 * Real.cos p.2) ^ 2|
        ∂d.radialMeasure.prod Zeta5.Analysis.angleMeasure := by
      rw [squaredMeasure, integral_map Zeta5.Analysis.squaredAuxiliaryMap_measurable.aemeasurable
        hm.aestronglyMeasurable]
    _ = ∫ a, ∫ θ, Real.log |y ^ 2 - (a * Real.cos θ) ^ 2|
        ∂Zeta5.Analysis.angleMeasure ∂d.radialMeasure := integral_prod _ hmapint
    _ = ∫ a, 2 * Zeta5.Analysis.arcsinePotential a y ∂d.radialMeasure := by
      apply integral_congr_ae
      filter_upwards [d.radialMeasure_ae_mem] with a ha
      rw [Zeta5.Analysis.integral_angleMeasure]
      exact (Zeta5.Analysis.arcsineSquared_halfAngle ha.1 hy).2
    _ = _ := by
      rw [d.integral_radialMeasure]
      unfold mixturePotential
      rw [intervalIntegral.integral_of_le d.radius_nonneg, ← integral_const_mul]
      apply setIntegral_congr_fun measurableSet_Ioc
      intro a _
      ring

end RadialMixtureData
end
end Zeta3.Analysis

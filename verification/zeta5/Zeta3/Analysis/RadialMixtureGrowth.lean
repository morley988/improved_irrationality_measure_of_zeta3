import Zeta3.Analysis.BoundedRadialMixture
import Zeta5.Analysis.MixtureEquilibrium

/-! Positive-kernel growth for an arbitrary bounded radial mixture. -/

open MeasureTheory Set Filter
namespace Zeta3.Analysis.RadialMixtureData
noncomputable section
variable (d : Zeta3.Analysis.RadialMixtureData)

def basePotential : ℝ := ∫ a in 0..d.radius, d.weight a * Real.log (a / 2)

def truncatedAbel (t : ℝ) : ℝ :=
  ∫ a in 0..d.radius, d.weight a * Zeta5.Analysis.abelKernel t a

theorem basePotential_intervalIntegrable :
    IntervalIntegrable (fun a => d.weight a * Real.log (a / 2)) volume 0 d.radius := by
  have hlog : IntervalIntegrable (fun a : ℝ => Real.log a - Real.log 2) volume 0 d.radius :=
    intervalIntegral.intervalIntegrable_log'.sub intervalIntegrable_const
  have hlogdiv : IntervalIntegrable (fun a : ℝ => Real.log (a / 2)) volume 0 d.radius := by
    apply hlog.congr_uIoo
    rw [uIoo_of_le d.radius_nonneg]
    intro a ha
    exact (Real.log_div ha.1.ne' (by norm_num)).symm
  exact hlogdiv.continuousOn_mul d.weight_continuous.continuousOn

theorem abelProduct_integrable (y : ℝ) :
    Integrable (fun p : ℝ × ℝ => d.weight p.1 * Zeta5.Analysis.abelKernel p.2 p.1)
      ((volume.restrict (Ioc 0 d.radius)).prod (volume.restrict (Ioc 0 y))) := by
  have hknown := Zeta5.Analysis.profileMassSlope_abel_prod_integrable (1 : ℝ)
    (by norm_num) (y := y) d.radius_nonneg
  have hm : Measurable (fun p : ℝ × ℝ => d.weight p.1 * Zeta5.Analysis.abelKernel p.2 p.1) := by
    unfold Zeta5.Analysis.abelKernel
    exact (d.weight_continuous.measurable.comp measurable_fst).mul (by fun_prop)
  apply (hknown.const_mul (2 * d.bound)).mono' hm.aestronglyMeasurable
  have hae : ∀ᵐ p : ℝ × ℝ ∂(volume.restrict (Ioc 0 d.radius)).prod (volume.restrict (Ioc 0 y)),
      p.1 ∈ Ioc (0 : ℝ) d.radius := by
    apply (Measure.ae_prod_iff_ae_ae (measurable_fst measurableSet_Ioc)).mpr
    filter_upwards [self_mem_ae_restrict measurableSet_Ioc] with a ha
    exact Eventually.of_forall (fun _ => ha)
  filter_upwards [hae] with p hp
  have hker := Zeta5.Analysis.abelKernel_nonneg p.2 p.1
  have hden : 0 < Real.sqrt (1 + p.1 ^ 2) := by positivity
  have hrat : 0 ≤ p.1 / Real.sqrt (1 + p.1 ^ 2) := div_nonneg hp.1.le hden.le
  have hlo : 1 / 2 ≤ Zeta5.Analysis.profileMassSlope 1 p.1 := by
    unfold Zeta5.Analysis.profileMassSlope
    norm_num only [one_pow]
    rw [mul_div_assoc]
    linarith
  have hw : d.weight p.1 ≤ 2 * d.bound * Zeta5.Analysis.profileMassSlope 1 p.1 := by
    have h := mul_le_mul_of_nonneg_left hlo d.bound_nonneg
    linarith [d.weight_le_bound p.1 hp]
  rw [Real.norm_of_nonneg (mul_nonneg (d.weight_nonneg p.1 hp) hker)]
  nlinarith [mul_le_mul_of_nonneg_right hw hker]

theorem truncatedAbel_intervalIntegrable {y : ℝ} (hy : 0 ≤ y) :
    IntervalIntegrable d.truncatedAbel volume 0 y := by
  have houter := (d.abelProduct_integrable y).integral_prod_right
  apply (intervalIntegrable_iff_integrableOn_Ioc_of_le hy).mpr
  change Integrable (fun t => ∫ a in 0..d.radius, d.weight a * Zeta5.Analysis.abelKernel t a)
    (volume.restrict (Ioc 0 y))
  simpa only [intervalIntegral.integral_of_le d.radius_nonneg] using houter

theorem mixturePotential_growth {y : ℝ} (hy : 0 ≤ y) :
    d.mixturePotential y = d.basePotential + ∫ t in 0..y, d.truncatedAbel t := by
  have hprod := d.abelProduct_integrable y
  have hbase := d.basePotential_intervalIntegrable.1
  have hleft := hprod.integral_prod_left
  have heq : (fun a => d.weight a * Zeta5.Analysis.arcsinePotential a y) =ᵐ[
      volume.restrict (Ioc 0 d.radius)]
      (fun a => d.weight a * Real.log (a / 2) +
        ∫ t in Ioc 0 y, d.weight a * Zeta5.Analysis.abelKernel t a) := by
    filter_upwards [self_mem_ae_restrict measurableSet_Ioc] with a ha
    rw [(Zeta5.Analysis.arcsinePotential_eq_log_add_abel ha.1 hy).2, mul_add,
      intervalIntegral.integral_of_le hy, integral_const_mul]
  unfold mixturePotential basePotential
  rw [intervalIntegral.integral_of_le d.radius_nonneg, intervalIntegral.integral_of_le d.radius_nonneg,
    integral_congr_ae heq, integral_add hbase hleft]
  congr 1
  rw [integral_integral_swap hprod]
  simp only [truncatedAbel, intervalIntegral.integral_of_le hy,
    intervalIntegral.integral_of_le d.radius_nonneg]

end
end Zeta3.Analysis.RadialMixtureData

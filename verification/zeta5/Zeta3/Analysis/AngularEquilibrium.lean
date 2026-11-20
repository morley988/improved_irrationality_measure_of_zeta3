import Zeta3.Analysis.AngularAbel
import Zeta3.Analysis.RadialMixtureGrowth

/-!
# The actual finite-charge angular equilibrium measure

The positive squared-arcsine mixture has exactly half the prescribed angular
mass.  Its logarithmic potential satisfies the global equilibrium inequality
and the contact equality throughout its support.  These are theorems about
the actual measure, not additional premises of the numerical certificate.
-/

noncomputable section
namespace Zeta3.Analysis
open MeasureTheory Set Filter
open scoped BigOperators
variable {n : ℕ}

def angularRadialData (c : ℝ) (K e : Fin n → ℝ)
    (hc : 0 < c) (hK : ∀ j, 0 ≤ K j) (he : ∀ j, 0 < e j)
    (b : ℝ) (hb : 0 ≤ b) : RadialMixtureData where
  radius := b
  radius_nonneg := hb
  weight := angularRadialWeight c K e
  weight_continuous := angularRadialWeight_continuous he
  bound := b * angularRadialBound c K e
  bound_nonneg := mul_nonneg hb (angularRadialBound_pos hc hK he).le
  weight_nonneg := fun _ ha => angularRadialWeight_nonneg hc hK he ha.1.le
  weight_le_bound := fun _ ha => angularRadialWeight_le hc hK he ha.1.le ha.2

theorem angularRadialData_mass (c : ℝ) (K e : Fin n → ℝ)
    (hc : 0 < c) (hK : ∀ j, 0 ≤ K j) (he : ∀ j, 0 < e j)
    (b : ℝ) (hb : 0 ≤ b) :
    (angularRadialData c K e hc hK he b hb).squaredMeasure.real (Ioc 0 (b ^ 2)) =
      angularMass c K e (b ^ 2) / 2 := by
  exact (angularRadialData c K e hc hK he b hb).squaredMeasure_real_Ioc.trans
    (integral_angularRadialWeight he b)

theorem angularRadialWeight_abel_above (c : ℝ) (K e : Fin n → ℝ)
    {b t : ℝ} (ht : 0 ≤ t) (htb : t ≤ b) :
    IntervalIntegrable (fun a => angularRadialWeight c K e a * Zeta5.Analysis.abelKernel t a)
      volume t b ∧
      (∫ a in t..b, angularRadialWeight c K e a * Zeta5.Analysis.abelKernel t a) = 0 := by
  have heq : EqOn (fun a => angularRadialWeight c K e a * Zeta5.Analysis.abelKernel t a)
      (fun _ => (0 : ℝ)) (uIcc t b) := by
    rw [uIcc_of_le htb]
    intro a ha
    change angularRadialWeight c K e a * Zeta5.Analysis.abelKernel t a = 0
    rw [Zeta5.Analysis.abelKernel_eq_zero_of_le ht ha.1, mul_zero]
  refine ⟨(intervalIntegrable_congr (heq.mono uIoc_subset_uIcc)).mpr intervalIntegrable_const, ?_⟩
  rw [intervalIntegral.integral_congr heq, intervalIntegral.integral_zero]

theorem angularRadialWeight_abel_truncated (c : ℝ) (K e : Fin n → ℝ)
    (hc : 0 < c) (hK : ∀ j, 0 ≤ K j) (he : ∀ j, 0 < e j)
    {b t : ℝ} (hb : 0 ≤ b) (ht : 0 < t) :
    IntervalIntegrable (fun a => angularRadialWeight c K e a * Zeta5.Analysis.abelKernel t a)
      volume 0 b ∧
      (∫ a in 0..b, angularRadialWeight c K e a * Zeta5.Analysis.abelKernel t a) ≤
        angularEquilibriumSlope c K e t ∧
      (t ≤ b → (∫ a in 0..b, angularRadialWeight c K e a * Zeta5.Analysis.abelKernel t a) =
        angularEquilibriumSlope c K e t) := by
  obtain ⟨hi, hv⟩ := angularRadialWeight_abel_integral (c := c) (K := K) he ht
  by_cases hbt : b ≤ t
  · have hsub : uIcc (0 : ℝ) b ⊆ uIcc 0 t := by
      rw [uIcc_of_le hb, uIcc_of_le ht.le]
      exact Icc_subset_Icc le_rfl hbt
    refine ⟨hi.mono_set hsub, ?_, ?_⟩
    · rw [← hv]
      apply intervalIntegral.integral_mono_interval le_rfl hb hbt _ hi
      filter_upwards [self_mem_ae_restrict measurableSet_Ioc] with a ha
      exact mul_nonneg (angularRadialWeight_nonneg hc hK he ha.1.le)
        (Zeta5.Analysis.abelKernel_nonneg t a)
    · intro htb
      have heq : b = t := le_antisymm hbt htb
      simpa [heq] using hv
  · have htb : t ≤ b := le_of_not_ge hbt
    obtain ⟨htail, htailv⟩ := angularRadialWeight_abel_above c K e ht.le htb
    have hsum := intervalIntegral.integral_add_adjacent_intervals hi htail
    rw [htailv, add_zero, hv] at hsum
    exact ⟨hi.trans htail, hsum.ge, fun _ => hsum.symm⟩

theorem angularMixturePotential_le (c : ℝ) (K e : Fin n → ℝ)
    (hc : 0 < c) (hK : ∀ j, 0 ≤ K j) (he : ∀ j, 0 < e j)
    {b y : ℝ} (hb : 0 ≤ b) (hy : 0 ≤ y) :
    4 * (angularRadialData c K e hc hK he b hb).mixturePotential y -
      angularField c K e (y ^ 2) ≤
      4 * (angularRadialData c K e hc hK he b hb).basePotential := by
  let d := angularRadialData c K e hc hK he b hb
  have hle : (∫ t in 0..y, d.truncatedAbel t) ≤
      ∫ t in 0..y, angularEquilibriumSlope c K e t := by
    apply intervalIntegral.integral_mono_on_of_le_Ioo hy
      (d.truncatedAbel_intervalIntegrable hy)
      ((angularEquilibriumSlope_continuous he).intervalIntegrable 0 y)
    intro t ht
    exact (angularRadialWeight_abel_truncated c K e hc hK he hb ht.1).2.1
  rw [integral_angularEquilibriumSlope he y] at hle
  have hg := d.mixturePotential_growth hy
  change 4 * d.mixturePotential y - angularField c K e (y ^ 2) ≤ 4 * d.basePotential
  linarith

theorem angularMixturePotential_eq (c : ℝ) (K e : Fin n → ℝ)
    (hc : 0 < c) (hK : ∀ j, 0 ≤ K j) (he : ∀ j, 0 < e j)
    {b y : ℝ} (hb : 0 ≤ b) (hy : 0 ≤ y) (hyb : y ≤ b) :
    4 * (angularRadialData c K e hc hK he b hb).mixturePotential y -
      angularField c K e (y ^ 2) =
      4 * (angularRadialData c K e hc hK he b hb).basePotential := by
  let d := angularRadialData c K e hc hK he b hb
  have heq : (∫ t in 0..y, d.truncatedAbel t) =
      ∫ t in 0..y, angularEquilibriumSlope c K e t := by
    apply intervalIntegral.integral_congr_Ioo_of_le hy
    intro t ht
    exact (angularRadialWeight_abel_truncated c K e hc hK he hb ht.1).2.2 (ht.2.le.trans hyb)
  rw [integral_angularEquilibriumSlope he y] at heq
  have hg := d.mixturePotential_growth hy
  change 4 * d.mixturePotential y - angularField c K e (y ^ 2) = 4 * d.basePotential
  linarith

theorem angularMeasure_equilibrium_le (c : ℝ) (K e : Fin n → ℝ)
    (hc : 0 < c) (hK : ∀ j, 0 ≤ K j) (he : ∀ j, 0 < e j)
    {b y : ℝ} (hb : 0 ≤ b) (hy : 0 ≤ y) :
    2 * (∫ w, Real.log |y - w| ∂(angularRadialData c K e hc hK he b hb).squaredMeasure) -
      angularField c K e y ≤ 4 * (angularRadialData c K e hc hK he b hb).basePotential := by
  have h := angularMixturePotential_le c K e hc hK he hb (Real.sqrt_nonneg y)
  rw [Real.sq_sqrt hy] at h
  have hi := (angularRadialData c K e hc hK he b hb).squaredMeasure_log_integral (Real.sqrt_nonneg y)
  rw [Real.sq_sqrt hy] at hi
  linarith

theorem angularMeasure_equilibrium_eq (c : ℝ) (K e : Fin n → ℝ)
    (hc : 0 < c) (hK : ∀ j, 0 ≤ K j) (he : ∀ j, 0 < e j)
    {b y : ℝ} (hb : 0 ≤ b) (hy : 0 ≤ y) (hyb : y ≤ b ^ 2) :
    2 * (∫ w, Real.log |y - w| ∂(angularRadialData c K e hc hK he b hb).squaredMeasure) -
      angularField c K e y = 4 * (angularRadialData c K e hc hK he b hb).basePotential := by
  have hs : Real.sqrt y ≤ b := (Real.sqrt_le_left hb).2 hyb
  have h := angularMixturePotential_eq c K e hc hK he hb (Real.sqrt_nonneg y) hs
  rw [Real.sq_sqrt hy] at h
  have hi := (angularRadialData c K e hc hK he b hb).squaredMeasure_log_integral (Real.sqrt_nonneg y)
  rw [Real.sq_sqrt hy] at hi
  linarith

end Zeta3.Analysis

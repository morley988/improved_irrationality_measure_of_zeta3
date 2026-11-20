import Zeta5.Analysis.ProfileInverse

/-!
# The actual two-window mass and its inverse

The cubic construction uses two unequal windows. Its physical mass is the
arithmetic mean of the two already proved one-window mass functions, at the
same support endpoint. This file proves the inverse and the sound connection
from finite endpoint-sign checks to the true inverse. No numerical premise
is assumed globally, and no root-finding implementation is trusted here.
-/

namespace Zeta3.Analysis

open scoped NNReal
noncomputable section

def physicalMass (s₁ s₂ b : ℝ) : ℝ :=
  (b + 1 - s₁ - s₂ - Real.sqrt (1 + b ^ 2) +
    Real.sqrt (s₁ ^ 2 + b ^ 2) + Real.sqrt (s₂ ^ 2 + b ^ 2)) / 2

def physicalMassSlope (s₁ s₂ b : ℝ) : ℝ :=
  (1 - b / Real.sqrt (1 + b ^ 2) +
    b / Real.sqrt (s₁ ^ 2 + b ^ 2) + b / Real.sqrt (s₂ ^ 2 + b ^ 2)) / 2

theorem physicalMass_eq_average (s₁ s₂ b : ℝ) :
    physicalMass s₁ s₂ b =
      (Zeta5.Analysis.profileMass s₁ b + Zeta5.Analysis.profileMass s₂ b) / 2 := by
  unfold physicalMass Zeta5.Analysis.profileMass
  ring

theorem physicalMassSlope_eq_average (s₁ s₂ b : ℝ) :
    physicalMassSlope s₁ s₂ b =
      (Zeta5.Analysis.profileMassSlope s₁ b +
        Zeta5.Analysis.profileMassSlope s₂ b) / 2 := by
  unfold physicalMassSlope Zeta5.Analysis.profileMassSlope
  ring

@[simp] theorem physicalMass_zero {s₁ s₂ : ℝ} (h₁ : 0 ≤ s₁) (h₂ : 0 ≤ s₂) :
    physicalMass s₁ s₂ 0 = 0 := by
  rw [physicalMass_eq_average, Zeta5.Analysis.profileMass_zero h₁,
    Zeta5.Analysis.profileMass_zero h₂]
  norm_num

theorem physicalMass_pos {s₁ s₂ b : ℝ} (h₁ : 0 < s₁) (h₂ : 0 < s₂) (hb : 0 < b) :
    0 < physicalMass s₁ s₂ b := by
  rw [physicalMass_eq_average]
  exact div_pos (add_pos (Zeta5.Analysis.profileMass_pos h₁ hb)
    (Zeta5.Analysis.profileMass_pos h₂ hb)) (by norm_num)

theorem physicalMass_nonneg {s₁ s₂ b : ℝ} (h₁ : 0 < s₁) (h₂ : 0 < s₂) (hb : 0 ≤ b) :
    0 ≤ physicalMass s₁ s₂ b := by
  rw [physicalMass_eq_average]
  exact div_nonneg (add_nonneg (Zeta5.Analysis.profileMass_nonneg h₁ hb)
    (Zeta5.Analysis.profileMass_nonneg h₂ hb)) (by norm_num)

theorem physicalMass_hasDerivAt {s₁ s₂ b : ℝ} (h₁ : 0 < s₁) (h₂ : 0 < s₂) :
    HasDerivAt (physicalMass s₁ s₂) (physicalMassSlope s₁ s₂ b) b := by
  have h := ((Zeta5.Analysis.profileMass_hasDerivAt h₁ (b := b)).add
    (Zeta5.Analysis.profileMass_hasDerivAt h₂ (b := b))).div_const 2
  simpa only [Pi.add_apply, ← physicalMass_eq_average, ← physicalMassSlope_eq_average] using h

theorem physicalMassSlope_pos {s₁ s₂ b : ℝ} (h₁ : 0 < s₁) (h₂ : 0 < s₂) (hb : 0 < b) :
    0 < physicalMassSlope s₁ s₂ b := by
  rw [physicalMassSlope_eq_average]
  exact div_pos (add_pos (Zeta5.Analysis.profileMassSlope_pos h₁ hb)
    (Zeta5.Analysis.profileMassSlope_pos h₂ hb)) (by norm_num)

theorem physicalMass_continuous {s₁ s₂ : ℝ} (h₁ : 0 < s₁) (h₂ : 0 < s₂) :
    Continuous (physicalMass s₁ s₂) :=
  continuous_iff_continuousAt.mpr fun _ => (physicalMass_hasDerivAt h₁ h₂).continuousAt

theorem physicalMass_strictMonoOn {s₁ s₂ : ℝ} (h₁ : 0 < s₁) (h₂ : 0 < s₂) :
    StrictMonoOn (physicalMass s₁ s₂) (Set.Ici 0) := by
  intro a ha b hb hab
  have hma := Zeta5.Analysis.profileMass_strictMonoOn h₁ ha hb hab
  have hmb := Zeta5.Analysis.profileMass_strictMonoOn h₂ ha hb hab
  rw [physicalMass_eq_average, physicalMass_eq_average]
  linarith

theorem endpoint_lt_shifted_mass {s₁ s₂ b : ℝ}
    (h₁ : 0 < s₁) (h₂ : 0 < s₂) (hb : 0 < b) :
    b < (s₁ + s₂) / 2 + physicalMass s₁ s₂ b := by
  have ha := Zeta5.Analysis.endpoint_lt_shifted_mass h₁ hb
  have hb' := Zeta5.Analysis.endpoint_lt_shifted_mass h₂ hb
  rw [physicalMass_eq_average]
  linarith

theorem exists_physicalMass_eq {s₁ s₂ v : ℝ}
    (h₁ : 0 < s₁) (h₂ : 0 < s₂) (hv : 0 ≤ v) :
    ∃ b : ℝ, 0 ≤ b ∧ physicalMass s₁ s₂ b = v := by
  let B : ℝ := v + (s₁ + s₂) / 2 + 1
  have hB : 0 < B := by dsimp [B]; linarith
  have hmB : v ≤ physicalMass s₁ s₂ B := by
    have h := endpoint_lt_shifted_mass h₁ h₂ hB
    dsimp [B] at h ⊢
    linarith
  have hm0 : physicalMass s₁ s₂ 0 ≤ v := by
    simpa only [physicalMass_zero h₁.le h₂.le] using hv
  obtain ⟨b, hb, hbu⟩ := intermediate_value_Icc hB.le
    (physicalMass_continuous h₁ h₂).continuousOn ⟨hm0, hmB⟩
  exact ⟨b, hb.1, hbu⟩

def physicalMassNNReal (s₁ s₂ : ℝ) (h₁ : 0 < s₁) (h₂ : 0 < s₂) (b : ℝ≥0) : ℝ≥0 :=
  ⟨physicalMass s₁ s₂ b, physicalMass_nonneg h₁ h₂ b.coe_nonneg⟩

theorem physicalMassNNReal_strictMono (s₁ s₂ : ℝ) (h₁ : 0 < s₁) (h₂ : 0 < s₂) :
    StrictMono (physicalMassNNReal s₁ s₂ h₁ h₂) := by
  intro a b hab
  exact physicalMass_strictMonoOn h₁ h₂ a.coe_nonneg b.coe_nonneg hab

theorem physicalMassNNReal_surjective (s₁ s₂ : ℝ) (h₁ : 0 < s₁) (h₂ : 0 < s₂) :
    Function.Surjective (physicalMassNNReal s₁ s₂ h₁ h₂) := by
  intro v
  obtain ⟨b, hb, hbu⟩ := exists_physicalMass_eq h₁ h₂ v.coe_nonneg
  refine ⟨⟨b, hb⟩, ?_⟩
  apply Subtype.ext
  exact hbu

def physicalMassOrderIso (s₁ s₂ : ℝ) (h₁ : 0 < s₁) (h₂ : 0 < s₂) : ℝ≥0 ≃o ℝ≥0 :=
  StrictMono.orderIsoOfSurjective (physicalMassNNReal s₁ s₂ h₁ h₂)
    (physicalMassNNReal_strictMono s₁ s₂ h₁ h₂)
    (physicalMassNNReal_surjective s₁ s₂ h₁ h₂)

def physicalEndpoint (s₁ s₂ : ℝ) (h₁ : 0 < s₁) (h₂ : 0 < s₂) (v : ℝ) : ℝ :=
  ((physicalMassOrderIso s₁ s₂ h₁ h₂).symm v.toNNReal : ℝ)

theorem physicalEndpoint_nonneg (s₁ s₂ : ℝ) (h₁ : 0 < s₁) (h₂ : 0 < s₂) (v : ℝ) :
    0 ≤ physicalEndpoint s₁ s₂ h₁ h₂ v := NNReal.coe_nonneg _

theorem physicalMass_endpoint (s₁ s₂ : ℝ) (h₁ : 0 < s₁) (h₂ : 0 < s₂)
    {v : ℝ} (hv : 0 ≤ v) :
    physicalMass s₁ s₂ (physicalEndpoint s₁ s₂ h₁ h₂ v) = v := by
  have h := congrArg (fun x : ℝ≥0 => (x : ℝ))
    ((physicalMassOrderIso s₁ s₂ h₁ h₂).apply_symm_apply v.toNNReal)
  change physicalMass s₁ s₂ (physicalEndpoint s₁ s₂ h₁ h₂ v) = (v.toNNReal : ℝ) at h
  simpa only [Real.coe_toNNReal v hv] using h

theorem physicalEndpoint_mass (s₁ s₂ : ℝ) (h₁ : 0 < s₁) (h₂ : 0 < s₂)
    {b : ℝ} (hb : 0 ≤ b) :
    physicalEndpoint s₁ s₂ h₁ h₂ (physicalMass s₁ s₂ b) = b := by
  have h := congrArg (fun x : ℝ≥0 => (x : ℝ))
    ((physicalMassOrderIso s₁ s₂ h₁ h₂).symm_apply_apply (⟨b, hb⟩ : ℝ≥0))
  have hm : (physicalMass s₁ s₂ b).toNNReal = physicalMassNNReal s₁ s₂ h₁ h₂ ⟨b, hb⟩ := by
    apply Subtype.ext
    exact Real.coe_toNNReal _ (physicalMass_nonneg h₁ h₂ hb)
  change ((physicalMassOrderIso s₁ s₂ h₁ h₂).symm
    (physicalMassNNReal s₁ s₂ h₁ h₂ ⟨b, hb⟩) : ℝ) = b at h
  simpa only [physicalEndpoint, hm] using h

@[simp] theorem physicalEndpoint_zero (s₁ s₂ : ℝ) (h₁ : 0 < s₁) (h₂ : 0 < s₂) :
    physicalEndpoint s₁ s₂ h₁ h₂ 0 = 0 := by
  simpa only [physicalMass_zero h₁.le h₂.le] using
    physicalEndpoint_mass s₁ s₂ h₁ h₂ (b := 0) le_rfl

theorem physicalEndpoint_pos (s₁ s₂ : ℝ) (h₁ : 0 < s₁) (h₂ : 0 < s₂)
    {v : ℝ} (hv : 0 < v) : 0 < physicalEndpoint s₁ s₂ h₁ h₂ v := by
  have hn := physicalEndpoint_nonneg s₁ s₂ h₁ h₂ v
  have hm := physicalMass_endpoint s₁ s₂ h₁ h₂ hv.le
  by_contra! h
  have hz : physicalEndpoint s₁ s₂ h₁ h₂ v = 0 := le_antisymm h hn
  rw [hz, physicalMass_zero h₁.le h₂.le] at hm
  linarith

theorem physicalEndpoint_continuous (s₁ s₂ : ℝ) (h₁ : 0 < s₁) (h₂ : 0 < s₂) :
    Continuous (physicalEndpoint s₁ s₂ h₁ h₂) :=
  NNReal.continuous_coe.comp ((physicalMassOrderIso s₁ s₂ h₁ h₂).symm.continuous.comp
    continuous_real_toNNReal)

theorem physicalEndpoint_hasDerivAt (s₁ s₂ : ℝ) (h₁ : 0 < s₁) (h₂ : 0 < s₂)
    {v : ℝ} (hv : 0 < v) :
    HasDerivAt (physicalEndpoint s₁ s₂ h₁ h₂)
      (physicalMassSlope s₁ s₂ (physicalEndpoint s₁ s₂ h₁ h₂ v))⁻¹ v := by
  apply HasDerivAt.of_local_left_inverse (physicalEndpoint_continuous s₁ s₂ h₁ h₂).continuousAt
    (physicalMass_hasDerivAt h₁ h₂)
    (ne_of_gt (physicalMassSlope_pos h₁ h₂ (physicalEndpoint_pos s₁ s₂ h₁ h₂ hv)))
  filter_upwards [isOpen_Ioi.mem_nhds hv] with w hw
  exact physicalMass_endpoint s₁ s₂ h₁ h₂ hw.le

/-- A finite pair of mass inequalities bounds the actual inverse endpoint. -/
theorem physicalEndpoint_mem_of_mass_bracket (s₁ s₂ : ℝ)
    (h₁ : 0 < s₁) (h₂ : 0 < s₂) {v lo hi : ℝ} (hv : 0 ≤ v)
    (hlo : 0 ≤ lo) (hhi : 0 ≤ hi)
    (hl : physicalMass s₁ s₂ lo ≤ v) (hu : v ≤ physicalMass s₁ s₂ hi) :
    lo ≤ physicalEndpoint s₁ s₂ h₁ h₂ v ∧ physicalEndpoint s₁ s₂ h₁ h₂ v ≤ hi := by
  have hb := physicalEndpoint_nonneg s₁ s₂ h₁ h₂ v
  have hm := physicalMass_endpoint s₁ s₂ h₁ h₂ hv
  constructor
  · by_contra! h
    have hc := physicalMass_strictMonoOn h₁ h₂ hb hlo h
    rw [hm] at hc
    exact (not_lt_of_ge hl) hc
  · by_contra! h
    have hc := physicalMass_strictMonoOn h₁ h₂ hhi hb h
    rw [hm] at hc
    exact (not_lt_of_ge hu) hc

/-- A simple coercive estimate useful for the sign of the saving derivative. -/
theorem half_endpoint_le_physicalMass {s₁ s₂ b : ℝ}
    (h₁ : 0 ≤ s₁) (h₁one : s₁ ≤ 1) (h₂ : 0 ≤ s₂) :
    b / 2 ≤ physicalMass s₁ s₂ b := by
  have hc := Real.sqrt_nonneg (s₁ ^ 2 + b ^ 2)
  have hd := Real.sqrt_nonneg (s₂ ^ 2 + b ^ 2)
  have he := Real.sqrt_nonneg (1 + b ^ 2)
  have hc2 := Real.sq_sqrt (show 0 ≤ s₁ ^ 2 + b ^ 2 by positivity)
  have hd2 := Real.sq_sqrt (show 0 ≤ s₂ ^ 2 + b ^ 2 by positivity)
  have he2 := Real.sq_sqrt (show 0 ≤ (1 : ℝ) + b ^ 2 by positivity)
  have hcs : s₁ ≤ Real.sqrt (s₁ ^ 2 + b ^ 2) := by nlinarith [sq_nonneg b]
  have hds : s₂ ≤ Real.sqrt (s₂ ^ 2 + b ^ 2) := by nlinarith [sq_nonneg b]
  have hs : Real.sqrt (1 + b ^ 2) ≤ Real.sqrt (s₁ ^ 2 + b ^ 2) + 1 - s₁ := by
    have hp := mul_nonneg (sub_nonneg.mpr h₁one) (sub_nonneg.mpr hcs)
    nlinarith
  unfold physicalMass
  linarith

theorem physicalEndpoint_le_twice (s₁ s₂ : ℝ) (h₁ : 0 < s₁) (h₂ : 0 < s₂)
    (h₁one : s₁ ≤ 1) {v : ℝ} (hv : 0 ≤ v) :
    physicalEndpoint s₁ s₂ h₁ h₂ v ≤ 2 * v := by
  have h := half_endpoint_le_physicalMass (b := physicalEndpoint s₁ s₂ h₁ h₂ v)
    h₁.le h₁one h₂.le
  rw [physicalMass_endpoint s₁ s₂ h₁ h₂ hv] at h
  linarith

end
end Zeta3.Analysis

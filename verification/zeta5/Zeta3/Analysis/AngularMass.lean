import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.Calculus.Deriv.Inverse
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Topology.Order.MonotoneContinuity
import Mathlib.Topology.Instances.NNReal.Lemmas
import Mathlib.Order.Hom.Set
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# The actual finite-charge angular mass and its inverse

The angular endpoint is constructed from the explicit mass equation.  Its
existence, uniqueness, continuity, monotonicity and bracket interpretation are
proved here.  No numerical or analytic axiom is introduced.

The numerical certificate specializes this finite family to 128 positive
rational pole distances and equal positive rational weights.  This file is
generic in the number of charges and permits zero weights.
-/

namespace Zeta3.Analysis

open scoped BigOperators NNReal

noncomputable section

variable {n : ℕ}

/-- Mass of the explicit finite-charge angular equilibrium candidate. -/
def angularMass (c : ℝ) (K e : Fin n → ℝ) (B : ℝ) : ℝ :=
  c * B / 2 + ∑ j, K j * (1 - 1 / Real.sqrt (1 + B / e j))

/-- Derivative of the mass with respect to its support parameter. -/
def angularMassSlope (c : ℝ) (K e : Fin n → ℝ) (B : ℝ) : ℝ :=
  c / 2 + ∑ j, K j / (2 * e j * Real.sqrt (1 + B / e j) ^ 3)

@[simp] theorem angularMass_zero (c : ℝ) (K e : Fin n → ℝ) :
    angularMass c K e 0 = 0 := by
  simp [angularMass]

theorem angular_sqrt_pos {e B : ℝ} (he : 0 < e) (hB : 0 ≤ B) :
    0 < Real.sqrt (1 + B / e) := by
  apply Real.sqrt_pos.2
  have h := div_nonneg hB he.le
  linarith

theorem angular_charge_hasDerivAt {K e B : ℝ} (he : 0 < e) (hB : 0 ≤ B) :
    HasDerivAt (fun x : ℝ => K * (1 - 1 / Real.sqrt (1 + x / e)))
      (K / (2 * e * Real.sqrt (1 + B / e) ^ 3)) B := by
  have harg : 1 + B / e ≠ 0 := by
    have h := div_nonneg hB he.le
    linarith
  have hs := angular_sqrt_pos he hB
  have ds := (((hasDerivAt_id B).div_const e).const_add 1).sqrt harg
  have di := (hasDerivAt_const B (1 : ℝ)).div ds hs.ne'
  have d := (di.const_sub 1).const_mul K
  convert! d using 1
  simp only [one_mul, zero_mul, zero_sub, id_eq]
  field_simp

theorem angularMass_hasDerivAt {c : ℝ} {K e : Fin n → ℝ}
    (he : ∀ j, 0 < e j) {B : ℝ} (hB : 0 ≤ B) :
    HasDerivAt (angularMass c K e) (angularMassSlope c K e B) B := by
  have ds := HasDerivAt.fun_sum (u := Finset.univ)
    (fun j _ => angular_charge_hasDerivAt (K := K j) (he j) hB)
  have dl := ((hasDerivAt_id B).const_mul c).div_const 2
  convert! dl.add ds using 1
  simp [angularMassSlope]

theorem angularMass_continuousOn {c : ℝ} {K e : Fin n → ℝ}
    (he : ∀ j, 0 < e j) :
    ContinuousOn (angularMass c K e) (Set.Ici 0) := by
  intro B hB
  exact (angularMass_hasDerivAt he hB).continuousAt.continuousWithinAt

theorem angularMassSlope_pos {c : ℝ} {K e : Fin n → ℝ}
    (hc : 0 < c) (hK : ∀ j, 0 ≤ K j) (he : ∀ j, 0 < e j)
    {B : ℝ} (hB : 0 ≤ B) :
    0 < angularMassSlope c K e B := by
  have hsum : 0 ≤ ∑ j, K j / (2 * e j * Real.sqrt (1 + B / e j) ^ 3) := by
    apply Finset.sum_nonneg
    intro j _
    have hs := angular_sqrt_pos (he j) hB
    exact div_nonneg (hK j)
      (mul_nonneg (mul_nonneg (by norm_num) (he j).le) (pow_nonneg hs.le _))
  dsimp [angularMassSlope]
  have hlin : 0 < c / 2 := by positivity
  linarith

theorem angularMass_strictMonoOn {c : ℝ} {K e : Fin n → ℝ}
    (hc : 0 < c) (hK : ∀ j, 0 ≤ K j) (he : ∀ j, 0 < e j) :
    StrictMonoOn (angularMass c K e) (Set.Ici 0) := by
  apply strictMonoOn_of_deriv_pos (convex_Ici 0) (angularMass_continuousOn he)
  intro B hB
  have hB' : 0 < B := by simpa only [interior_Ici, Set.mem_Ioi] using hB
  rw [(angularMass_hasDerivAt he hB'.le).deriv]
  exact angularMassSlope_pos hc hK he hB'.le

theorem angularMass_lower_bound {c : ℝ} {K e : Fin n → ℝ}
    (hK : ∀ j, 0 ≤ K j) (he : ∀ j, 0 < e j) {B : ℝ} (hB : 0 ≤ B) :
    c * B / 2 ≤ angularMass c K e B := by
  have hsum : 0 ≤ ∑ j, K j * (1 - 1 / Real.sqrt (1 + B / e j)) := by
    apply Finset.sum_nonneg
    intro j _
    have hs : 1 ≤ Real.sqrt (1 + B / e j) := by
      apply Real.one_le_sqrt.2
      have h := div_nonneg hB (he j).le
      linarith
    have hp : 0 < Real.sqrt (1 + B / e j) := lt_of_lt_of_le zero_lt_one hs
    have hi : 1 / Real.sqrt (1 + B / e j) ≤ 1 := (div_le_one hp).2 hs
    exact mul_nonneg (hK j) (sub_nonneg.2 hi)
  dsimp [angularMass]
  linarith

theorem angularMass_nonneg {c : ℝ} {K e : Fin n → ℝ}
    (hc : 0 < c) (hK : ∀ j, 0 ≤ K j) (he : ∀ j, 0 < e j)
    {B : ℝ} (hB : 0 ≤ B) :
    0 ≤ angularMass c K e B := by
  exact le_trans (by positivity) (angularMass_lower_bound hK he hB)

theorem exists_angularMass_eq {c : ℝ} {K e : Fin n → ℝ}
    (hc : 0 < c) (hK : ∀ j, 0 ≤ K j) (he : ∀ j, 0 < e j)
    {t : ℝ} (ht : 0 ≤ t) :
    ∃ B : ℝ, 0 ≤ B ∧ angularMass c K e B = t := by
  let b : ℝ := 2 * t / c
  have hb : 0 ≤ b := by dsimp [b]; positivity
  have hlin : c * b / 2 = t := by dsimp [b]; field_simp
  have hupper : t ≤ angularMass c K e b := by
    rw [← hlin]
    exact angularMass_lower_bound hK he hb
  have hlower : angularMass c K e 0 ≤ t := by simpa using ht
  have hcont : ContinuousOn (angularMass c K e) (Set.Icc 0 b) :=
    (angularMass_continuousOn he).mono (fun _ hx => hx.1)
  obtain ⟨B, hB, hmass⟩ := intermediate_value_Icc hb hcont ⟨hlower, hupper⟩
  exact ⟨B, hB.1, hmass⟩

theorem existsUnique_angularMass_eq {c : ℝ} {K e : Fin n → ℝ}
    (hc : 0 < c) (hK : ∀ j, 0 ≤ K j) (he : ∀ j, 0 < e j)
    {t : ℝ} (ht : 0 ≤ t) :
    ∃! B : ℝ, 0 ≤ B ∧ angularMass c K e B = t := by
  obtain ⟨B, hB, hmass⟩ := exists_angularMass_eq hc hK he ht
  refine ⟨B, ⟨hB, hmass⟩, ?_⟩
  intro C hC
  exact ((angularMass_strictMonoOn hc hK he).eq_iff_eq hC.1 hB).1
    (hC.2.trans hmass.symm)

def angularMassNNReal (c : ℝ) (K e : Fin n → ℝ)
    (hc : 0 < c) (hK : ∀ j, 0 ≤ K j) (he : ∀ j, 0 < e j)
    (B : ℝ≥0) : ℝ≥0 :=
  ⟨angularMass c K e B, angularMass_nonneg hc hK he B.coe_nonneg⟩

theorem angularMassNNReal_strictMono (c : ℝ) (K e : Fin n → ℝ)
    (hc : 0 < c) (hK : ∀ j, 0 ≤ K j) (he : ∀ j, 0 < e j) :
    StrictMono (angularMassNNReal c K e hc hK he) := by
  intro A B hAB
  exact angularMass_strictMonoOn hc hK he A.coe_nonneg B.coe_nonneg hAB

theorem angularMassNNReal_surjective (c : ℝ) (K e : Fin n → ℝ)
    (hc : 0 < c) (hK : ∀ j, 0 ≤ K j) (he : ∀ j, 0 < e j) :
    Function.Surjective (angularMassNNReal c K e hc hK he) := by
  intro t
  obtain ⟨B, hB, ht⟩ := exists_angularMass_eq hc hK he t.coe_nonneg
  refine ⟨⟨B, hB⟩, ?_⟩
  apply Subtype.ext
  exact ht

def angularMassOrderIso (c : ℝ) (K e : Fin n → ℝ)
    (hc : 0 < c) (hK : ∀ j, 0 ≤ K j) (he : ∀ j, 0 < e j) : ℝ≥0 ≃o ℝ≥0 :=
  StrictMono.orderIsoOfSurjective (angularMassNNReal c K e hc hK he)
    (angularMassNNReal_strictMono c K e hc hK he)
    (angularMassNNReal_surjective c K e hc hK he)

/-- The actual inverse mass endpoint, extended by zero at negative inputs. -/
def angularEndpoint (c : ℝ) (K e : Fin n → ℝ)
    (hc : 0 < c) (hK : ∀ j, 0 ≤ K j) (he : ∀ j, 0 < e j) (t : ℝ) : ℝ :=
  ((angularMassOrderIso c K e hc hK he).symm t.toNNReal : ℝ)

theorem angularEndpoint_nonneg (c : ℝ) (K e : Fin n → ℝ)
    (hc : 0 < c) (hK : ∀ j, 0 ≤ K j) (he : ∀ j, 0 < e j) (t : ℝ) :
    0 ≤ angularEndpoint c K e hc hK he t := NNReal.coe_nonneg _

theorem angularMass_endpoint (c : ℝ) (K e : Fin n → ℝ)
    (hc : 0 < c) (hK : ∀ j, 0 ≤ K j) (he : ∀ j, 0 < e j)
    {t : ℝ} (ht : 0 ≤ t) :
    angularMass c K e (angularEndpoint c K e hc hK he t) = t := by
  have h := congrArg (fun x : ℝ≥0 => (x : ℝ))
    ((angularMassOrderIso c K e hc hK he).apply_symm_apply t.toNNReal)
  change angularMass c K e (angularEndpoint c K e hc hK he t) = (t.toNNReal : ℝ) at h
  simpa only [Real.coe_toNNReal t ht] using h

theorem angularEndpoint_mass (c : ℝ) (K e : Fin n → ℝ)
    (hc : 0 < c) (hK : ∀ j, 0 ≤ K j) (he : ∀ j, 0 < e j)
    {B : ℝ} (hB : 0 ≤ B) :
    angularEndpoint c K e hc hK he (angularMass c K e B) = B := by
  have h := congrArg (fun x : ℝ≥0 => (x : ℝ))
    ((angularMassOrderIso c K e hc hK he).symm_apply_apply (⟨B, hB⟩ : ℝ≥0))
  have hm : (angularMass c K e B).toNNReal = angularMassNNReal c K e hc hK he ⟨B, hB⟩ := by
    apply Subtype.ext
    exact Real.coe_toNNReal _ (angularMass_nonneg hc hK he hB)
  change ((angularMassOrderIso c K e hc hK he).symm
    (angularMassNNReal c K e hc hK he ⟨B, hB⟩) : ℝ) = B at h
  simpa only [angularEndpoint, hm] using h

@[simp] theorem angularEndpoint_zero (c : ℝ) (K e : Fin n → ℝ)
    (hc : 0 < c) (hK : ∀ j, 0 ≤ K j) (he : ∀ j, 0 < e j) :
    angularEndpoint c K e hc hK he 0 = 0 := by
  simpa only [angularMass_zero] using angularEndpoint_mass c K e hc hK he (B := 0) le_rfl

theorem angularEndpoint_pos (c : ℝ) (K e : Fin n → ℝ)
    (hc : 0 < c) (hK : ∀ j, 0 ≤ K j) (he : ∀ j, 0 < e j)
    {t : ℝ} (ht : 0 < t) :
    0 < angularEndpoint c K e hc hK he t := by
  have hn := angularEndpoint_nonneg c K e hc hK he t
  have hm := angularMass_endpoint c K e hc hK he ht.le
  by_contra! h
  have hz := le_antisymm h hn
  rw [hz, angularMass_zero] at hm
  linarith

theorem angularEndpoint_continuous (c : ℝ) (K e : Fin n → ℝ)
    (hc : 0 < c) (hK : ∀ j, 0 ≤ K j) (he : ∀ j, 0 < e j) :
    Continuous (angularEndpoint c K e hc hK he) :=
  NNReal.continuous_coe.comp ((angularMassOrderIso c K e hc hK he).symm.continuous.comp
    continuous_real_toNNReal)

theorem angularEndpoint_strictMonoOn (c : ℝ) (K e : Fin n → ℝ)
    (hc : 0 < c) (hK : ∀ j, 0 ≤ K j) (he : ∀ j, 0 < e j) :
    StrictMonoOn (angularEndpoint c K e hc hK he) (Set.Ici 0) := by
  intro s hs t ht hst
  by_contra! h
  have hm := (angularMass_strictMonoOn hc hK he).monotoneOn
    (angularEndpoint_nonneg c K e hc hK he t)
    (angularEndpoint_nonneg c K e hc hK he s) h
  rw [angularMass_endpoint c K e hc hK he ht,
    angularMass_endpoint c K e hc hK he hs] at hm
  exact (not_le_of_gt hst) hm

theorem angularEndpoint_hasDerivAt (c : ℝ) (K e : Fin n → ℝ)
    (hc : 0 < c) (hK : ∀ j, 0 ≤ K j) (he : ∀ j, 0 < e j)
    {t : ℝ} (ht : 0 < t) :
    HasDerivAt (angularEndpoint c K e hc hK he)
      (angularMassSlope c K e (angularEndpoint c K e hc hK he t))⁻¹ t := by
  have hB := angularEndpoint_nonneg c K e hc hK he t
  apply HasDerivAt.of_local_left_inverse
    (angularEndpoint_continuous c K e hc hK he).continuousAt
    (angularMass_hasDerivAt he hB) (ne_of_gt (angularMassSlope_pos hc hK he hB))
  filter_upwards [isOpen_Ioi.mem_nhds ht] with v hv
  exact angularMass_endpoint c K e hc hK he hv.le

/-- Exact endpoint sign inequalities are sufficient to certify the chosen inverse. -/
theorem angularEndpoint_mem_Ioo_of_signs (c : ℝ) (K e : Fin n → ℝ)
    (hc : 0 < c) (hK : ∀ j, 0 ≤ K j) (he : ∀ j, 0 < e j)
    {t a b : ℝ} (ht : 0 ≤ t) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hleft : angularMass c K e a < t) (hright : t < angularMass c K e b) :
    angularEndpoint c K e hc hK he t ∈ Set.Ioo a b := by
  have hB := angularEndpoint_nonneg c K e hc hK he t
  have hm := angularMass_endpoint c K e hc hK he ht
  constructor
  · by_contra! h
    have hh := (angularMass_strictMonoOn hc hK he).monotoneOn hB ha h
    rw [hm] at hh
    exact (not_le_of_gt hleft) hh
  · by_contra! h
    have hh := (angularMass_strictMonoOn hc hK he).monotoneOn hb hB h
    rw [hm] at hh
    exact (not_le_of_gt hright) hh

theorem angularEndpoint_mem_Icc_of_signs (c : ℝ) (K e : Fin n → ℝ)
    (hc : 0 < c) (hK : ∀ j, 0 ≤ K j) (he : ∀ j, 0 < e j)
    {t a b : ℝ} (ht : 0 ≤ t) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hleft : angularMass c K e a ≤ t) (hright : t ≤ angularMass c K e b) :
    angularEndpoint c K e hc hK he t ∈ Set.Icc a b := by
  have hB := angularEndpoint_nonneg c K e hc hK he t
  have hm := angularMass_endpoint c K e hc hK he ht
  constructor
  · apply ((angularMass_strictMonoOn hc hK he).le_iff_le ha hB).1
    simpa only [hm] using hleft
  · apply ((angularMass_strictMonoOn hc hK he).le_iff_le hB hb).1
    simpa only [hm] using hright

theorem angularEndpoint_upper_bound (c : ℝ) (K e : Fin n → ℝ)
    (hc : 0 < c) (hK : ∀ j, 0 ≤ K j) (he : ∀ j, 0 < e j)
    {t : ℝ} (ht : 0 ≤ t) :
    angularEndpoint c K e hc hK he t ≤ 2 * t / c := by
  have h := angularMass_lower_bound (c := c) hK he (angularEndpoint_nonneg c K e hc hK he t)
  rw [angularMass_endpoint c K e hc hK he ht] at h
  apply (le_div_iff₀ hc).2
  nlinarith

/-! The concrete rational charge family used by the external certificate. -/

namespace CertificateAngular

def coefficient : ℝ := 3835733171 / 31250000000

def contour : ℝ := 1000001 / 1000000

def weight (_ : Fin 128) : ℝ := 3 / 1280

def node (j : Fin 128) : ℝ := 2 / 5 + 3 * (2 * (j : ℝ) + 1) / 1280

def pole (j : Fin 128) : ℝ :=
  (contour ^ 2 - node j ^ 2) ^ 2 / (2 * contour ^ 2 * node j ^ 2)

theorem coefficient_pos : 0 < coefficient := by norm_num [coefficient]

theorem weight_pos (j : Fin 128) : 0 < weight j := by norm_num [weight]

theorem weight_nonneg (j : Fin 128) : 0 ≤ weight j := (weight_pos j).le

theorem node_bounds (j : Fin 128) : (2 : ℝ) / 5 < node j ∧ node j < 1 := by
  have hjNat : j.val ≤ 127 := Nat.le_of_lt_succ j.isLt
  have hj : (j : ℝ) ≤ 127 := by exact_mod_cast hjNat
  have hj0 : 0 ≤ (j : ℝ) := by positivity
  dsimp [node]
  constructor <;> linarith

theorem pole_pos (j : Fin 128) : 0 < pole j := by
  have hn := node_bounds j
  have hn0 : 0 < node j := by linarith
  have hu : 1 < contour := by norm_num [contour]
  have hu0 : 0 < contour := by linarith
  have hd : 0 < contour ^ 2 - node j ^ 2 := by nlinarith
  dsimp [pole]
  exact div_pos (sq_pos_of_pos hd) (by positivity)

/-- The unique nonnegative endpoint for the actual 128-charge family. -/
def endpoint (t : ℝ) : ℝ :=
  angularEndpoint coefficient weight pole coefficient_pos weight_nonneg pole_pos t

theorem mass_endpoint {t : ℝ} (ht : 0 ≤ t) :
    angularMass coefficient weight pole (endpoint t) = t :=
  angularMass_endpoint coefficient weight pole coefficient_pos weight_nonneg pole_pos ht

theorem endpoint_nonneg (t : ℝ) : 0 ≤ endpoint t :=
  angularEndpoint_nonneg coefficient weight pole coefficient_pos weight_nonneg pole_pos t

theorem endpoint_mem_Ioo_of_signs {t a b : ℝ}
    (ht : 0 ≤ t) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hleft : angularMass coefficient weight pole a < t)
    (hright : t < angularMass coefficient weight pole b) :
    endpoint t ∈ Set.Ioo a b :=
  angularEndpoint_mem_Ioo_of_signs coefficient weight pole
    coefficient_pos weight_nonneg pole_pos ht ha hb hleft hright

end CertificateAngular

end

end Zeta3.Analysis

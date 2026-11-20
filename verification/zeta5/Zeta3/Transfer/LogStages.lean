import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Choosing polynomial stages on a logarithmic denominator scale

The stage `floor (c log q)` is sufficient for a family indexed by all natural
numbers. A fixed physical stage modulus is handled by indexing that family
as `P_(L*n)` and rescaling the three rates; no divisibility condition on
`floor (c log q)` is required.
-/

noncomputable section
namespace Zeta3.Transfer
open Filter
open scoped Topology

def logarithmicStage (c : ℝ) (q : ℕ) : ℕ := ⌊c * Real.log (q : ℝ)⌋₊

theorem log_denominator_tendsto_atTop :
    Tendsto (fun q : ℕ => Real.log (q : ℝ)) atTop atTop :=
  Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop

theorem logarithmicStage_tendsto_atTop {c : ℝ} (hc : 0 < c) :
    Tendsto (logarithmicStage c) atTop atTop := by
  exact tendsto_nat_floor_atTop.comp
    (Tendsto.const_mul_atTop hc log_denominator_tendsto_atTop)

theorem logarithmicStage_ratio {c : ℝ} (hc : 0 ≤ c) :
    Tendsto (fun q : ℕ => (logarithmicStage c q : ℝ) / Real.log (q : ℝ))
      atTop (𝓝 c) := by
  exact (tendsto_nat_floor_mul_div_atTop hc).comp log_denominator_tendsto_atTop

theorem logarithmicStage_reciprocal_ratio {c : ℝ} (hc : 0 < c) :
    Tendsto (fun q : ℕ => Real.log (q : ℝ) / (logarithmicStage c q : ℝ))
      atTop (𝓝 c⁻¹) := by
  simpa only [inv_div] using (logarithmicStage_ratio hc.le).inv₀ hc.ne'

theorem inverse_logarithmicStage_tendsto_zero {c : ℝ} (hc : 0 < c) :
    Tendsto (fun q : ℕ => (logarithmicStage c q : ℝ)⁻¹) atTop (𝓝 0) :=
  tendsto_inv_atTop_zero.comp
    (tendsto_natCast_atTop_atTop.comp (logarithmicStage_tendsto_atTop hc))

/-- If `a*c < ν`, an approximation on the `q^(-ν)` scale lies inside the
local response radius at the selected stage, eventually in `q`. -/
theorem eventually_rpow_le_stage_radius {c a ν : ℝ} (hc : 0 < c)
    (hac : a * c < ν) :
    ∀ᶠ q : ℕ in atTop,
      (q : ℝ) ^ (-ν) ≤ Real.exp (-a * (logarithmicStage c q : ℝ)) := by
  have hlim := (logarithmicStage_ratio hc.le).const_mul a
  have hsmall := hlim.eventually (eventually_lt_nhds hac)
  filter_upwards [hsmall, eventually_ge_atTop (2 : ℕ)] with q hq hq2
  have hqR : (1 : ℝ) < q := by exact_mod_cast (show 1 < q by omega)
  have hlog : 0 < Real.log (q : ℝ) := Real.log_pos hqR
  have hprod : a * (logarithmicStage c q : ℝ) < ν * Real.log (q : ℝ) := by
    apply (div_lt_iff₀ hlog).mp
    simpa only [mul_div_assoc] using hq
  rw [Real.rpow_def_of_pos (zero_lt_one.trans hqR)]
  apply Real.exp_le_exp.mpr
  nlinarith

/-- The total logarithmic cost of clearing a rational denominator and taking
a bounded-order Cauchy derivative is negative at the logarithmic stage.
The error hypothesis is the actual `o(n^2)` condition. -/
theorem eventually_cleared_jet_exponent_neg
    (degreeRate D a κ : ℝ) (B : ℕ) (error : ℕ → ℝ) {c : ℝ}
    (hc : 0 < c) (hgap : degreeRate / c < κ)
    (herror : Tendsto (fun n : ℕ => error n / (n : ℝ) ^ 2) atTop (𝓝 0)) :
    ∀ᶠ q : ℕ in atTop,
      (degreeRate * (logarithmicStage c q : ℝ) + D) * Real.log (q : ℝ) -
        κ * (logarithmicStage c q : ℝ) ^ 2 + error (logarithmicStage c q) +
        a * (B : ℝ) * (logarithmicStage c q : ℝ) < 0 := by
  have hstage := logarithmicStage_tendsto_atTop hc
  have hr := logarithmicStage_reciprocal_ratio hc
  have hi := inverse_logarithmicStage_tendsto_zero hc
  have he := herror.comp hstage
  let e : ℕ → ℝ := fun q =>
    degreeRate * (Real.log (q : ℝ) / (logarithmicStage c q : ℝ)) +
      D * ((Real.log (q : ℝ) / (logarithmicStage c q : ℝ)) *
        (logarithmicStage c q : ℝ)⁻¹) - κ +
      error (logarithmicStage c q) / (logarithmicStage c q : ℝ) ^ 2 +
      (a * (B : ℝ)) * (logarithmicStage c q : ℝ)⁻¹
  have hlim : Tendsto e atTop (𝓝 (degreeRate / c - κ)) := by
    simpa only [e, Function.comp_def, mul_zero, add_zero, div_eq_mul_inv] using
      ((((hr.const_mul degreeRate).add ((hr.mul hi).const_mul D)).sub tendsto_const_nhds).add he).add
        (hi.const_mul (a * (B : ℝ)))
  have hneg := hlim.eventually (eventually_lt_nhds (sub_neg.mpr hgap))
  filter_upwards [hneg, hstage.eventually (eventually_gt_atTop (0 : ℕ))] with q hq hn
  have hnR : (0 : ℝ) < logarithmicStage c q := by exact_mod_cast hn
  have hid : e q * (logarithmicStage c q : ℝ) ^ 2 =
      (degreeRate * (logarithmicStage c q : ℝ) + D) * Real.log (q : ℝ) -
        κ * (logarithmicStage c q : ℝ) ^ 2 + error (logarithmicStage c q) +
        a * (B : ℝ) * (logarithmicStage c q : ℝ) := by
    dsimp [e]
    field_simp [hnR.ne']
  rw [← hid]
  exact mul_neg_of_neg_of_pos hq (pow_pos hnR 2)

end Zeta3.Transfer

import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.MeasureTheory.Function.SpecialFunctions.Basic
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

/-!
# Differentiating quadratic logarithmic integrals

Uniform domination is proved on a positive neighborhood of the parameter.
These elementary formulas apply both to the angular probability measure
and to the actual positive physical measure.
-/

noncomputable section
namespace Zeta3.Analysis
open MeasureTheory Set Filter Topology

private theorem quadratic_resolvent_bound {u w : ℝ} (hu : 0 < u) (hw : 0 ≤ w) :
    |u/(u^2+w)| ≤ 1/u := by
  rw [abs_of_nonneg (by positivity)]
  calc
    _ ≤ u/u^2 := div_le_div_of_nonneg_left hu.le (sq_pos_of_pos hu) (by linarith)
    _ = _ := by field_simp

private theorem quadratic_resolvent_derivative_bound {u w : ℝ} (hu : 0 < u) (hw : 0 ≤ w) :
    |(w-u^2)/(u^2+w)^2| ≤ 1/u^2 := by
  have hd : 0 < u^2+w := by positivity
  have hab : |w-u^2| ≤ u^2+w := abs_le.mpr ⟨by nlinarith,by nlinarith⟩
  rw [abs_div, abs_of_pos (sq_pos_of_pos hd)]
  calc
    _ ≤ (u^2+w)/(u^2+w)^2 := div_le_div_of_nonneg_right hab (by positivity)
    _ = 1/(u^2+w) := by field_simp
    _ ≤ 1/u^2 := one_div_le_one_div_of_le (sq_pos_of_pos hu) (by linarith)

def quadraticResolvent {α : Type*} [MeasurableSpace α] (μ : Measure α)
    (w : α → ℝ) (u : ℝ) : ℝ := ∫ x, u/(u^2+w x) ∂μ

theorem quadraticResolvent_integrable {α : Type*} [MeasurableSpace α]
    (μ : Measure α) [IsFiniteMeasure μ] (w : α → ℝ) (hw : Measurable w)
    (hn : ∀ᵐ x ∂μ, 0 ≤ w x) {u : ℝ} (hu : 0 < u) :
    Integrable (fun x => u/(u^2+w x)) μ := by
  apply (integrable_const (1/u)).mono' (by apply Measurable.aestronglyMeasurable; fun_prop)
  filter_upwards [hn] with x hx
  simpa only [Real.norm_eq_abs] using quadratic_resolvent_bound hu hx

theorem quadraticLogIntegral_hasDerivAt {α : Type*} [MeasurableSpace α]
    (μ : Measure α) [IsFiniteMeasure μ] (w : α → ℝ) (hw : Measurable w)
    (hn : ∀ᵐ x ∂μ, 0 ≤ w x) {u : ℝ} (hu : 0 < u)
    (hi : Integrable (fun x => Real.log (u^2+w x)) μ) :
    HasDerivAt (fun v => ∫ x, Real.log (v^2+w x) ∂μ) (2*quadraticResolvent μ w u) u := by
  have hs : Ioo (u/2) (3*u/2) ∈ 𝓝 u := Ioo_mem_nhds (by linarith) (by linarith)
  have hd := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := μ) (F := fun v x => Real.log (v^2+w x))
    (F' := fun v x => 2*v/(v^2+w x)) (bound := fun _ => 4/u) hs
    (Eventually.of_forall (fun _ => by apply Measurable.aestronglyMeasurable; fun_prop)) hi
    (by apply Measurable.aestronglyMeasurable; fun_prop)
    (by
      filter_upwards [hn] with x hx
      intro v hv
      have hvpos : 0 < v := by linarith [hv.1]
      have hb := quadratic_resolvent_bound hvpos hx
      have hrec : 2/v ≤ 4/u := by apply (div_le_div_iff₀ hvpos hu).2; linarith [hv.1]
      rw [Real.norm_eq_abs, show 2*v/(v^2+w x)=2*(v/(v^2+w x)) by ring, abs_mul]
      norm_num only [show |(2:ℝ)|=2 by norm_num]
      calc
        _ ≤ 2*(1/v) := mul_le_mul_of_nonneg_left hb (by norm_num)
        _ = 2/v := by ring
        _ ≤ 4/u := hrec)
    (integrable_const _)
    (by
      filter_upwards [hn] with x hx
      intro v hv
      have hvpos : 0 < v := by linarith [hv.1]
      have hh := (((hasDerivAt_id v).pow 2).add_const (w x)).log (by change v^2+w x ≠ 0; positivity)
      simpa only [id_eq, Nat.cast_ofNat, Nat.reduceSub, pow_one, mul_one, Pi.pow_apply] using hh)
  have he : 2*quadraticResolvent μ w u = (∫ x, 2*u/(u^2+w x) ∂μ) := by
    rw [quadraticResolvent, ← integral_const_mul]
    congr 1
    ext x
    ring
  rw [he]
  exact hd.2

theorem quadraticResolvent_hasDerivAt {α : Type*} [MeasurableSpace α]
    (μ : Measure α) [IsFiniteMeasure μ] (w : α → ℝ) (hw : Measurable w)
    (hn : ∀ᵐ x ∂μ, 0 ≤ w x) {u : ℝ} (hu : 0 < u) :
    HasDerivAt (quadraticResolvent μ w)
      (∫ x, (w x-u^2)/(u^2+w x)^2 ∂μ) u := by
  have hs : Ioo (u/2) (3*u/2) ∈ 𝓝 u := Ioo_mem_nhds (by linarith) (by linarith)
  have hd := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := μ) (F := fun v x => v/(v^2+w x))
    (F' := fun v x => (w x-v^2)/(v^2+w x)^2) (bound := fun _ => 4/u^2) hs
    (Eventually.of_forall (fun _ => by apply Measurable.aestronglyMeasurable; fun_prop))
    (quadraticResolvent_integrable μ w hw hn hu)
    (by apply Measurable.aestronglyMeasurable; fun_prop)
    (by
      filter_upwards [hn] with x hx
      intro v hv
      have hvpos : 0 < v := by linarith [hv.1]
      have hb := quadratic_resolvent_derivative_bound hvpos hx
      have hrec : 1/v^2 ≤ 4/u^2 := by
        apply (div_le_div_iff₀ (sq_pos_of_pos hvpos) (sq_pos_of_pos hu)).2
        nlinarith [hv.1]
      simpa only [Real.norm_eq_abs] using hb.trans hrec)
    (integrable_const _)
    (by
      filter_upwards [hn] with x hx
      intro v hv
      have hvpos : 0 < v := by linarith [hv.1]
      have hh := (hasDerivAt_id v).div (((hasDerivAt_id v).pow 2).add_const (w x)) (by change v^2+w x ≠ 0; positivity)
      have he : (1*(v^2+w x)-v*(2*v))/(v^2+w x)^2 = (w x-v^2)/(v^2+w x)^2 := by ring
      simp only [id_eq, Pi.pow_apply, Nat.cast_ofNat, Nat.reduceSub, pow_one, mul_one, he] at hh
      change HasDerivAt (fun t : ℝ => t/(t^2+w x)) ((w x-v^2)/(v^2+w x)^2) v at hh
      exact hh)
  exact hd.2

theorem quadraticResolvent_derivative_integrable {α : Type*} [MeasurableSpace α]
    (μ : Measure α) [IsFiniteMeasure μ] (w : α → ℝ) (hw : Measurable w)
    (hn : ∀ᵐ x ∂μ, 0 ≤ w x) {u : ℝ} (hu : 0 < u) :
    Integrable (fun x => (w x-u^2)/(u^2+w x)^2) μ := by
  apply (integrable_const (1/u^2)).mono' (by apply Measurable.aestronglyMeasurable; fun_prop)
  filter_upwards [hn] with x hx
  simpa only [Real.norm_eq_abs] using quadratic_resolvent_derivative_bound hu hx

theorem quadratic_linear_integral_identity {α : Type*} [MeasurableSpace α]
    (μ : Measure α) [IsFiniteMeasure μ] (w : α → ℝ) (hw : Measurable w)
    (hn : ∀ᵐ x ∂μ, 0 ≤ w x) {u : ℝ} (hu : 0 < u) :
    (∫ x, 2*u^2*w x/(u^2+w x)^2 ∂μ) =
      u*(quadraticResolvent μ w u + u*(∫ x, (w x-u^2)/(u^2+w x)^2 ∂μ)) := by
  rw [quadraticResolvent, ← integral_const_mul,
    ← integral_add (quadraticResolvent_integrable μ w hw hn hu)
      ((quadraticResolvent_derivative_integrable μ w hw hn hu).const_mul u), ← integral_const_mul]
  apply integral_congr_ae
  filter_upwards [hn] with x hx
  have hd : u^2+w x ≠ 0 := by positivity
  field_simp
  ring

end Zeta3.Analysis

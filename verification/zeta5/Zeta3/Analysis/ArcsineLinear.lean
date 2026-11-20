import Zeta3.Analysis.QuadraticResolvent
import Zeta3.Analysis.ImaginaryPotential
import Zeta3.Analysis.ContourLinear

/-!
# The exact angular linear-deficit coefficient

Two rigorously dominated differentiations of the actual arcsine logarithmic
integral identify its rational angular coefficient with `physicalLinearKernel`.
-/

noncomputable section
namespace Zeta3.Analysis
open MeasureTheory Set Filter Topology

private theorem gammaRadical_left_hasDerivAt {u b : ℝ} (hu : 0 < u) :
    HasDerivAt (fun v => gammaRadical v b) (u/gammaRadical u b) u := by
  have hh := (((hasDerivAt_id u).pow 2).add_const (b^2)).sqrt (by
    change u^2+b^2 ≠ 0
    positivity)
  convert hh using 1 <;> (try simp only [id_eq, Pi.pow_apply, Nat.cast_ofNat, Nat.reduceSub, pow_one, mul_one])
  · rfl
  · unfold gammaRadical
    ring

theorem imaginaryArcsineValue_left_hasDerivAt {u b : ℝ} (hu : 0 < u) :
    HasDerivAt (fun v => imaginaryArcsineValue v b) (1/gammaRadical u b) u := by
  have hR := gammaRadical_pos (b := b) hu
  have hh := (((hasDerivAt_id u).add (gammaRadical_left_hasDerivAt hu)).div_const 2).log (by
    change (u+gammaRadical u b)/2 ≠ 0
    positivity)
  convert hh using 1 <;> (try simp only [id_eq, Pi.add_apply])
  · rfl
  · field_simp
    ring

theorem angular_log_quadratic_integrable {u : ℝ} (hu : 0 < u) (b : ℝ) :
    Integrable (fun θ => Real.log (u^2+(b*Real.cos θ)^2)) Zeta5.Analysis.angleMeasure := by
  have hc : Continuous (fun θ => Real.log (u^2+(b*Real.cos θ)^2)) := by
    apply Continuous.log (by fun_prop)
    intro θ
    positivity
  unfold Zeta5.Analysis.angleMeasure
  exact (hc.integrableOn_Icc (a := 0) (b := Real.pi)).mono_set Ioc_subset_Icc_self |>.smul_measure ENNReal.ofReal_ne_top

theorem angular_quadraticResolvent_eq {u b : ℝ} (hu : 0 < u) (hb : 0 < b) :
    quadraticResolvent Zeta5.Analysis.angleMeasure (fun θ => (b*Real.cos θ)^2) u =
      1/gammaRadical u b := by
  have hd := quadraticLogIntegral_hasDerivAt Zeta5.Analysis.angleMeasure
    (fun θ => (b*Real.cos θ)^2) (by fun_prop)
    (Eventually.of_forall (fun θ => sq_nonneg _)) hu (angular_log_quadratic_integrable hu b)
  have he : (fun v => ∫ θ, Real.log (v^2+(b*Real.cos θ)^2) ∂Zeta5.Analysis.angleMeasure) =ᶠ[𝓝 u]
      (fun v => 2*imaginaryArcsineValue v b) := by
    filter_upwards [Ioi_mem_nhds hu] with v hv
    exact integral_angle_log_quadratic hb hv
  have hother := ((imaginaryArcsineValue_left_hasDerivAt (b := b) hu).const_mul 2).congr_of_eventuallyEq he
  have h := hd.unique hother
  linarith

theorem angular_quadraticResolvent_derivative_eq {u b : ℝ} (hu : 0 < u) (hb : 0 < b) :
    (∫ θ, ((b*Real.cos θ)^2-u^2)/(u^2+(b*Real.cos θ)^2)^2 ∂Zeta5.Analysis.angleMeasure) =
      -u/gammaRadical u b^3 := by
  have hR := gammaRadical_pos (b := b) hu
  have hd := quadraticResolvent_hasDerivAt Zeta5.Analysis.angleMeasure
    (fun θ => (b*Real.cos θ)^2) (by fun_prop)
    (Eventually.of_forall (fun θ => sq_nonneg _)) hu
  have hother : HasDerivAt (fun v => 1/gammaRadical v b) (-u/gammaRadical u b^3) u := by
    have hh := (hasDerivAt_const u (1:ℝ)).div (gammaRadical_left_hasDerivAt hu) hR.ne'
    convert hh using 1 <;> (try simp only [zero_mul, one_mul, zero_sub]) <;> first | rfl | (field_simp <;> ring)
  have he : quadraticResolvent Zeta5.Analysis.angleMeasure (fun θ => (b*Real.cos θ)^2) =ᶠ[𝓝 u]
      (fun v => 1/gammaRadical v b) := by
    filter_upwards [Ioi_mem_nhds hu] with v hv
    exact angular_quadraticResolvent_eq hv hb
  exact hd.unique (hother.congr_of_eventuallyEq he)

theorem integral_angle_linear_kernel {u b : ℝ} (hu : 0 < u) (hb : 0 ≤ b) :
    (∫ θ, 2*u^2*(b*Real.cos θ)^2/(u^2+(b*Real.cos θ)^2)^2 ∂Zeta5.Analysis.angleMeasure) =
      physicalLinearKernel u b := by
  rcases hb.eq_or_lt with rfl | hb
  · simp [physicalLinearKernel]
  have h := quadratic_linear_integral_identity Zeta5.Analysis.angleMeasure
    (fun θ => (b*Real.cos θ)^2) (by fun_prop)
    (Eventually.of_forall (fun θ => sq_nonneg _)) hu
  rw [angular_quadraticResolvent_eq hu hb, angular_quadraticResolvent_derivative_eq hu hb] at h
  rw [h]
  unfold physicalLinearKernel
  have hR := gammaRadical_pos (b := b) hu
  have hsq := gammaRadical_sq u b
  field_simp
  nlinarith

end Zeta3.Analysis

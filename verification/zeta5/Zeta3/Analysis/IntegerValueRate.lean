import Zeta3.Analysis.DeterminantRate
import Zeta3.Analysis.ConcreteResponse
import Zeta3.Transfer.Cauchy

/-!
# From the actual normalizer to decay of the actual integer polynomial

The arithmetic rate is an explicit mathematical hypothesis in this assembly
lemma, not part of an external finite numerical certificate.
-/

noncomputable section
namespace Zeta3.Analysis
open Filter Polynomial Zeta3.Construction Zeta3.Transfer
open scoped Topology

theorem windowIntegerPolynomial_norm_realZetaThree (n : ℕ) :
    ‖(windowIntegerPolynomial n).eval₂ (Int.castRingHom ℂ) (Zeta5.Endpoint.realZeta 3 : ℂ)‖ =
      (windowNormalizer n : ℝ)*windowValue n := by
  rw [eval_int_complex_ofReal,Complex.norm_real,Real.norm_eq_abs,
    windowIntegerPolynomial_eval_real]
  change |(windowNormalizer n:ℝ)*windowValue n| = _
  rw [abs_of_pos (mul_pos (by exact_mod_cast windowNormalizer_pos n) (windowValue_pos n))]

theorem exists_certified_integer_rate_error
    (hfinite : Zeta3.Certificate.AnalyticFiniteEvidence) {C_ar : ℝ}
    (harithmetic : ∃ E : ℕ → ℝ,
      Tendsto (fun n => E n/windowScale n) atTop (𝓝 0) ∧
      (∀ᶠ n in atTop, Real.log (windowNormalizer n:ℝ) ≤ C_ar*windowScale n+E n)) :
    ∃ E : ℕ → ℝ, Tendsto (fun n => E n/windowScale n) atTop (𝓝 0) ∧
      (∀ᶠ n in atTop,
        ‖(windowIntegerPolynomial n).eval₂ (Int.castRingHom ℂ) (Zeta5.Endpoint.realZeta 3 : ℂ)‖ ≤
          Real.exp (-(Zeta3.Parameters.analyticLower-C_ar)*windowScale n+E n)) := by
  obtain ⟨E_an,hE_an,han⟩ := exists_certified_analytic_rate_error hfinite
  obtain ⟨E_ar,hE_ar,har⟩ := harithmetic
  refine ⟨fun n => E_an n+E_ar n,?_,?_⟩
  · simpa only [add_div,add_zero] using hE_an.add hE_ar
  · filter_upwards [han,har] with n hn hr
    rw [windowIntegerPolynomial_norm_realZetaThree]
    have hM : (0:ℝ)<windowNormalizer n := by exact_mod_cast windowNormalizer_pos n
    have hV := windowValue_pos n
    have hlog : Real.log ((windowNormalizer n:ℝ)*windowValue n) ≤
        -(Zeta3.Parameters.analyticLower-C_ar)*windowScale n+(E_an n+E_ar n) := by
      rw [Real.log_mul hM.ne' hV.ne']
      linarith
    have he := Real.exp_le_exp.mpr hlog
    rwa [Real.exp_log (mul_pos hM hV)] at he

theorem quadratic_error_rescale {E : ℕ → ℝ}
    (hE : Tendsto (fun n => E n/windowScale n) atTop (𝓝 0)) :
    Tendsto (fun n => E n/(n:ℝ)^2) atTop (𝓝 0) := by
  have h := hE.const_mul 2500
  simp only [mul_zero] at h
  apply h.congr'
  filter_upwards [eventually_gt_atTop (0:ℕ)] with n hn
  have hnR : (n:ℝ)≠0 := by exact_mod_cast hn.ne'
  unfold windowScale
  field_simp
  ring

end Zeta3.Analysis

import Zeta3.Analysis.ComplexPotentialHarmonic
import Zeta3.Analysis.ComplexPotentialInfinity
import Zeta3.Analysis.ContourMaximum
import Mathlib.Analysis.Calculus.Deriv.Polynomial

/-!
# Polynomial comparison for a genuine compactly supported measure

Continuity, harmonicity and decay at infinity are proved for the actual
logarithmic potential. Thus the only boundary input below is the finite
weighted real-axis estimate, not an unproved maximum-principle hypothesis.
-/

noncomputable section
namespace Zeta3.Analysis
open MeasureTheory Set Filter Metric InnerProductSpace

theorem polynomial_weighted_le (μ : Measure ℝ) [IsFiniteMeasure μ]
    {B C N M : ℝ} (hB : 0 ≤ B) (hC : 0 ≤ C) (hN : 0 ≤ N) (hM : 0 ≤ M)
    (hsupport : ∀ᵐ w ∂μ, w ∈ Icc 0 B)
    (hsmall : ∀ (v ρ : ℝ), 0 < ρ →
      μ {w : ℝ | |v-w| < ρ^4} ≤ ENNReal.ofReal (C*ρ))
    (m : ℕ) (hmass : N*μ.real univ = m)
    (p : Polynomial ℂ) (hdeg : p.natDegree < m)
    (hboundary : ∀ x ∈ Icc 0 B,
      ‖p.eval (x:ℂ)‖ * Real.exp (-N*complexLogPotential μ (x:ℂ)) ≤ M)
    (z : ℂ) : ‖p.eval z‖ * Real.exp (-N*complexLogPotential μ z) ≤ M := by
  have hcont := (complexLogPotential_continuous μ hsupport hC hsmall).const_mul N
  have hharm := (complexLogPotential_harmonicOnNhd μ hsupport hC hsmall).const_smul (c := N)
  have hzero := weighted_polynomial_tendsto_zero μ hB hN hsupport
    (fun z => (complexLog_integrable_and_truncation_error μ hsupport hC
      (by norm_num : (0:ℝ)<1) hsmall z).1) m hmass p hdeg
  apply le_of_forall_pos_le_add
  intro ε hε
  have hw := weighted_norm_le_of_tendsto_zero p.eval (fun z => N*complexLogPotential μ z)
    (isCompact_Icc.image Complex.continuous_ofReal).isClosed p.differentiable.continuous hcont
    (fun x _ => p.differentiable.analyticAt x) hharm (M+ε) (by positivity)
    (by
      rintro _ ⟨x,hx,rfl⟩
      simpa only [neg_mul] using (hboundary x hx).trans (le_add_of_nonneg_right hε.le))
    (by simpa only [neg_mul] using hzero) z
  simpa only [neg_mul] using hw

end Zeta3.Analysis

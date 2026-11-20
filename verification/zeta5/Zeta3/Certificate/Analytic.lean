import Zeta3.Parameters
import Zeta3.Analysis.PhysicalProfile
import Zeta3.Analysis.FiniteGrid

/-!
# The finite analytic-certificate interface

`AnalyticFiniteEvidence` is an explicit hypothesis about one finite sum of
the actual formula at the actual inverse endpoints. It is not a hypothesis
about an integral, a determinant, or an asymptotic estimate. Arb checks this
finite assertion through root brackets and directed elementary operations.
The passage from that finite assertion to the integral bound is proved here.

No instance of this evidence is postulated as an axiom in this stage.
-/

namespace Zeta3.Certificate
open Zeta3.Analysis Zeta3.Parameters MeasureTheory Set
open scoped BigOperators
noncomputable section

def saving (v : ℝ) : ℝ :=
  physicalSaving s₁ s₂ windows_positive.1 windows_positive.2.1 v

def endpoint (v : ℝ) : ℝ :=
  physicalEndpoint s₁ s₂ windows_positive.1 windows_positive.2.1 v

def analyticIntegral : ℝ := ∫ v in 0..δ, saving v

def analyticPanels : ℕ := 8192
def analyticStep : ℝ := δ / (analyticPanels : ℝ)

/-- Exactly the left sum in the external replay, before its rational lower
rounding. -/
def analyticFiniteSum : ℝ := analyticStep * ∑ i ∈ Finset.range analyticPanels,
  physicalSavingFormula s₁ s₂ (endpoint (analyticStep * (i : ℝ))) (analyticStep * (i : ℝ))

structure AnalyticFiniteEvidence : Prop where
  finite_sum_lower : analyticLower ≤ analyticFiniteSum

theorem saving_strictMonoOn : StrictMonoOn saving (Ici 0) :=
  physicalSaving_strictMonoOn s₁ s₂ windows_positive.1 windows_positive.2.1
    (by norm_num [s₁])

theorem analyticStep_nonneg : 0 ≤ analyticStep := by
  norm_num [analyticStep, analyticPanels, δ]

theorem analyticStep_mul_panels : analyticStep * (analyticPanels : ℝ) = δ := by
  norm_num [analyticStep, analyticPanels]

theorem analyticFiniteSum_le_integral : analyticFiniteSum ≤ analyticIntegral := by
  have hm : MonotoneOn saving (Icc 0 (analyticStep * (analyticPanels : ℝ))) :=
    saving_strictMonoOn.monotoneOn.mono (fun _ hx => hx.1)
  have hs := left_sum_le_integral_of_monotoneOn saving analyticStep_nonneg analyticPanels hm
  rw [analyticStep_mul_panels] at hs
  have he : analyticFiniteSum =
      analyticStep * ∑ i ∈ Finset.range analyticPanels, saving (analyticStep * (i : ℝ)) := by
    unfold analyticFiniteSum
    apply congrArg (fun x : ℝ => analyticStep * x)
    apply Finset.sum_congr rfl
    intro i _
    exact (physicalSaving_eq_formula s₁ s₂ windows_positive.1 windows_positive.2.1
      (mul_nonneg analyticStep_nonneg (Nat.cast_nonneg i))).symm
  rw [he]
  exact hs

theorem analyticLower_le_integral (h : AnalyticFiniteEvidence) :
    analyticLower ≤ analyticIntegral :=
  h.finite_sum_lower.trans analyticFiniteSum_le_integral

end
end Zeta3.Certificate

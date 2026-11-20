import Zeta3.Analysis.PhysicalProfile
import Zeta5.Analysis.RiemannWeight

/-! # The exact endpoint error of the physical saving grid -/

noncomputable section
namespace Zeta3.Analysis
open Real Set MeasureTheory Filter Finset
open scoped Topology BigOperators

theorem physicalSaving_grid_lower (s₁ s₂ : ℝ) (h₁ : 0 < s₁) (h₂ : 0 < s₂)
    (h₁one : s₁ ≤ 1) {N : ℝ} (hN : 0 < N) (r : ℕ) :
    N * (∫ v in 0..((r : ℝ) / N), physicalSaving s₁ s₂ h₁ h₂ v) -
        physicalSaving s₁ s₂ h₁ h₂ ((r : ℝ) / N) + physicalSaving s₁ s₂ h₁ h₂ 0 ≤
      ∑ k ∈ range r, physicalSaving s₁ s₂ h₁ h₂ ((k : ℝ) / N) := by
  let f : ℝ → ℝ := fun v => physicalSaving s₁ s₂ h₁ h₂ (max 0 v)
  have hf : Continuous f :=
    (physicalSaving_continuousOn s₁ s₂ h₁ h₂).comp_continuous
      (continuous_const.max continuous_id) (fun v => le_max_left 0 v)
  have hmono : MonotoneOn f (Ici 0) := by
    intro a ha b hb hab
    dsimp [f]
    rw [max_eq_right ha, max_eq_right hb]
    exact (physicalSaving_strictMonoOn s₁ s₂ h₁ h₂ h₁one).monotoneOn ha hb hab
  have hgrid := (Zeta5.Analysis.monotone_grid_integral_bounds f hf hmono hN r).2
  have hint : (∫ v in 0..((r : ℝ) / N), f v) =
      ∫ v in 0..((r : ℝ) / N), physicalSaving s₁ s₂ h₁ h₂ v := by
    apply intervalIntegral.integral_congr
    intro v hv
    rw [Set.uIcc_of_le (by positivity)] at hv
    dsimp [f]
    rw [max_eq_right hv.1]
  have hval (k : ℕ) : f ((k : ℝ) / N) = physicalSaving s₁ s₂ h₁ h₂ ((k : ℝ) / N) := by
    dsimp [f]
    rw [max_eq_right (by positivity)]
  rw [hint] at hgrid
  simp only [hval] at hgrid
  have htel := Finset.sum_range_sub
    (fun k : ℕ => physicalSaving s₁ s₂ h₁ h₂ ((k : ℝ) / N)) r
  rw [Finset.sum_sub_distrib] at htel
  simp only [Nat.cast_zero, zero_div] at htel
  linarith

end Zeta3.Analysis

import Zeta3.Analysis.CubicDensity
import Zeta3.Construction.Functional
import Zeta5.Analysis.PhysicalMeasureMoments

/-! # Exact cubic Bernoulli moments of the actual positive density -/

noncomputable section
namespace Zeta3.Analysis.PhysicalMeasure
open Real Set MeasureTheory Filter Polynomial
open scoped Topology BigOperators

theorem density_moment (k : ℕ) :
    (∫ x : ℝ in Ioi 0, x ^ (2 * k) * density x) =
      (Zeta3.Construction.rationalMoment k : ℝ) := by
  rw [density_moment_zeta, Zeta5.Analysis.PhysicalMeasure.evenZeta_series]
  have hp : (2 * Real.pi) ^ (2 * k + 2) ≠ 0 := by positivity
  have hf : (Nat.factorial (2 * k + 2) : ℝ) ≠ 0 := by positivity
  have hfac : (Nat.factorial (2 * k + 3) : ℝ) =
      (2 * (k : ℝ) + 3) * (Nat.factorial (2 * k + 2) : ℝ) := by
    rw [show 2 * k + 3 = (2 * k + 2) + 1 by omega, Nat.factorial_succ]
    push_cast
    ring
  unfold momentFactor Zeta3.Construction.rationalMoment
  push_cast
  rw [hfac]
  field_simp
  <;> ring

theorem density_mass : (∫ x : ℝ in Ioi 0, density x) = 1 / 4 := by
  have h := density_moment 0
  norm_num [Zeta3.Construction.rationalMoment, _root_.bernoulli] at h ⊢
  exact h

end Zeta3.Analysis.PhysicalMeasure

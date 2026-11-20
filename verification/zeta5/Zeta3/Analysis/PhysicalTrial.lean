import Zeta3.Analysis.PhysicalEquilibrium
import Zeta5.Analysis.PotentialTail

/-!
# Uniform two-window trial polynomials and an integrable tail

The two one-window masses at a common endpoint are each at most twice the
two-window mass. Averaging their proved potential-defect estimates yields a
uniform tail for the genuine two-window potential. Together with its own
quantile polynomial this gives the analytic trial family needed for norms.
-/

namespace Zeta3.Analysis
noncomputable section

def physicalTailThreshold (s₁ s₂ δ : ℝ) : ℝ :=
  max (Zeta5.Analysis.tailThreshold s₁ (2 * δ)) (Zeta5.Analysis.tailThreshold s₂ (2 * δ))

theorem physicalPotential_zero_support (s₁ s₂ : ℝ) (h₁ : 0 < s₁) (h₂ : 0 < s₂)
    {y : ℝ} (hy : 0 ≤ y) : physicalPotential s₁ s₂ h₁ h₂ 0 y = 0 := by
  simp only [physicalPotential, Zeta5.Analysis.auxiliaryPotential_zero_support s₁ h₁ hy,
    Zeta5.Analysis.auxiliaryPotential_zero_support s₂ h₂ hy, zero_add, zero_div]

theorem uniform_physical_trial_polynomial (s₁ s₂ : ℝ) (h₁ : 0 < s₁) (h₂ : 0 < s₂)
    (h₁one : s₁ ≤ 1) {δ N : ℝ} (hδ : 0 ≤ δ) (hN : 1 ≤ N)
    (n : ℕ) (hnδ : (n : ℝ) / N ≤ δ) :
    ∃ p : Polynomial ℝ, p.Monic ∧ p.natDegree = n ∧ ∀ y : ℝ, 0 ≤ y →
      |p.eval (N ^ 2 * y ^ 2)| ^ 2 ≤ Zeta5.Analysis.trialPrefactor (2 * δ) * N ^ (4 * n + 16) *
        Real.exp (4 * N * physicalPotential s₁ s₂ h₁ h₂
          (physicalEndpoint s₁ s₂ h₁ h₂ ((n : ℝ) / N)) y) := by
  have hNpos : 0 < N := lt_of_lt_of_le zero_lt_one hN
  have hu : 0 ≤ (n : ℝ) / N := by positivity
  have hb := physicalEndpoint_nonneg s₁ s₂ h₁ h₂ ((n : ℝ) / N)
  have hbB : physicalEndpoint s₁ s₂ h₁ h₂ ((n : ℝ) / N) ≤ 2 * δ :=
    (physicalEndpoint_le_twice s₁ s₂ h₁ h₂ h₁one hu).trans (by linarith)
  rcases n.eq_zero_or_pos with rfl | hn
  · refine ⟨1, Polynomial.monic_one, Polynomial.natDegree_one, ?_⟩
    intro y hy
    simp only [Nat.cast_zero, zero_div, physicalEndpoint_zero,
      physicalPotential_zero_support s₁ s₂ h₁ h₂ hy, mul_zero, Real.exp_zero, mul_one,
      Polynomial.eval_one, abs_one, one_pow, Nat.mul_zero, zero_add]
    exact one_le_mul_of_one_le_of_one_le (Zeta5.Analysis.trialPrefactor_one_le (by positivity))
      (one_le_pow₀ hN)
  · obtain ⟨p, hpm, hpd, hp⟩ := physicalPotential_trial_polynomial s₁ s₂ h₁ h₂ hb hN n hn
      (physicalMass_endpoint s₁ s₂ h₁ h₂ hu)
    refine ⟨p, hpm, hpd, ?_⟩
    intro y _
    apply (hp y).trans
    change Zeta5.Analysis.trialPrefactor (physicalEndpoint s₁ s₂ h₁ h₂ ((n : ℝ) / N)) *
      N ^ (4 * n + 16) * _ ≤ _
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (Zeta5.Analysis.trialPrefactor_mono hb hbB) (by positivity))
      (Real.exp_pos _).le

theorem physicalPotential_equilibrium_decay (s₁ s₂ : ℝ)
    (h₁ : 0 < s₁) (h₂ : 0 < s₂) {δ b y : ℝ}
    (hδ : 0 ≤ δ) (hb : 0 ≤ b) (hmass : physicalMass s₁ s₂ b ≤ δ) (hy : 0 ≤ y) :
    4 * physicalPotential s₁ s₂ h₁ h₂ b y - physicalField s₁ s₂ y ≤
      physicalEquilibriumAtEndpoint s₁ s₂ h₁ h₂ b -
        (Real.pi / 2) * max 0 (y - physicalTailThreshold s₁ s₂ δ) := by
  have hm₁ := Zeta5.Analysis.profileMass_nonneg h₁ hb
  have hm₂ := Zeta5.Analysis.profileMass_nonneg h₂ hb
  have hm := hmass
  rw [physicalMass_eq_average] at hm
  have hm₁u : Zeta5.Analysis.profileMass s₁ b ≤ 2 * δ := by linarith
  have hm₂u : Zeta5.Analysis.profileMass s₂ b ≤ 2 * δ := by linarith
  have hb₁ : b ≤ s₁ + 2 * δ := by
    have h := Zeta5.Analysis.profileEndpoint_le_shifted_mass s₁ h₁ hm₁
    rw [Zeta5.Analysis.profileEndpoint_mass s₁ h₁ hb] at h
    linarith
  have hb₂ : b ≤ s₂ + 2 * δ := by
    have h := Zeta5.Analysis.profileEndpoint_le_shifted_mass s₂ h₂ hm₂
    rw [Zeta5.Analysis.profileEndpoint_mass s₂ h₂ hb] at h
    linarith
  have he₁ := Zeta5.Analysis.auxiliaryPotential_equilibrium_decay s₁ h₁
    (show 0 ≤ 2 * δ by positivity) hb hb₁ hm₁u hy
  have he₂ := Zeta5.Analysis.auxiliaryPotential_equilibrium_decay s₂ h₂
    (show 0 ≤ 2 * δ by positivity) hb hb₂ hm₂u hy
  have hx₁ : max 0 (y - physicalTailThreshold s₁ s₂ δ) ≤
      max 0 (y - Zeta5.Analysis.tailThreshold s₁ (2 * δ)) := by
    apply max_le_max_left
    exact sub_le_sub_left (le_max_left _ _) y
  have hx₂ : max 0 (y - physicalTailThreshold s₁ s₂ δ) ≤
      max 0 (y - Zeta5.Analysis.tailThreshold s₂ (2 * δ)) := by
    apply max_le_max_left
    exact sub_le_sub_left (le_max_right _ _) y
  have hp₁ := mul_le_mul_of_nonneg_left hx₁ (show 0 ≤ Real.pi / 2 by positivity)
  have hp₂ := mul_le_mul_of_nonneg_left hx₂ (show 0 ≤ Real.pi / 2 by positivity)
  rw [physicalField_eq_average]
  unfold physicalPotential physicalEquilibriumAtEndpoint
  linarith

theorem uniform_physical_trial_polynomial_decay (s₁ s₂ : ℝ)
    (h₁ : 0 < s₁) (h₂ : 0 < s₂) (h₁one : s₁ ≤ 1) {δ N : ℝ}
    (hδ : 0 ≤ δ) (hN : 1 ≤ N) (n : ℕ) (hnδ : (n : ℝ) / N ≤ δ) :
    ∃ p : Polynomial ℝ, p.Monic ∧ p.natDegree = n ∧ ∀ y : ℝ, 0 ≤ y →
      |p.eval (N ^ 2 * y ^ 2)| ^ 2 * Real.exp (-N * physicalField s₁ s₂ y) ≤
        Zeta5.Analysis.trialPrefactor (2 * δ) * N ^ (4 * n + 16) *
          Real.exp (N * physicalEquilibrium s₁ s₂ h₁ h₂ ((n : ℝ) / N)) *
          Real.exp (-(Real.pi / 2) * N * max 0 (y - physicalTailThreshold s₁ s₂ δ)) := by
  have hNpos : 0 < N := lt_of_lt_of_le zero_lt_one hN
  have hu : 0 ≤ (n : ℝ) / N := by positivity
  have hb := physicalEndpoint_nonneg s₁ s₂ h₁ h₂ ((n : ℝ) / N)
  obtain ⟨p, hpm, hpd, hp⟩ := uniform_physical_trial_polynomial s₁ s₂ h₁ h₂ h₁one hδ hN n hnδ
  refine ⟨p, hpm, hpd, ?_⟩
  intro y hy
  have hd := physicalPotential_equilibrium_decay s₁ s₂ h₁ h₂ hδ hb
    (by simpa only [physicalMass_endpoint s₁ s₂ h₁ h₂ hu] using hnδ) hy
  change _ ≤ physicalEquilibrium s₁ s₂ h₁ h₂ ((n : ℝ) / N) - _ at hd
  calc
    _ ≤ (Zeta5.Analysis.trialPrefactor (2 * δ) * N ^ (4 * n + 16) *
        Real.exp (4 * N * physicalPotential s₁ s₂ h₁ h₂
          (physicalEndpoint s₁ s₂ h₁ h₂ ((n : ℝ) / N)) y)) *
        Real.exp (-N * physicalField s₁ s₂ y) :=
      mul_le_mul_of_nonneg_right (hp y hy) (Real.exp_pos _).le
    _ = Zeta5.Analysis.trialPrefactor (2 * δ) * N ^ (4 * n + 16) *
        Real.exp (N * (4 * physicalPotential s₁ s₂ h₁ h₂
          (physicalEndpoint s₁ s₂ h₁ h₂ ((n : ℝ) / N)) y - physicalField s₁ s₂ y)) := by
      rw [mul_assoc, ← Real.exp_add]
      congr 2
      ring
    _ ≤ Zeta5.Analysis.trialPrefactor (2 * δ) * N ^ (4 * n + 16) *
        Real.exp (N * (physicalEquilibrium s₁ s₂ h₁ h₂ ((n : ℝ) / N) -
          (Real.pi / 2) * max 0 (y - physicalTailThreshold s₁ s₂ δ))) :=
      mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr
        (mul_le_mul_of_nonneg_left hd hNpos.le))
        (mul_nonneg (Zeta5.Analysis.trialPrefactor_pos _).le (by positivity))
    _ = _ := by
      rw [show N * (physicalEquilibrium s₁ s₂ h₁ h₂ ((n : ℝ) / N) -
          (Real.pi / 2) * max 0 (y - physicalTailThreshold s₁ s₂ δ)) =
          N * physicalEquilibrium s₁ s₂ h₁ h₂ ((n : ℝ) / N) +
            (-(Real.pi / 2) * N * max 0 (y - physicalTailThreshold s₁ s₂ δ)) by ring,
        Real.exp_add]
      ring

end
end Zeta3.Analysis

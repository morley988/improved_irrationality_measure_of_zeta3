import Zeta3.Analysis.PhysicalNorm
import Zeta5.Analysis.PhysicalNormTrial

/-! # Uniform actual norm bounds from the constructive potential trial -/

noncomputable section
namespace Zeta3.Analysis
open Real Set MeasureTheory Filter Polynomial
open scoped Topology BigOperators

def normEnvelope (y : ℝ) : ℝ := (1 + y ^ 3) * Real.exp (-(Real.pi / 2) * y)

def normEnvelopeMass : ℝ := 1 / (Real.pi / 2) + 6 / (Real.pi / 2) ^ 4

theorem normEnvelope_integrable : IntegrableOn normEnvelope (Ioi 0) := by
  have h0 : IntegrableOn (fun y : ℝ => Real.exp (-(Real.pi / 2) * y)) (Ioi 0) := by
    simpa only [pow_zero, one_mul, neg_mul] using
      Zeta5.Analysis.PhysicalMeasure.integrableOn_pow_mul_exp_neg_mul 0
        (by positivity : (0 : ℝ) < Real.pi / 2)
  have h3 : IntegrableOn (fun y : ℝ => y ^ 3 * Real.exp (-(Real.pi / 2) * y)) (Ioi 0) := by
    simpa only [neg_mul] using
      Zeta5.Analysis.PhysicalMeasure.integrableOn_pow_mul_exp_neg_mul 3
        (by positivity : (0 : ℝ) < Real.pi / 2)
  unfold normEnvelope
  simp only [add_mul, one_mul]
  exact h0.add h3

theorem normEnvelope_integral : (∫ y : ℝ in Ioi 0, normEnvelope y) = normEnvelopeMass := by
  unfold normEnvelope
  simp only [add_mul, one_mul]
  have h0 : IntegrableOn (fun y : ℝ => Real.exp (-(Real.pi / 2) * y)) (Ioi 0) := by
    simpa only [pow_zero, one_mul, neg_mul] using Zeta5.Analysis.PhysicalMeasure.integrableOn_pow_mul_exp_neg_mul 0
      (by positivity : (0 : ℝ) < Real.pi / 2)
  have h3 : IntegrableOn (fun y : ℝ => y ^ 3 * Real.exp (-(Real.pi / 2) * y)) (Ioi 0) := by
    simpa only [neg_mul] using Zeta5.Analysis.PhysicalMeasure.integrableOn_pow_mul_exp_neg_mul 3
      (by positivity : (0 : ℝ) < Real.pi / 2)
  rw [integral_add h0 h3]
  have hv0 := Zeta5.Analysis.PhysicalMeasure.integral_pow_mul_exp_neg_mul 0
    (by positivity : (0 : ℝ) < Real.pi / 2)
  have hv5 := Zeta5.Analysis.PhysicalMeasure.integral_pow_mul_exp_neg_mul 3
    (by positivity : (0 : ℝ) < Real.pi / 2)
  norm_num only [Nat.factorial, Nat.cast_ofNat, Nat.cast_mul, Nat.cast_one,
    Nat.reduceAdd, Nat.reduceMul, Nat.succ_eq_add_one, pow_zero, one_mul, zero_add,
    pow_one] at hv0 hv5
  simpa only [normEnvelopeMass, neg_mul] using congrArg₂ (· + ·) hv0 hv5


theorem normEnvelopeMass_pos : 0 < normEnvelopeMass := by unfold normEnvelopeMass; positivity

theorem windowSquaredNorm_scaled (N m₁ m₂ : ℕ) (hN : 0 < N) (P : ℝ[X]) :
    windowSquaredNorm N m₁ m₂ P = (N : ℝ) * ∫ y : ℝ in Ioi 0,
      P.eval ((N : ℝ) ^ 2 * y ^ 2) ^ 2 * physicalCommonWeight N m₁ m₂ ((N : ℝ) * y) := by
  have h := integral_comp_mul_left_Ioi'
    (fun x : ℝ => P.eval (x ^ 2) ^ 2 * physicalCommonWeight N m₁ m₂ x) 0
    (by exact_mod_cast hN : (0 : ℝ) < N)
  simpa only [windowSquaredNorm_integral, mul_zero, smul_eq_mul, mul_pow] using h.symm

/-- A single positive constant controls every degree in a fixed mass window.
The exponent 20 records only polynomial errors and disappears on the N² scale. -/
theorem exists_uniform_windowSquaredNorm_bound (s₁ s₂ : ℝ) (h₁ : 0 < s₁) (h₂ : 0 < s₂)
    (h₁one : s₁ ≤ 1) (δ : ℝ) (hδ : 0 ≤ δ) :
    ∃ K : ℝ, 0 < K ∧ ∀ N m₁ m₂ k : ℕ, 0 < N → (m₁ : ℝ) / N = s₁ → (m₂ : ℝ) / N = s₂ → (k : ℝ) / N ≤ δ →
      ∃ P : ℝ[X], P.Monic ∧ P.natDegree = k ∧
        windowSquaredNorm N m₁ m₂ P ≤ K * physicalWeightScale N m₁ m₂ * (N : ℝ) ^ (4 * k + 20) *
          Real.exp ((N : ℝ) * physicalEquilibrium s₁ s₂ h₁ h₂ ((k : ℝ) / N)) := by
  obtain ⟨C, hC, hdensity⟩ := PhysicalMeasure.exists_density_exponential_bound
  let K : ℝ := C * Zeta5.Analysis.trialPrefactor (2 * δ) * Real.exp ((Real.pi / 2) * physicalTailThreshold s₁ s₂ δ) *
    normEnvelopeMass
  have hK : 0 < K := by dsimp [K]; exact mul_pos (mul_pos (mul_pos hC
    (Zeta5.Analysis.trialPrefactor_pos _)) (Real.exp_pos _)) normEnvelopeMass_pos
  refine ⟨K, hK, ?_⟩
  intro N m₁ m₂ k hN hms₁ hms₂ hkδ
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  obtain ⟨P, hPm, hPk, hP⟩ := uniform_physical_trial_polynomial_decay s₁ s₂ h₁ h₂ h₁one hδ hN1 k hkδ
  refine ⟨P, hPm, hPk, ?_⟩
  let A : ℝ := C * (N : ℝ) ^ 3 * physicalWeightScale N m₁ m₂ *
    (Zeta5.Analysis.trialPrefactor (2 * δ) * (N : ℝ) ^ (4 * k + 16) *
      Real.exp ((N : ℝ) * physicalEquilibrium s₁ s₂ h₁ h₂ ((k : ℝ) / N))) *
    Real.exp ((Real.pi / 2) * physicalTailThreshold s₁ s₂ δ)
  have hW : 0 < physicalWeightScale N m₁ m₂ := physicalWeightScale_pos hN m₁ m₂
  have hT : 0 < Zeta5.Analysis.trialPrefactor (2 * δ) := Zeta5.Analysis.trialPrefactor_pos _
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hpoint {y : ℝ} (hy : 0 < y) :
      P.eval ((N : ℝ) ^ 2 * y ^ 2) ^ 2 * physicalCommonWeight N m₁ m₂ ((N : ℝ) * y) ≤
        A * normEnvelope y := by
    have hw := physicalCommonWeight_scaled_bound hC hdensity N m₁ m₂ hN hy
    rw [hms₁, hms₂] at hw
    have htrial := hP y hy.le
    rw [sq_abs] at htrial
    have htail := Zeta5.Analysis.exponential_tail_envelope (y := y) (T := physicalTailThreshold s₁ s₂ δ) hN1
    calc
      _ ≤ P.eval ((N : ℝ) ^ 2 * y ^ 2) ^ 2 *
          (C * (N : ℝ) ^ 3 * physicalWeightScale N m₁ m₂ * (1 + y ^ 3) *
            Real.exp (-(N : ℝ) * physicalField s₁ s₂ y)) :=
        mul_le_mul_of_nonneg_left hw (sq_nonneg _)
      _ = (C * (N : ℝ) ^ 3 * physicalWeightScale N m₁ m₂ * (1 + y ^ 3)) *
          (P.eval ((N : ℝ) ^ 2 * y ^ 2) ^ 2 * Real.exp (-(N : ℝ) * physicalField s₁ s₂ y)) := by ring
      _ ≤ (C * (N : ℝ) ^ 3 * physicalWeightScale N m₁ m₂ * (1 + y ^ 3)) *
          (Zeta5.Analysis.trialPrefactor (2 * δ) * (N : ℝ) ^ (4 * k + 16) *
            Real.exp ((N : ℝ) * physicalEquilibrium s₁ s₂ h₁ h₂ ((k : ℝ) / N)) *
              Real.exp (-(Real.pi / 2) * (N : ℝ) * max 0 (y - physicalTailThreshold s₁ s₂ δ))) := by
        exact mul_le_mul_of_nonneg_left htrial (by positivity [physicalWeightScale_pos hN m₁ m₂])
      _ ≤ (C * (N : ℝ) ^ 3 * physicalWeightScale N m₁ m₂ * (1 + y ^ 3)) *
          (Zeta5.Analysis.trialPrefactor (2 * δ) * (N : ℝ) ^ (4 * k + 16) *
            Real.exp ((N : ℝ) * physicalEquilibrium s₁ s₂ h₁ h₂ ((k : ℝ) / N)) *
              (Real.exp ((Real.pi / 2) * physicalTailThreshold s₁ s₂ δ) * Real.exp (-(Real.pi / 2) * y))) := by
        exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left htail (by positivity))
          (by positivity)
      _ = _ := by dsimp [A, normEnvelope]; ring
  have hscaled : IntegrableOn (fun y : ℝ => P.eval ((N : ℝ) ^ 2 * y ^ 2) ^ 2 *
      physicalCommonWeight N m₁ m₂ ((N : ℝ) * y)) (Ioi 0) := by
    have h := (integrableOn_Ioi_comp_mul_left_iff
      (fun x : ℝ => P.eval (x ^ 2) ^ 2 * physicalCommonWeight N m₁ m₂ x) 0 hNr).mpr
        (by simpa only [mul_zero] using windowSquaredNorm_integrable N m₁ m₂ P)
    simpa only [mul_pow] using h
  rw [windowSquaredNorm_scaled N m₁ m₂ hN]
  have hI := integral_mono_ae hscaled (normEnvelope_integrable.const_mul A) (by
    filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with y hy
    exact hpoint hy)
  rw [integral_const_mul, normEnvelope_integral] at hI
  apply (mul_le_mul_of_nonneg_left hI hNr.le).trans_eq
  dsimp [A, K]
  have hp : (N : ℝ) * (N : ℝ) ^ 3 * (N : ℝ) ^ (4 * k + 16) =
      (N : ℝ) ^ (4 * k + 20) := by
    rw [← pow_succ', ← pow_add]
    congr 1
    omega
  calc
    _ = (C * Zeta5.Analysis.trialPrefactor (2 * δ) * Real.exp ((Real.pi / 2) * physicalTailThreshold s₁ s₂ δ) * normEnvelopeMass) *
        physicalWeightScale N m₁ m₂ * ((N : ℝ) * (N : ℝ) ^ 3 * (N : ℝ) ^ (4 * k + 16)) *
          Real.exp ((N : ℝ) * physicalEquilibrium s₁ s₂ h₁ h₂ ((k : ℝ) / N)) := by ring
    _ = _ := by rw [hp]

end Zeta3.Analysis

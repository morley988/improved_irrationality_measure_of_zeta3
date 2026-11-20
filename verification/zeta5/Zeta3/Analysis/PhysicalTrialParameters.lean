import Zeta3.Analysis.AngularTrialExistence

/-! # Uniform support and degree parameters for every actual trial space -/

noncomputable section
namespace Zeta3.Analysis
open Set

theorem physicalMass_le_three_halves {s₁ s₂ b : ℝ}
    (h₁ : 0 ≤ s₁) (h₂ : 0 ≤ s₂) (hb : 0 ≤ b) :
    physicalMass s₁ s₂ b ≤ (3/2:ℝ)*b := by
  have hsa : Real.sqrt (s₁^2+b^2) ≤ s₁+b :=
    (Real.sqrt_le_iff).2 ⟨by positivity,by nlinarith [mul_nonneg h₁ hb]⟩
  have hsb : Real.sqrt (s₂^2+b^2) ≤ s₂+b :=
    (Real.sqrt_le_iff).2 ⟨by positivity,by nlinarith [mul_nonneg h₂ hb]⟩
  have hs1 : 1 ≤ Real.sqrt (1+b^2) := Real.one_le_sqrt.2 (by nlinarith [sq_nonneg b])
  unfold physicalMass
  linarith

theorem physicalEndpoint_lower (s₁ s₂ : ℝ) (h₁ : 0 < s₁) (h₂ : 0 < s₂)
    {v : ℝ} (hv : 0 ≤ v) : (2/3:ℝ)*v ≤ physicalEndpoint s₁ s₂ h₁ h₂ v := by
  have h := physicalMass_le_three_halves h₁.le h₂.le (physicalEndpoint_nonneg s₁ s₂ h₁ h₂ v)
  rw [physicalMass_endpoint s₁ s₂ h₁ h₂ hv] at h
  linarith

namespace CertificateResponse

def trialMass (n m : ℕ) : ℝ := delta-2*(m:ℝ)/(50*n)
def trialEndpoint (n m : ℕ) : ℝ := physicalEndpoint (2/25) (8/25) (by norm_num) (by norm_num) (trialMass n m)

theorem concrete_window_ratios (n : ℕ) (hn : 0 < n) :
    ((4*n:ℕ):ℝ)/(50*n)=2/25 ∧ ((16*n:ℕ):ℝ)/(50*n)=8/25 := by
  have hnr : (n:ℝ)≠0 := by exact_mod_cast hn.ne'
  constructor <;> push_cast <;> field_simp <;> ring

theorem trial_degree_removed_le (n m : ℕ) (hn : 0 < n)
    (hcap : 2*(m:ℝ)/(50*n) ≤ angularCap) : 2*m ≤ 7*n := by
  have hnr : (0:ℝ)<n := by exact_mod_cast hn
  have h := (div_le_iff₀ (by positivity : (0:ℝ)<50*n)).mp hcap
  norm_num only [angularCap] at h
  have hh : (2:ℝ)*m ≤ 7*n := by linarith
  exact_mod_cast hh

theorem trialMass_bounds (n m : ℕ) (hn : 0 < n)
    (hcap : 2*(m:ℝ)/(50*n) ≤ angularCap) : trialMass n m ∈ Icc (22/25) delta := by
  have ht : 0 ≤ 2*(m:ℝ)/(50*n) := by positivity
  unfold trialMass
  constructor
  · dsimp [delta,angularCap] at *
    linarith
  · linarith

theorem trialEndpoint_bounds (n m : ℕ) (hn : 0 < n)
    (hcap : 2*(m:ℝ)/(50*n) ≤ angularCap) : trialEndpoint n m ∈ Icc (44/75) (51/25) := by
  have hv := trialMass_bounds n m hn hcap
  have hv0 : 0 ≤ trialMass n m := by linarith [hv.1]
  have hl := physicalEndpoint_lower (2/25) (8/25) (by norm_num) (by norm_num) hv0
  have hu := physicalEndpoint_le_twice (2/25) (8/25) (by norm_num) (by norm_num) (by norm_num) hv0
  change (44/75:ℝ) ≤ trialEndpoint n m ∧ trialEndpoint n m ≤ 51/25
  dsimp only [trialEndpoint] at *
  dsimp only [delta] at hv
  constructor <;> linarith [hv.1,hv.2]

theorem trialEndpoint_square_bounds (n m : ℕ) (hn : 0 < n)
    (hcap : 2*(m:ℝ)/(50*n) ≤ angularCap) :
    1/((50*n:ℕ):ℝ)^2 ≤ (trialEndpoint n m)^2 ∧ (trialEndpoint n m)^2 ≤ 5 := by
  have hb := trialEndpoint_bounds n m hn hcap
  have hnr : (1:ℝ)≤n := by exact_mod_cast hn
  have hN : (50:ℝ) ≤ ((50*n:ℕ):ℝ) := by push_cast; nlinarith
  have hN0 : (0:ℝ) < ((50*n:ℕ):ℝ)^2 := by positivity
  constructor
  · have hb1 : (1:ℝ)/4 ≤ (trialEndpoint n m)^2 := by nlinarith [hb.1]
    have hden : (4:ℝ) ≤ ((50*n:ℕ):ℝ)^2 := by nlinarith
    exact (one_div_le_one_div_of_le (by norm_num : (0:ℝ)<4) hden).trans hb1
  · nlinarith [hb.1,hb.2]

theorem trialEndpoint_mass_index (n m : ℕ) (hn : 0 < n)
    (hcap : 2*(m:ℝ)/(50*n) ≤ angularCap) :
    ((50*n:ℕ):ℝ)*physicalMass (2/25) (8/25) (trialEndpoint n m) = ((51*n-2*m:ℕ):ℝ) := by
  have hrem := trial_degree_removed_le n m hn hcap
  have hle : 2*m ≤ 51*n := by omega
  have hv := (trialMass_bounds n m hn hcap).1
  unfold trialEndpoint
  rw [physicalMass_endpoint (2/25) (8/25) (by norm_num) (by norm_num) (by linarith)]
  rw [Nat.cast_sub hle]
  unfold trialMass delta
  push_cast
  have hnr : (n:ℝ)≠0 := by exact_mod_cast hn.ne'
  field_simp <;> ring

end CertificateResponse
end Zeta3.Analysis

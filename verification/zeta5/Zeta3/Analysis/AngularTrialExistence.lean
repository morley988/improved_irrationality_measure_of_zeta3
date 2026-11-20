import Zeta3.Analysis.AngularTrial
import Zeta3.Analysis.CertifiedContourExponent

/-! # Uniform angular factors for every admissible degree, including zero -/

noncomputable section
namespace Zeta3.Analysis
open Set
open scoped BigOperators

variable {j : ℕ}

theorem angularField_nonneg (c : ℝ) (weights poles : Fin j → ℝ)
    (hc : 0 ≤ c) (hw : ∀ i, 0 ≤ weights i) (he : ∀ i, 0 < poles i)
    {y : ℝ} (hy : 0 ≤ y) : 0 ≤ angularField c weights poles y := by
  unfold angularField
  apply add_nonneg (mul_nonneg hc hy)
  apply Finset.sum_nonneg
  intro i _
  apply mul_nonneg (hw i) (Real.log_nonneg ?_)
  have h := div_nonneg hy (he i).le
  linarith

theorem angularQuantileConstant_ge_one (c : ℝ) (weights poles : Fin j → ℝ)
    (hc : 0 < c) (hw : ∀ i, 0 ≤ weights i) (he : ∀ i, 0 < poles i) :
    1 ≤ angularQuantileConstant c weights poles := by
  have hp := angularRadialBound_pos hc hw he
  have hex : 1 ≤ Real.exp (24*angularRadialBound c weights poles) := Real.one_le_exp_iff.2 (by positivity)
  unfold angularQuantileConstant
  linarith

theorem exists_angular_factors_at_mass (c : ℝ) (weights poles : Fin j → ℝ)
    (hc : 0 < c) (hw : ∀ i, 0 ≤ weights i) (he : ∀ i, 0 < poles i)
    {N : ℝ} (hN : 1 ≤ N) (m : ℕ)
    (hcap : 2*(m:ℝ)/N ≤ angularMass c weights poles 1) :
    ∃ h : Fin m → ℝ, (∀ i, h i ∈ Icc 0 1) ∧ ∀ y : ℝ, 0 ≤ y →
      (∏ i, (2*|y-h i|)^2) ≤ angularQuantileConstant c weights poles*N^16*
        Real.exp (N*(angularField c weights poles y+
          angularProfile c weights poles hc hw he (2*(m:ℝ)/N))) := by
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · refine ⟨Fin.elim0, fun i => Fin.elim0 i, ?_⟩
    intro y hy
    simp only [Nat.cast_zero, mul_zero, zero_div, angularProfile_zero, add_zero, Fin.prod_univ_zero]
    have hC := angularQuantileConstant_ge_one c weights poles hc hw he
    have hp : 1 ≤ N^16 := one_le_pow₀ hN
    have he : 1 ≤ Real.exp (N*angularField c weights poles y) :=
      Real.one_le_exp_iff.2 (mul_nonneg (by linarith) (angularField_nonneg c weights poles hc.le hw he hy))
    nlinarith [mul_le_mul hC hp (by norm_num : (0:ℝ)≤1) (by positivity)]
  · have hNN : 0 < N := by linarith
    have ht : 0 ≤ 2*(m:ℝ)/N := by positivity
    let B := angularEndpoint c weights poles hc hw he (2*(m:ℝ)/N)
    have hB := angularEndpoint_nonneg c weights poles hc hw he (2*(m:ℝ)/N)
    have hB1 : B ≤ 1 := (angularEndpoint_mem_Icc_of_signs c weights poles hc hw he ht
      (by norm_num : (0:ℝ)≤0) (by norm_num : (0:ℝ)≤1) (by simpa only [angularMass_zero] using ht) hcap).2
    have hb1 : Real.sqrt B ≤ 1 := (Real.sqrt_le_iff).2 ⟨by norm_num,by simpa using hB1⟩
    apply exists_uniform_angular_quantile_zeros c weights poles hc hw he
      (Real.sqrt_nonneg B) hb1 hN m hm
    rw [Real.sq_sqrt hB]
    exact angularMass_endpoint c weights poles hc hw he ht

namespace CertificateResponse

theorem exists_certified_angular_factors {N : ℝ} (hN : 1 ≤ N) (m : ℕ)
    (hcap : 2*(m:ℝ)/N ≤ angularCap)
    (hguard : angularCap < angularMass CertificateAngular.coefficient
      CertificateAngular.weight CertificateAngular.pole 1) :
    ∃ h : Fin m → ℝ, (∀ i, h i ∈ Icc 0 1) ∧ ∀ y : ℝ, 0 ≤ y →
      (∏ i, (2*|y-h i|)^2) ≤
        angularQuantileConstant CertificateAngular.coefficient CertificateAngular.weight CertificateAngular.pole*N^16*
          Real.exp (N*(angularField CertificateAngular.coefficient CertificateAngular.weight CertificateAngular.pole y+
            angularProfile CertificateAngular.coefficient CertificateAngular.weight CertificateAngular.pole
              CertificateAngular.coefficient_pos CertificateAngular.weight_nonneg CertificateAngular.pole_pos (2*(m:ℝ)/N))) :=
  exists_angular_factors_at_mass _ _ _ CertificateAngular.coefficient_pos
    CertificateAngular.weight_nonneg CertificateAngular.pole_pos hN m (hcap.trans hguard.le)

end CertificateResponse
end Zeta3.Analysis

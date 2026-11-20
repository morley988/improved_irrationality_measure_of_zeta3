import Zeta3.Analysis.ComplexPolynomialComparison
import Zeta3.Analysis.ContourUniformNorm

/-!
# The genuine physical quadratic form controls complex polynomial values

This combines the proved polynomial-loss real-axis bound with the actual
measure's contact identity and the proved exterior comparison.
-/

noncomputable section
namespace Zeta3.Analysis
open MeasureTheory Set Polynomial
open scoped NNReal

theorem physicalSquaredMeasure_ae_mem (s₁ s₂ : ℝ)
    (h₁ : 0 < s₁) (h₂ : 0 < s₂) {b : ℝ} (hb : 0 ≤ b) :
    ∀ᵐ w ∂physicalSquaredMeasure s₁ s₂ h₁ h₂ b, w ∈ Icc 0 (b^2) := by
  unfold physicalSquaredMeasure
  apply Measure.ae_smul_measure
  exact ae_add_measure_iff.mpr
    ⟨Zeta5.Analysis.squaredAuxiliaryMeasure_ae_mem s₁ h₁ hb,
      Zeta5.Analysis.squaredAuxiliaryMeasure_ae_mem s₂ h₂ hb⟩

theorem physicalSquaredMeasure_real_univ (s₁ s₂ : ℝ)
    (h₁ : 0 < s₁) (h₂ : 0 < s₂) {b : ℝ} (hb : 0 ≤ b) :
    (physicalSquaredMeasure s₁ s₂ h₁ h₂ b).real univ = physicalMass s₁ s₂ b := by
  have h := congrArg (fun μ : Measure ℝ => μ.real univ)
    (physicalSquaredMeasure_restrict_Ioc s₁ s₂ h₁ h₂ hb)
  rw [measureReal_restrict_apply_univ] at h
  exact h.symm.trans (physicalSquaredMeasure_real_Ioc s₁ s₂ h₁ h₂ hb)

theorem physicalComplexPotential_contact (s₁ s₂ : ℝ)
    (h₁ : 0 < s₁) (h₂ : 0 < s₂) {b x : ℝ} (hb : 0 ≤ b) (hx : x ∈ Icc 0 (b^2)) :
    2 * complexLogPotential (physicalSquaredMeasure s₁ s₂ h₁ h₂ b) (x:ℂ) -
      physicalField s₁ s₂ (Real.sqrt x) = physicalEquilibriumAtEndpoint s₁ s₂ h₁ h₂ b := by
  have hyb : Real.sqrt x ≤ b := (Real.sqrt_le_iff).2 ⟨hb,hx.2⟩
  have hc := physicalPotential_equilibrium_eq s₁ s₂ h₁ h₂ (Real.sqrt_nonneg x) hyb
  rw [physicalPotential_integral s₁ s₂ h₁ h₂ hb, Real.sq_sqrt hx.1] at hc
  have he : complexLogPotential (physicalSquaredMeasure s₁ s₂ h₁ h₂ b) (x:ℂ) =
      ∫ w : ℝ, Real.log |x-w| ∂physicalSquaredMeasure s₁ s₂ h₁ h₂ b := by
    unfold complexLogPotential
    simp only [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
  rw [he]
  linarith

/-- Generic square estimate, including a vanishing boundary bound. -/
theorem polynomial_square_le_from_contact (μ : Measure ℝ) [IsFiniteMeasure μ]
    {B C N H ell : ℝ} (hB : 0 ≤ B) (hC : 0 ≤ C) (hN : 0 ≤ N) (hH : 0 ≤ H)
    (hsupport : ∀ᵐ w ∂μ, w ∈ Icc 0 B)
    (hsmall : ∀ (v ρ : ℝ), 0 < ρ →
      μ {w : ℝ | |v-w| < ρ^4} ≤ ENNReal.ofReal (C*ρ))
    (m : ℕ) (hmass : N*μ.real univ = m) (p : Polynomial ℂ) (hdeg : p.natDegree < m)
    (V : ℝ → ℝ) (hcontact : ∀ x ∈ Icc 0 B, 2*complexLogPotential μ (x:ℂ)-V x=ell)
    (hboundary : ∀ x ∈ Icc 0 B, ‖p.eval (x:ℂ)‖^2*Real.exp (-N*V x) ≤ H)
    (z : ℂ) : ‖p.eval z‖^2 ≤ H*Real.exp (N*(2*complexLogPotential μ z-ell)) := by
  let M := Real.sqrt H * Real.exp (-N*ell/2)
  have hM : 0 ≤ M := by dsimp [M]; positivity
  have hMsq : M^2 = H*Real.exp (-N*ell) := by
    dsimp [M]
    rw [mul_pow, Real.sq_sqrt hH, ← Real.exp_nat_mul]
    congr 2
    ring
  have hb : ∀ x ∈ Icc 0 B, ‖p.eval (x:ℂ)‖ * Real.exp (-N*complexLogPotential μ (x:ℂ)) ≤ M := by
    intro x hx
    have hc := hcontact x hx
    have he : (Real.exp (-N*complexLogPotential μ (x:ℂ)))^2 =
        Real.exp (-N*V x)*Real.exp (-N*ell) := by
      rw [← Real.exp_nat_mul, ← Real.exp_add]
      congr 1
      norm_num only [Nat.cast_ofNat]
      nlinarith
    have hs : (‖p.eval (x:ℂ)‖*Real.exp (-N*complexLogPotential μ (x:ℂ)))^2 ≤ M^2 := by
      rw [mul_pow, he, hMsq, ← mul_assoc]
      exact mul_le_mul_of_nonneg_right (hboundary x hx) (Real.exp_nonneg _)
    exact (sq_le_sq₀ (by positivity) hM).mp hs
  have hc := polynomial_weighted_le μ hB hC hN hM hsupport hsmall m hmass p hdeg hb z
  have hs := (sq_le_sq₀ (by positivity : 0 ≤ ‖p.eval z‖*Real.exp (-N*complexLogPotential μ z)) hM).mpr hc
  rw [mul_pow, hMsq, ← Real.exp_nat_mul] at hs
  have hm := mul_le_mul_of_nonneg_right hs (Real.exp_nonneg (2*N*complexLogPotential μ z))
  have hl : (‖p.eval z‖^2*Real.exp (2*(-N*complexLogPotential μ z)))*
      Real.exp (2*N*complexLogPotential μ z) = ‖p.eval z‖^2 := by
    rw [mul_assoc, ← Real.exp_add]
    ring_nf
    simp
  have hr : (H*Real.exp (-N*ell))*Real.exp (2*N*complexLogPotential μ z) =
      H*Real.exp (N*(2*complexLogPotential μ z-ell)) := by
    rw [mul_assoc, ← Real.exp_add]
    congr 2
    ring
  norm_num only [Nat.cast_ofNat] at hm
  simpa only [hl,hr] using hm

/-- The actual complex pointwise norm estimate, uniform in the polynomial. -/
theorem actual_physical_complex_norm_bound (q : ℝ[X]) (n N m₁ m₂ m : ℕ) (δ b R : ℝ)
    (hd : q.natDegree ≤ n) (hdegree : q.natDegree < m)
    (hN : 0 < N) (hm₁ : 0 < m₁) (hm₂ : 0 < m₂)
    (hδ : 0 ≤ δ) (hn : (n:ℝ) ≤ δ*(N:ℝ)) (hb : 0 ≤ b) (hBR : b^2 ≤ R)
    (hBN : 1/(N:ℝ)^2 ≤ b^2)
    (hmass : (N:ℝ)*physicalMass ((m₁:ℝ)/N) ((m₂:ℝ)/N) b = m)
    (z : ℂ) :
    ‖q.eval₂ Complex.ofRealHom z‖^2 ≤
      physicalNormComparisonConstant δ
        (physicalDensityCompactConstant ((m₁:ℝ)/N) ((m₂:ℝ)/N) R)*(N:ℝ)^20*
      normalizedPhysicalNorm N m₁ m₂ q *
        Real.exp ((N:ℝ)*(2*complexLogPotential
          (physicalSquaredMeasure ((m₁:ℝ)/N) ((m₂:ℝ)/N) (by positivity) (by positivity) b) z-
            physicalEquilibriumAtEndpoint ((m₁:ℝ)/N) ((m₂:ℝ)/N) (by positivity) (by positivity) b)) := by
  have hNr : (0:ℝ)<N := by exact_mod_cast hN
  have hs₁ : 0 < (m₁:ℝ)/N := by positivity
  have hs₂ : 0 < (m₂:ℝ)/N := by positivity
  have hR : 0 < R := lt_of_lt_of_le (lt_of_lt_of_le (by positivity) hBN) hBR
  have hκ := physicalDensityCompactConstant_pos ((m₁:ℝ)/N) ((m₂:ℝ)/N) R hR
  have hK := physicalNormComparisonConstant_pos δ _ hδ hκ
  have hH : 0 ≤ physicalNormComparisonConstant δ
      (physicalDensityCompactConstant ((m₁:ℝ)/N) ((m₂:ℝ)/N) R)*(N:ℝ)^20*
        normalizedPhysicalNorm N m₁ m₂ q := by
    exact mul_nonneg (mul_nonneg hK.le (by positivity)) (normalizedPhysicalNorm_nonneg N m₁ m₂ hN q)
  have hmap : (q.map Complex.ofRealHom).natDegree < m :=
    (Polynomial.natDegree_map_le).trans_lt hdegree
  have hp := polynomial_square_le_from_contact
    (physicalSquaredMeasure ((m₁:ℝ)/N) ((m₂:ℝ)/N) hs₁ hs₂ b)
    (sq_nonneg b) (by positivity : (0:ℝ) ≤ 3+(3/2:ℝ)*b) hNr.le hH
    (physicalSquaredMeasure_ae_mem _ _ hs₁ hs₂ hb)
    (fun v ρ hρ => physicalSquaredMeasure_smallBall _ _ hs₁ hs₂ hb v ρ hρ) m
    (by rw [physicalSquaredMeasure_real_univ _ _ hs₁ hs₂ hb]; exact hmass)
    (q.map Complex.ofRealHom) hmap
    (fun x => physicalField ((m₁:ℝ)/N) ((m₂:ℝ)/N) (Real.sqrt x))
    (fun x hx => physicalComplexPotential_contact _ _ hs₁ hs₂ hb hx) ?_ z
  · simpa only [Polynomial.eval_map] using hp
  · intro x hx
    have h := actual_physical_uniform_norm_bound q n N m₁ m₂ δ (b^2) R
      hd hN hm₁ hm₂ hδ hn hBR hBN x hx
    rw [Polynomial.eval_map]
    change ‖q.eval₂ Complex.ofRealHom (Complex.ofRealHom x)‖^2 * _ ≤ _
    rw [Polynomial.eval₂_at_apply]
    simpa only [Complex.ofRealHom_eq_coe, Complex.norm_real, Real.norm_eq_abs, sq_abs] using h

end Zeta3.Analysis

import Zeta3.Analysis.GammaKernel
import Zeta3.Analysis.FiniteGrid
import Zeta3.Analysis.CertifiedResponse

/-!
# The actual linear angular-deficit integral and its finite grid

This file defines the integral `C_v` appearing in the manuscript, proves
the kernel monotonicity used by its 2,048-panel lower Riemann sum, and
isolates finite external sample bounds.  Identifying this integral with
the physical potential deficit remains a separate mathematical theorem.
-/

noncomputable section
open Set MeasureTheory
open scoped BigOperators

namespace Zeta3.Analysis

def physicalLinearKernel (u b : ℝ) : ℝ := u*b^2/gammaRadical u b^3

theorem physicalLinearKernel_formula (u b : ℝ) :
    physicalLinearKernel u b = u*b*b/((u^2+b^2)*Real.sqrt (u^2+b^2)) := by
  unfold physicalLinearKernel
  rw [show gammaRadical u b^3=gammaRadical u b^2*gammaRadical u b by ring,
    gammaRadical_sq]
  unfold gammaRadical
  ring

theorem physicalLinearKernel_hasDerivAt {u b : ℝ} (hu : 0 < u) :
    HasDerivAt (physicalLinearKernel u)
      (u*b*(2*u^2-b^2)/gammaRadical u b^5) b := by
  have hw := gammaRadical_pos (b := b) hu
  have hs := gammaRadical_sq u b
  have h := (((hasDerivAt_id b).pow 2).const_mul u).div
    ((gammaRadical_hasDerivAt (b := b) hu).pow 3) (by exact pow_ne_zero 3 (ne_of_gt hw))
  simp only [Pi.pow_apply, id_eq, Nat.cast_ofNat, Nat.reduceSub, pow_one, mul_one] at h
  convert! h using 1
  field_simp
  rw [hs]
  ring

theorem physicalLinearKernel_continuous {u : ℝ} (hu : 0 < u) :
    Continuous (physicalLinearKernel u) :=
  continuous_iff_continuousAt.mpr (fun _ => (physicalLinearKernel_hasDerivAt hu).continuousAt)

theorem physicalLinearKernel_nonneg {u : ℝ} (hu : 0 < u) (b : ℝ) :
    0 ≤ physicalLinearKernel u b := by
  unfold physicalLinearKernel
  positivity [gammaRadical_pos (b := b) hu]

theorem physicalLinearKernel_monotoneOn {u : ℝ} (hu : 0 < u) :
    MonotoneOn (physicalLinearKernel u) (Icc 0 u) := by
  apply monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc 0 u)
    (physicalLinearKernel_continuous hu).continuousOn
    (fun b _ => (physicalLinearKernel_hasDerivAt hu).hasDerivWithinAt)
  intro b hb
  have hb' : b ∈ Icc (0:ℝ) u := interior_subset hb
  have hp : 0 ≤ 2*u^2-b^2 := by nlinarith [sq_nonneg u, mul_nonneg hb'.1 (sub_nonneg.mpr hb'.2)]
  exact div_nonneg (mul_nonneg (mul_nonneg hu.le hb'.1) hp)
    (pow_nonneg (gammaRadical_pos (b := b) hu).le 5)

theorem physicalEndpoint_monotone_nonneg (s₁ s₂ : ℝ) (h₁ : 0 < s₁) (h₂ : 0 < s₂) :
    MonotoneOn (physicalEndpoint s₁ s₂ h₁ h₂) (Ici 0) := by
  intro a ha b hb hab
  by_contra! h
  have hm := physicalMass_strictMonoOn h₁ h₂
    (physicalEndpoint_nonneg s₁ s₂ h₁ h₂ b) (physicalEndpoint_nonneg s₁ s₂ h₁ h₂ a) h
  rw [physicalMass_endpoint s₁ s₂ h₁ h₂ hb,physicalMass_endpoint s₁ s₂ h₁ h₂ ha] at hm
  exact not_lt_of_ge hab hm

def physicalLinearIntegrand (s₁ s₂ u : ℝ) (h₁ : 0 < s₁) (h₂ : 0 < s₂) (v : ℝ) : ℝ :=
  physicalLinearKernel u (physicalEndpoint s₁ s₂ h₁ h₂ v)

def physicalLinearIntegral (s₁ s₂ u : ℝ) (h₁ : 0 < s₁) (h₂ : 0 < s₂) (v : ℝ) : ℝ :=
  ∫ w in 0..v, physicalLinearIntegrand s₁ s₂ u h₁ h₂ w

theorem physicalLinearIntegrand_continuous (s₁ s₂ u : ℝ)
    (h₁ : 0 < s₁) (h₂ : 0 < s₂) (hu : 0 < u) :
    Continuous (physicalLinearIntegrand s₁ s₂ u h₁ h₂) :=
  (physicalLinearKernel_continuous hu).comp (physicalEndpoint_continuous s₁ s₂ h₁ h₂)

theorem physicalLinearIntegrand_monotoneOn (s₁ s₂ u cap : ℝ)
    (h₁ : 0 < s₁) (h₂ : 0 < s₂) (hu : 0 < u)
    (hguard : cap ≤ physicalMass s₁ s₂ u) :
    MonotoneOn (physicalLinearIntegrand s₁ s₂ u h₁ h₂) (Icc 0 cap) := by
  have hb (v : ℝ) (hv : v ∈ Icc 0 cap) : physicalEndpoint s₁ s₂ h₁ h₂ v ∈ Icc 0 u := by
    refine ⟨physicalEndpoint_nonneg s₁ s₂ h₁ h₂ v, ?_⟩
    exact (physicalEndpoint_mem_of_mass_bracket s₁ s₂ h₁ h₂ (lo := 0) (hi := u) hv.1 (by norm_num) hu.le
      (by simpa [physicalMass_zero h₁.le h₂.le] using hv.1) (hv.2.trans hguard)).2
  intro a ha b hb' hab
  exact physicalLinearKernel_monotoneOn hu (hb a ha) (hb b hb')
    (physicalEndpoint_monotone_nonneg s₁ s₂ h₁ h₂ ha.1 hb'.1 hab)

theorem physicalLinearIntegral_monotoneOn (s₁ s₂ u : ℝ)
    (h₁ : 0 < s₁) (h₂ : 0 < s₂) (hu : 0 < u) :
    MonotoneOn (physicalLinearIntegral s₁ s₂ u h₁ h₂) (Ici 0) := by
  intro a ha b hb hab
  exact intervalIntegral.integral_mono_interval (le_refl 0) ha hab
    (Filter.Eventually.of_forall (fun w => physicalLinearKernel_nonneg hu _))
    ((physicalLinearIntegrand_continuous s₁ s₂ u h₁ h₂ hu).intervalIntegrable 0 b)

namespace CertificateLinear

def cap : ℝ := 22/25
def integrand : ℝ → ℝ := physicalLinearIntegrand (2/25) (8/25) CertificateAngular.contour
  (by norm_num) (by norm_num)
def integral (v : ℝ) : ℝ := physicalLinearIntegral (2/25) (8/25) CertificateAngular.contour
  (by norm_num) (by norm_num) v

structure FiniteEvidence (lower : ℕ → ℝ) : Prop where
  physical_guard : CertificateResponse.delta < physicalMass (2/25) (8/25) CertificateAngular.contour
  sample_lower : ∀ i < 2048, lower i ≤ integrand ((cap/2048)*(i:ℝ))
  sum_lower : CertificateAngular.coefficient ≤ (cap/2048)*∑ i ∈ Finset.range 2048, lower i

theorem integral_lower {lower : ℕ → ℝ} (h : FiniteEvidence lower) :
    CertificateAngular.coefficient ≤ integral cap := by
  have hcap : cap ≤ physicalMass (2/25) (8/25) CertificateAngular.contour :=
    (by norm_num [cap,CertificateResponse.delta] : cap ≤ CertificateResponse.delta).trans h.physical_guard.le
  have hm := physicalLinearIntegrand_monotoneOn (2/25) (8/25) CertificateAngular.contour cap
    (by norm_num) (by norm_num) (by norm_num [CertificateAngular.contour]) hcap
  have hgrid := left_sum_le_integral_of_monotoneOn integrand
    (h := cap/2048) (by norm_num [cap]) 2048 (by simpa [integrand] using hm)
  have hs : (cap/2048)*∑ i ∈ Finset.range 2048, lower i ≤
      (cap/2048)*∑ i ∈ Finset.range 2048, integrand ((cap/2048)*(i:ℝ)) := by
    apply mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun i hi => h.sample_lower i (Finset.mem_range.mp hi)))
    norm_num [cap]
  have hp := h.sum_lower.trans (hs.trans hgrid)
  simpa [integral, physicalLinearIntegral, integrand] using hp

theorem integral_lower_of_cap_le {lower : ℕ → ℝ} (h : FiniteEvidence lower)
    {v : ℝ} (hv : cap ≤ v) : CertificateAngular.coefficient ≤ integral v := by
  apply (integral_lower h).trans
  exact physicalLinearIntegral_monotoneOn (2/25) (8/25) CertificateAngular.contour
    (by norm_num) (by norm_num) (by norm_num [CertificateAngular.contour])
    (by norm_num [cap]) (le_trans (by norm_num [cap]) hv) hv

end CertificateLinear
end Zeta3.Analysis

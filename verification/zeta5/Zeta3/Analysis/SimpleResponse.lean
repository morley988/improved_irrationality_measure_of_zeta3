import Zeta3.Analysis.AngularProfile
import Zeta3.Analysis.FiniteGrid

/-!
# Finite numerical evidence bounds the actual response integral

The angular function is the explicit response at its constructed inverse mass
endpoint.  The physical response is supplied as a function together with a
mathematical monotonicity theorem; that theorem is deliberately not a field
of the finite external-numerics interface.

The numerical structure contains only a finite sample table, its rational
upper sum and endpoint inequalities.  Integrability, interval monotonicity,
positivity between sample points, and the bound on the actual integral are
proved here, not delegated to the external checker.
-/

namespace Zeta3.Analysis

open MeasureTheory Set Finset
open scoped BigOperators

noncomputable section

variable {m : ℕ}

def simpleResponse (Γ : ℝ → ℝ) (δ c : ℝ) (K e : Fin m → ℝ)
    (hc : 0 < c) (hK : ∀ j, 0 ≤ K j) (he : ∀ j, 0 < e j) (t : ℝ) : ℝ :=
  Γ (δ - t) + angularProfile c K e hc hK he t

theorem simpleResponse_strictAntiOn (Γ : ℝ → ℝ) (δ c : ℝ) (K e : Fin m → ℝ)
    (hc : 0 < c) (hK : ∀ j, 0 ≤ K j) (he : ∀ j, 0 < e j)
    {T : ℝ} (hT : 0 < T)
    (hΓ : MonotoneOn Γ (Icc (δ - T) δ))
    (hcap : angularEndpoint c K e hc hK he T < 2) :
    StrictAntiOn (simpleResponse Γ δ c K e hc hK he) (Icc 0 T) := by
  intro s hs t ht hst
  have hphys := hΓ (show δ - t ∈ Icc (δ - T) δ by constructor <;> linarith [ht.1, ht.2])
    (show δ - s ∈ Icc (δ - T) δ by constructor <;> linarith [hs.1, hs.2])
    (by linarith : δ - t ≤ δ - s)
  have hang := angularProfile_strictAntiOn c K e hc hK he hT hcap hs ht hst
  dsimp [simpleResponse]
  linarith

theorem simpleResponse_intervalIntegrable (Γ : ℝ → ℝ) (δ c : ℝ) (K e : Fin m → ℝ)
    (hc : 0 < c) (hK : ∀ j, 0 ≤ K j) (he : ∀ j, 0 < e j)
    {T : ℝ} (hT : 0 < T)
    (hΓ : MonotoneOn Γ (Icc (δ - T) δ))
    (hcap : angularEndpoint c K e hc hK he T < 2) :
    IntervalIntegrable (simpleResponse Γ δ c K e hc hK he) volume 0 T := by
  apply AntitoneOn.intervalIntegrable
  rw [uIcc_of_le hT.le]
  exact (simpleResponse_strictAntiOn Γ δ c K e hc hK he hT hΓ hcap).antitoneOn

theorem simpleResponse_pos_of_endpoint (Γ : ℝ → ℝ) (δ c : ℝ) (K e : Fin m → ℝ)
    (hc : 0 < c) (hK : ∀ j, 0 ≤ K j) (he : ∀ j, 0 < e j)
    {T : ℝ} (hT : 0 < T)
    (hΓ : MonotoneOn Γ (Icc (δ - T) δ))
    (hcap : angularEndpoint c K e hc hK he T < 2)
    (hend : 0 < simpleResponse Γ δ c K e hc hK he T) :
    ∀ t ∈ Icc 0 T, 0 < simpleResponse Γ δ c K e hc hK he t := by
  intro t ht
  exact lt_of_lt_of_le hend
    ((simpleResponse_strictAntiOn Γ δ c K e hc hK he hT hΓ hcap).antitoneOn
      ht ⟨hT.le, le_rfl⟩ ht.2)

/-- Only finitely many numerical inequalities; no asymptotic or integral premise. -/
structure ResponseGridEvidence (f : ℝ → ℝ) (T : ℝ) (n : ℕ)
    (upper : ℕ → ℝ) (integralUpper endpointLower endpointUpper : ℝ) : Prop where
  sample_bounds : ∀ i < n, f ((T / (n : ℝ)) * (i : ℝ)) ≤ upper i
  sum_bound : (T / (n : ℝ)) * (∑ i ∈ range n, upper i) ≤ integralUpper
  endpoint_lower : endpointLower ≤ f T
  endpoint_upper : f T ≤ endpointUpper

theorem integral_le_of_responseGridEvidence (f : ℝ → ℝ) {T : ℝ} (hT : 0 ≤ T)
    {n : ℕ} (hn : 0 < n) {upper : ℕ → ℝ} {I lo hi : ℝ}
    (hm : AntitoneOn f (Icc 0 T))
    (evidence : ResponseGridEvidence f T n upper I lo hi) :
    (∫ t in 0..T, f t) ≤ I := by
  have hnR : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hh : 0 ≤ T / (n : ℝ) := div_nonneg hT hnR.le
  have hlen : T / (n : ℝ) * (n : ℝ) = T := by field_simp
  have hgrid := integral_le_left_sum_of_antitoneOn f hh n (by simpa only [hlen] using hm)
  rw [hlen] at hgrid
  have hs := mul_le_mul_of_nonneg_left
    (Finset.sum_le_sum (fun i hi => evidence.sample_bounds i (mem_range.mp hi))) hh
  exact hgrid.trans (hs.trans evidence.sum_bound)

theorem simpleResponse_integral_le_of_evidence
    (Γ : ℝ → ℝ) (δ c : ℝ) (K e : Fin m → ℝ)
    (hc : 0 < c) (hK : ∀ j, 0 ≤ K j) (he : ∀ j, 0 < e j)
    {T : ℝ} (hT : 0 < T)
    (hΓ : MonotoneOn Γ (Icc (δ - T) δ))
    (hcap : angularEndpoint c K e hc hK he T < 2)
    {n : ℕ} (hn : 0 < n) {upper : ℕ → ℝ} {I lo hi : ℝ}
    (evidence : ResponseGridEvidence (simpleResponse Γ δ c K e hc hK he)
      T n upper I lo hi) :
    (∫ t in 0..T, simpleResponse Γ δ c K e hc hK he t) ≤ I :=
  integral_le_of_responseGridEvidence _ hT.le hn
    (simpleResponse_strictAntiOn Γ δ c K e hc hK he hT hΓ hcap).antitoneOn evidence

theorem simpleResponse_positive_of_evidence
    (Γ : ℝ → ℝ) (δ c : ℝ) (K e : Fin m → ℝ)
    (hc : 0 < c) (hK : ∀ j, 0 ≤ K j) (he : ∀ j, 0 < e j)
    {T : ℝ} (hT : 0 < T)
    (hΓ : MonotoneOn Γ (Icc (δ - T) δ))
    (hcap : angularEndpoint c K e hc hK he T < 2)
    {n : ℕ} {upper : ℕ → ℝ} {I lo hi : ℝ} (hlo : 0 < lo)
    (evidence : ResponseGridEvidence (simpleResponse Γ δ c K e hc hK he)
      T n upper I lo hi) :
    ∀ t ∈ Icc 0 T, 0 < simpleResponse Γ δ c K e hc hK he t :=
  simpleResponse_pos_of_endpoint Γ δ c K e hc hK he hT hΓ hcap
    (lt_of_lt_of_le hlo evidence.endpoint_lower)

end

end Zeta3.Analysis

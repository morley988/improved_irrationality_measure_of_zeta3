import Mathlib.Analysis.Complex.AbsMax
import Mathlib.Analysis.Complex.Harmonic.Analytic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Topology.Connected.Clopen

/-!
# A weighted maximum principle from local analytic representations

If `u` is harmonic, then locally `u = Re F` for an analytic function `F`.
Thus `‖q‖ exp(-u)` locally is the norm of the analytic function `q exp(-F)`.
The ordinary maximum modulus principle then proves the required comparison
without postulating a separate subharmonic maximum theorem.

The exterior version assumes an actual boundary bound and an actual bound
outside some disk.  For the polynomial application the latter follows from
the strict degree/mass inequality.  Neither condition is numerical evidence.
-/

noncomputable section
open Set Filter Metric Bornology Topology InnerProductSpace

namespace Zeta3.Analysis

/-- A real function locally representable as the norm of an analytic function. -/
def LocalAnalyticNormOn (g : ℂ → ℝ) (U : Set ℂ) : Prop :=
  ∀ z ∈ U, ∃ f : ℂ → ℂ,
    (∀ᶠ w in 𝓝 z, DifferentiableAt ℂ f w) ∧ (∀ᶠ w in 𝓝 z, g w = ‖f w‖)

theorem LocalAnalyticNormOn.mono {g : ℂ → ℝ} {U V : Set ℂ}
    (h : LocalAnalyticNormOn g U) (hVU : V ⊆ U) : LocalAnalyticNormOn g V :=
  fun z hz => h z (hVU hz)

theorem LocalAnalyticNormOn.eventually_eq_of_isLocalMax {g : ℂ → ℝ} {U : Set ℂ}
    (h : LocalAnalyticNormOn g U) {z : ℂ} (hz : z ∈ U) (hm : IsLocalMax g z) :
    ∀ᶠ w in 𝓝 z, g w = g z := by
  obtain ⟨f,hd,he⟩ := h z hz
  have hez : g z = ‖f z‖ := he.self_of_nhds
  have hmf : IsLocalMax (norm ∘ f) z := by
    change ∀ᶠ w in 𝓝 z, ‖f w‖ ≤ ‖f z‖
    filter_upwards [hm,he] with w hw hew
    simpa only [← hew, ← hez] using hw
  have hf := Complex.norm_eventually_eq_of_isLocalMax hd hmf
  filter_upwards [he,hf] with w hew hfw
  exact hew.trans (hfw.trans hez.symm)

/-- Maximum principle for locally analytic norms on any bounded set. -/
theorem localAnalyticNorm_le_of_frontier {g : ℂ → ℝ} {U : Set ℂ}
    (hU : IsBounded U) (hc : ContinuousOn g (closure U))
    (ha : LocalAnalyticNormOn g (interior U)) {C : ℝ}
    (hb : ∀ z ∈ frontier U, g z ≤ C) {x : ℂ} (hx : x ∈ closure U) :
    g x ≤ C := by
  by_contra hbad
  have hbad' : C < g x := lt_of_not_ge hbad
  have hcompact : IsCompact (closure U) := hU.isCompact_closure
  obtain ⟨z,hz,hm⟩ := hcompact.exists_isMaxOn ⟨x,hx⟩ hc
  have hgt : C < g z := hbad'.trans_le (hm hx)
  let S : Set ℂ := closure U ∩ g ⁻¹' {g z}
  have hsclosed : IsClosed S := hc.preimage_isClosed_of_isClosed isClosed_closure isClosed_singleton
  have hsopen : IsOpen S := by
    apply isOpen_iff_mem_nhds.mpr
    intro w hw
    have hwcl : w ∈ closure U := hw.1
    have hweq : g w = g z := hw.2
    have hwint : w ∈ interior U := by
      rw [closure_eq_interior_union_frontier, mem_union] at hwcl
      rcases hwcl with hi | hbnd
      · exact hi
      · have := hb w hbnd
        linarith
    have hmw : IsMaxOn g (closure U) w := by
      intro y hy
      rw [hweq]
      exact hm hy
    have hn : closure U ∈ 𝓝 w := mem_of_superset (isOpen_interior.mem_nhds hwint)
      interior_subset_closure
    have he := ha.eventually_eq_of_isLocalMax hwint (hmw.isLocalMax hn)
    filter_upwards [isOpen_interior.mem_nhds hwint,he] with y hy hey
    exact ⟨interior_subset_closure hy, hey.trans hweq⟩
  have hsne : S.Nonempty := ⟨z,hz,rfl⟩
  have hsuniv : S = univ := (show IsClopen S from ⟨hsclosed,hsopen⟩).eq_univ hsne
  have hsbounded : IsBounded S := hcompact.isBounded.subset inter_subset_left
  rw [hsuniv] at hsbounded
  exact NormedSpace.unbounded_univ ℂ ℂ hsbounded

theorem localAnalyticNormOn_weighted (q : ℂ → ℂ) (u : ℂ → ℝ) {U : Set ℂ}
    (hU : IsOpen U) (hq : AnalyticOnNhd ℂ q U) (hu : HarmonicOnNhd u U) :
    LocalAnalyticNormOn (fun z => ‖q z‖*Real.exp (-u z)) U := by
  intro z hz
  obtain ⟨r,hr,hball⟩ := Metric.isOpen_iff.mp hU z hz
  obtain ⟨F,hF,hre⟩ := (hu.mono hball).exists_analyticOnNhd_ball_re_eq
  refine ⟨fun w => q w*Complex.exp (-F w), ?_, ?_⟩
  · filter_upwards [ball_mem_nhds z hr] with w hw
    exact (hq w (hball hw)).differentiableAt.mul ((hF w hw).differentiableAt.neg.cexp)
  · filter_upwards [ball_mem_nhds z hr] with w hw
    have hrew : (F w).re = u w := hre hw
    rw [norm_mul, Complex.norm_exp, Complex.neg_re, hrew]

/-- Exterior comparison with an explicit tail disk.  The inner set need
only be closed; no topological assumptions on its complement are needed. -/
theorem localAnalyticNorm_le_on_closed_complement {g : ℂ → ℝ} {K : Set ℂ}
    (hK : IsClosed K) (hc : Continuous g) (ha : LocalAnalyticNormOn g Kᶜ)
    (C R : ℝ) (hboundary : ∀ z ∈ K, g z ≤ C)
    (htail : ∀ z : ℂ, R ≤ ‖z‖ → g z ≤ C) (x : ℂ) :
    g x ≤ C := by
  by_cases hxK : x ∈ K
  · exact hboundary x hxK
  by_cases hxR : R ≤ ‖x‖
  · exact htail x hxR
  let U : Set ℂ := ball (0:ℂ) R ∩ Kᶜ
  have hxU : x ∈ U := ⟨by simpa only [mem_ball, dist_zero_right] using lt_of_not_ge hxR,hxK⟩
  apply localAnalyticNorm_le_of_frontier
    (isBounded_ball.subset inter_subset_left) hc.continuousOn
    (ha.mono (interior_subset.trans inter_subset_right)) (x := x) (U := U) ?_
    (subset_closure hxU)
  intro z hz
  have hf := frontier_inter_subset (ball (0:ℂ) R) Kᶜ hz
  rcases hf with hball | hinner
  · have hs := frontier_ball_subset_sphere hball.1
    apply htail z
    have he : ‖z‖ = R := by simpa only [mem_sphere, dist_zero_right] using hs
    exact he.ge
  · apply hboundary z
    have hfront : z ∈ frontier K := by simpa only [frontier_compl] using hinner.2
    exact hK.closure_eq ▸ frontier_subset_closure hfront

/-- Weighted exterior maximum principle used by the polynomial estimate. -/
theorem weighted_norm_le_on_closed_complement (q : ℂ → ℂ) (u : ℂ → ℝ)
    {K : Set ℂ} (hK : IsClosed K) (hqcont : Continuous q) (hucont : Continuous u)
    (hq : AnalyticOnNhd ℂ q Kᶜ) (hu : HarmonicOnNhd u Kᶜ)
    (C R : ℝ) (hboundary : ∀ z ∈ K, ‖q z‖*Real.exp (-u z) ≤ C)
    (htail : ∀ z : ℂ, R ≤ ‖z‖ → ‖q z‖*Real.exp (-u z) ≤ C)
    (x : ℂ) : ‖q x‖*Real.exp (-u x) ≤ C := by
  exact localAnalyticNorm_le_on_closed_complement hK
    (hqcont.norm.mul hucont.neg.rexp)
    (localAnalyticNormOn_weighted q u hK.isOpen_compl hq hu)
    C R hboundary htail x

/-- The tail hypothesis follows automatically when the weighted polynomial
norm tends to zero at infinity and the boundary bound is positive. -/
theorem weighted_norm_le_of_tendsto_zero (q : ℂ → ℂ) (u : ℂ → ℝ)
    {K : Set ℂ} (hK : IsClosed K) (hqcont : Continuous q) (hucont : Continuous u)
    (hq : AnalyticOnNhd ℂ q Kᶜ) (hu : HarmonicOnNhd u Kᶜ)
    (C : ℝ) (hC : 0 < C) (hboundary : ∀ z ∈ K, ‖q z‖*Real.exp (-u z) ≤ C)
    (hzero : Tendsto (fun z => ‖q z‖*Real.exp (-u z)) (cobounded ℂ) (𝓝 0))
    (x : ℂ) : ‖q x‖*Real.exp (-u x) ≤ C := by
  have he : ∀ᶠ z in cobounded ℂ, ‖q z‖*Real.exp (-u z) ≤ C :=
    (hzero.eventually (gt_mem_nhds hC)).mono (fun _ h => h.le)
  obtain ⟨R,_,hR⟩ := (Filter.hasBasis_cobounded_norm (E := ℂ)).eventually_iff.mp he
  exact weighted_norm_le_on_closed_complement q u hK hqcont hucont hq hu C R hboundary hR x

end Zeta3.Analysis

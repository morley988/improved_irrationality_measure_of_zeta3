import Zeta3.Transfer.IntegerJets
import Zeta3.Transfer.LogStages
import Mathlib.NumberTheory.Transcendental.Liouville.LiouvilleWith

/-!
# Quantitative transfer from bounded-order integer-polynomial jets

The central theorem proves the all-rational-approximants conclusion from
explicit algebraic and analytic hypotheses. It is an abstract transfer
theorem, not a claim that the cubic zeta determinant already satisfies those
hypotheses. In particular the local-jet decay is a mathematical input and
must never be hidden in an external numerical certificate.
-/

noncomputable section
namespace Zeta3.Transfer
open Filter Polynomial
open scoped Topology

/-- The standard eventual rational-approximation formulation of an upper
bound for an irrationality exponent. Every exponent strictly above `μ` is
excluded, with all integer numerators and all sufficiently large positive
natural denominators. -/
def HasApproximationExponentLE (ξ μ : ℝ) : Prop :=
  ∀ ν : ℝ, μ < ν → ∀ᶠ q : ℕ in atTop, ∀ p : ℤ,
    (q : ℝ) ^ (-ν) ≤ |ξ - (p : ℝ) / (q : ℝ)|

theorem HasApproximationExponentLE.mono {ξ μ μ' : ℝ}
    (h : HasApproximationExponentLE ξ μ) (hle : μ ≤ μ') :
    HasApproximationExponentLE ξ μ' := by
  intro ν hν
  exact h ν (hle.trans_lt hν)

/-- The all-denominator formulation also implies ordinary irrationality;
exact rational multiples would otherwise violate its positive lower bound. -/
theorem HasApproximationExponentLE.irrational {ξ μ : ℝ}
    (h : HasApproximationExponentLE ξ μ) : Irrational ξ := by
  rintro ⟨r, hr⟩
  obtain ⟨Q, hQ⟩ := eventually_atTop.mp (h (μ + 1) (by linarith))
  let q : ℕ := r.den * (Q + 1)
  let p : ℤ := r.num * ((Q + 1 : ℕ) : ℤ)
  have hden : 1 ≤ r.den := r.den_pos
  have hqpos : 0 < q := by dsimp [q]; positivity
  have hqge : Q ≤ q := by
    dsimp [q]
    nlinarith
  have hqR : (0 : ℝ) < q := by exact_mod_cast hqpos
  have hdenR : (r.den : ℝ) ≠ 0 := by exact_mod_cast r.den_ne_zero
  have hQR : ((Q + 1 : ℕ) : ℝ) ≠ 0 := by positivity
  have heq : (p : ℝ) / (q : ℝ) = ξ := by
    rw [← hr, Rat.cast_def]
    dsimp [p, q]
    push_cast
    field_simp
  have hbound := hQ q hqge p
  rw [heq, sub_self, abs_zero] at hbound
  exact (not_le_of_gt (Real.rpow_pos_of_pos hqR (-(μ + 1)))) hbound

/-- Uniform local bounds for all jet orders through `B`. Cauchy's estimate
on a ball of twice the response radius gives precisely this shape. -/
def LocalJetDecay (ξ : ℝ) (P : ℕ → ℤ[X]) (B : ℕ)
    (a κ : ℝ) (error : ℕ → ℝ) : Prop :=
  ∀ᶠ n : ℕ in atTop, ∀ x : ℝ,
    |x - ξ| ≤ Real.exp (-a * (n : ℝ)) → ∀ m : ℕ, m ≤ B →
      |(hasseDeriv m (P n)).eval₂ (Int.castRingHom ℝ) x| ≤
        Real.exp (-κ * (n : ℝ) ^ 2 + error n + a * (B : ℝ) * (n : ℝ))

theorem approximation_exponent_le_of_local_jets
    (ξ : ℝ) (P : ℕ → ℤ[X]) (B : ℕ) (degreeRate D a κ : ℝ) (error : ℕ → ℝ)
    (hdegreeRate : 0 < degreeRate) (ha : 0 < a) (hκ : 0 < κ)
    (hdegree : ∀ᶠ n : ℕ in atTop, ((P n).natDegree : ℝ) ≤ degreeRate * (n : ℝ) + D)
    (hjets : HasBoundedRationalJets P B)
    (herror : Tendsto (fun n : ℕ => error n / (n : ℝ) ^ 2) atTop (𝓝 0))
    (hdecay : LocalJetDecay ξ P B a κ error) :
    HasApproximationExponentLE ξ (degreeRate * a / κ) := by
  intro ν hν
  have hinterval : degreeRate / κ < ν / a := by
    apply (lt_div_iff₀ ha).mpr
    simpa only [div_mul_eq_mul_div] using hν
  obtain ⟨c, hc₁, hc₂⟩ := exists_between hinterval
  have hc : 0 < c := (div_pos hdegreeRate hκ).trans hc₁
  have hgap : degreeRate / c < κ := by
    apply (div_lt_iff₀ hc).mpr
    have h := (div_lt_iff₀ hκ).mp hc₁
    nlinarith
  have hac : a * c < ν := by
    have h := (lt_div_iff₀ ha).mp hc₂
    nlinarith
  have hstage := logarithmicStage_tendsto_atTop hc
  have hsmall := eventually_cleared_jet_exponent_neg degreeRate D a κ B error hc hgap herror
  have hradius := eventually_rpow_le_stage_radius hc hac
  filter_upwards [hsmall, hradius, hstage.eventually hdegree,
    hstage.eventually hdecay, eventually_ge_atTop (1 : ℕ)] with q hsmallq hradiusq hdegq hdecayq hq
  intro p
  by_contra hnot
  have hclose : |ξ - (p : ℝ) / (q : ℝ)| < (q : ℝ) ^ (-ν) := lt_of_not_ge hnot
  have hqpos : 0 < q := by omega
  have hqR : (0 : ℝ) < q := by exact_mod_cast hqpos
  have hlogq : 0 ≤ Real.log (q : ℝ) := Real.log_nonneg (by exact_mod_cast hq)
  let n := logarithmicStage c q
  obtain ⟨m, hm, hnonzero⟩ := hjets n p q hqpos
  have hlocal : |(p : ℝ) / (q : ℝ) - ξ| ≤ Real.exp (-a * (n : ℝ)) := by
    rw [abs_sub_comm]
    exact hclose.le.trans hradiusq
  have hupper := hdecayq ((p : ℝ) / (q : ℝ)) hlocal m hm
  have hlower := one_le_degree_scaled_abs_hasse_eval (P n) p q m
    (P n).natDegree hqpos le_rfl hnonzero
  have habs : 0 < |(hasseDeriv m (P n)).eval₂ (Int.castRingHom ℝ)
      ((p : ℝ) / (q : ℝ))| := abs_pos.mpr hnonzero
  have hlogupper := Real.log_le_log habs hupper
  rw [Real.log_exp] at hlogupper
  have hloglower := Real.log_nonneg hlower
  rw [Real.log_mul (pow_ne_zero _ hqR.ne') habs.ne', Real.log_pow] at hloglower
  have hdegcost := mul_le_mul_of_nonneg_right hdegq hlogq
  dsimp [n] at hlogupper hloglower
  nlinarith

/-- Bridge to Mathlib's existing exponent predicate. It includes arbitrary
multiplicative constants because an exponent strictly between `μ` and `ν`
absorbs such a constant. -/
theorem HasApproximationExponentLE.not_liouvilleWith {ξ μ ν : ℝ}
    (h : HasApproximationExponentLE ξ μ) (hν : μ < ν) :
    ¬ LiouvilleWith ν ξ := by
  intro hl
  obtain ⟨w, hμw, hwν⟩ := exists_between hν
  have hf := hl.frequently_lt_rpow_neg hwν
  have he := h w hμw
  obtain ⟨q, hq, p, _, hp⟩ := (he.and_frequently hf).exists
  exact (not_lt_of_ge (hq p)) hp

end Zeta3.Transfer

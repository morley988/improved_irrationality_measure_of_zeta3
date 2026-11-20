import Zeta3.Analysis.GammaKernel

/-!
# The explicit physical response Gamma

The response is defined by the actual square-root/logarithm expression used
in the numerical certificate.  Differentiation proves its monotonicity; this
is not left as an external numerical premise.  Identification with the later
weighted-polynomial coefficient estimate is a separate theorem.
-/

namespace Zeta3.Analysis

noncomputable section

def gammaNegativeIntegral (u a : ℝ) : ℝ :=
  a * Real.log (u ^ 2 - a ^ 2) + u * Real.log ((u + a) / (u - a)) - 2 * a

def physicalGammaBase (s₁ s₂ u : ℝ) : ℝ :=
  gammaNegativeIntegral u s₁ + gammaNegativeIntegral u s₂ - gammaNegativeIntegral u 1 - 2 +
    2 * s₁ * (1 - Real.log s₁) + 2 * s₂ * (1 - Real.log s₂)

def physicalGammaAtEndpoint (s₁ s₂ u b : ℝ) : ℝ :=
  physicalGammaBase s₁ s₂ u + 4 * physicalMass s₁ s₂ b * gammaLog u b +
    2 * u * (gammaArc u b - gammaAuxJ u 1 b + gammaAuxJ u s₁ b + gammaAuxJ u s₂ b)

def physicalGamma (s₁ s₂ u : ℝ) (h₁ : 0 < s₁) (h₂ : 0 < s₂) (v : ℝ) : ℝ :=
  physicalGammaAtEndpoint s₁ s₂ u (physicalEndpoint s₁ s₂ h₁ h₂ v)

/-- The literal quotient formula used for the auxiliary term in the checker. -/
def gammaJQuotient (u a b : ℝ) : ℝ :=
  Real.log ((gammaRadical u b + gammaRadical a b) / (u + a)) -
    (a / u) * Real.log ((u * gammaRadical a b + a * gammaRadical u b) /
      (a * (gammaRadical u b + u)))

def physicalGammaFormula (s₁ s₂ u b : ℝ) : ℝ :=
  physicalGammaBase s₁ s₂ u +
    4 * physicalMass s₁ s₂ b * Real.log ((u + gammaRadical u b) / b) +
    2 * u * (Real.log ((b + gammaRadical u b) / u) -
      gammaJQuotient u 1 b + gammaJQuotient u s₁ b + gammaJQuotient u s₂ b)

theorem physicalGammaAtEndpoint_eq_formula {s₁ s₂ u b : ℝ}
    (h₁ : 0 < s₁) (h₂ : 0 < s₂) (hu : 0 < u) (hb : 0 < b) :
    physicalGammaAtEndpoint s₁ s₂ u b = physicalGammaFormula s₁ s₂ u b := by
  unfold physicalGammaAtEndpoint physicalGammaFormula gammaJQuotient
  rw [gammaLog_formula hu hb, gammaArc_formula hu hb,
    gammaAuxJ_formula hu (by norm_num : (0 : ℝ) < 1),
    gammaAuxJ_formula hu h₁, gammaAuxJ_formula hu h₂]

theorem physicalGamma_eq_formula (s₁ s₂ u : ℝ)
    (h₁ : 0 < s₁) (h₂ : 0 < s₂) (hu : 0 < u) {v : ℝ} (hv : 0 < v) :
    physicalGamma s₁ s₂ u h₁ h₂ v =
      physicalGammaFormula s₁ s₂ u (physicalEndpoint s₁ s₂ h₁ h₂ v) :=
  physicalGammaAtEndpoint_eq_formula h₁ h₂ hu (physicalEndpoint_pos s₁ s₂ h₁ h₂ hv)

theorem physicalGamma_derivative_cancellation {s₁ s₂ u b : ℝ}
    (h₁ : 0 < s₁) (h₂ : 0 < s₂) (hu : 0 < u) (hb : 0 < b) :
    4 * physicalMass s₁ s₂ b * (-u / (b * gammaRadical u b)) +
      2 * u * (1 / gammaRadical u b -
        b / (gammaRadical u b * (gammaRadical 1 b + 1)) +
        b / (gammaRadical u b * (gammaRadical s₁ b + s₁)) +
        b / (gammaRadical u b * (gammaRadical s₂ b + s₂))) = 0 := by
  have hw := gammaRadical_pos (b := b) hu
  rw [gammaAuxJ_derivative_rewrite hu (by norm_num : (0 : ℝ) < 1) hb,
    gammaAuxJ_derivative_rewrite hu h₁ hb, gammaAuxJ_derivative_rewrite hu h₂ hb]
  unfold physicalMass gammaRadical
  norm_num only [one_pow]
  field_simp
  ring

theorem physicalGammaAtEndpoint_hasDerivAt {s₁ s₂ u b : ℝ}
    (h₁ : 0 < s₁) (h₂ : 0 < s₂) (hu : 0 < u) (hb : 0 < b) :
    HasDerivAt (physicalGammaAtEndpoint s₁ s₂ u)
      (4 * physicalMassSlope s₁ s₂ b * gammaLog u b) b := by
  have dm := physicalMass_hasDerivAt (b := b) h₁ h₂
  have dlog := gammaLog_hasDerivAt hu hb
  have darc := gammaArc_hasDerivAt hu hb
  have dJone := gammaAuxJ_hasDerivAt (b := b) hu (by norm_num : (0 : ℝ) < 1)
  have dJ₁ := gammaAuxJ_hasDerivAt (b := b) hu h₁
  have dJ₂ := gammaAuxJ_hasDerivAt (b := b) hu h₂
  have d := (((dm.const_mul 4).mul dlog).const_add (physicalGammaBase s₁ s₂ u)).add
    ((((darc.sub dJone).add dJ₁).add dJ₂).const_mul (2 * u))
  have hcancel := physicalGamma_derivative_cancellation h₁ h₂ hu hb
  convert! d using 1
  linear_combination -hcancel

theorem physicalGamma_hasDerivAt (s₁ s₂ u : ℝ)
    (h₁ : 0 < s₁) (h₂ : 0 < s₂) (hu : 0 < u) {v : ℝ} (hv : 0 < v) :
    HasDerivAt (physicalGamma s₁ s₂ u h₁ h₂)
      (4 * gammaLog u (physicalEndpoint s₁ s₂ h₁ h₂ v)) v := by
  have hb := physicalEndpoint_pos s₁ s₂ h₁ h₂ hv
  have hd := physicalMassSlope_pos h₁ h₂ hb
  have d := (physicalGammaAtEndpoint_hasDerivAt h₁ h₂ hu hb).comp v
    (physicalEndpoint_hasDerivAt s₁ s₂ h₁ h₂ hv)
  convert! d using 1
  field_simp

theorem physicalGamma_continuousOn (s₁ s₂ u : ℝ)
    (h₁ : 0 < s₁) (h₂ : 0 < s₂) (hu : 0 < u) :
    ContinuousOn (physicalGamma s₁ s₂ u h₁ h₂) (Set.Ioi 0) := by
  intro v hv
  exact (physicalGamma_hasDerivAt s₁ s₂ u h₁ h₂ hu hv).continuousAt.continuousWithinAt

theorem physicalGamma_strictMonoOn (s₁ s₂ u : ℝ)
    (h₁ : 0 < s₁) (h₂ : 0 < s₂) (hu : 0 < u) :
    StrictMonoOn (physicalGamma s₁ s₂ u h₁ h₂) (Set.Ioi 0) := by
  apply strictMonoOn_of_deriv_pos (convex_Ioi 0)
    (physicalGamma_continuousOn s₁ s₂ u h₁ h₂ hu)
  intro v hv
  have hv' : 0 < v := by simpa only [interior_Ioi, Set.mem_Ioi] using hv
  rw [(physicalGamma_hasDerivAt s₁ s₂ u h₁ h₂ hu hv').deriv]
  exact mul_pos (by norm_num) (gammaLog_pos hu (physicalEndpoint_pos s₁ s₂ h₁ h₂ hv'))

end

end Zeta3.Analysis

import Zeta3.Transfer.Cauchy
import Zeta3.Transfer.Multiplicity

/-!
# Determinant response and the generic quantitative transfer

The response function is the actual multiplicative ratio in an explicitly
assumed identity. The two asymptotic bounds and root-multiplicity bound are
ordinary mathematical hypotheses. They are intentionally separate from any
finite numerical-evidence interface.
-/

noncomputable section
namespace Zeta3.Transfer
open Filter Polynomial
open scoped Topology

theorem localPolynomialDecay_of_response
    (ξ : ℝ) (P : ℕ → ℤ[X]) (response : ℕ → ℂ → ℂ)
    (a ε ρ : ℝ) (errorSmall errorResponse : ℕ → ℝ)
    (hidentity : ∀ (n : ℕ) (h : ℂ),
      (P n).eval₂ (Int.castRingHom ℂ) ((ξ : ℂ) + h) =
        (P n).eval₂ (Int.castRingHom ℂ) (ξ : ℂ) * response n h)
    (hsmall : ∀ᶠ n : ℕ in atTop,
      ‖(P n).eval₂ (Int.castRingHom ℂ) (ξ : ℂ)‖ ≤
        Real.exp (-ε * (n : ℝ) ^ 2 + errorSmall n))
    (hresponse : ∀ᶠ n : ℕ in atTop, ∀ h : ℂ,
      ‖h‖ ≤ 2 * Real.exp (-a * (n : ℝ)) →
        ‖response n h‖ ≤ Real.exp (ρ * (n : ℝ) ^ 2 + errorResponse n)) :
    LocalPolynomialDecay ξ P a (ε - ρ) (fun n => errorSmall n + errorResponse n) := by
  filter_upwards [hsmall, hresponse] with n hn hresp
  intro z hz
  have hp := hidentity n (z - (ξ : ℂ))
  have hc : (ξ : ℂ) + (z - (ξ : ℂ)) = z := by ring
  rw [hc] at hp
  rw [hp, norm_mul]
  calc
    ‖(P n).eval₂ (Int.castRingHom ℂ) (ξ : ℂ)‖ * ‖response n (z - (ξ : ℂ))‖ ≤
        Real.exp (-ε * (n : ℝ) ^ 2 + errorSmall n) *
          Real.exp (ρ * (n : ℝ) ^ 2 + errorResponse n) :=
      mul_le_mul hn (hresp _ hz) (norm_nonneg _) (Real.exp_pos _).le
    _ = Real.exp (-(ε - ρ) * (n : ℝ) ^ 2 +
        (errorSmall n + errorResponse n)) := by
      rw [← Real.exp_add]
      congr 1
      ring

/-- The complete abstract bounded-multiplicity response transfer. To apply
it to the cubic determinant, its hypotheses must be proved for that exact
polynomial family and response, using the externally certified finite
constants only at their proper numerical interfaces. -/
theorem approximation_exponent_le_of_response
    (ξ : ℝ) (P : ℕ → ℤ[X]) (response : ℕ → ℂ → ℂ)
    (B : ℕ) (degreeRate D a ε ρ : ℝ) (errorSmall errorResponse : ℕ → ℝ)
    (hdegreeRate : 0 < degreeRate) (ha : 0 < a) (hgap : ρ < ε)
    (hdegree : ∀ᶠ n : ℕ in atTop, ((P n).natDegree : ℝ) ≤ degreeRate * (n : ℝ) + D)
    (hnonzero : ∀ n, P n ≠ 0)
    (hmult : ∀ (n : ℕ) (p : ℤ) (q : ℕ), 0 < q →
      ((P n).map (Int.castRingHom ℝ)).rootMultiplicity ((p : ℝ) / (q : ℝ)) ≤ B)
    (herrorSmall : Tendsto (fun n : ℕ => errorSmall n / (n : ℝ) ^ 2) atTop (𝓝 0))
    (herrorResponse : Tendsto (fun n : ℕ => errorResponse n / (n : ℝ) ^ 2) atTop (𝓝 0))
    (hidentity : ∀ (n : ℕ) (h : ℂ),
      (P n).eval₂ (Int.castRingHom ℂ) ((ξ : ℂ) + h) =
        (P n).eval₂ (Int.castRingHom ℂ) (ξ : ℂ) * response n h)
    (hsmall : ∀ᶠ n : ℕ in atTop,
      ‖(P n).eval₂ (Int.castRingHom ℂ) (ξ : ℂ)‖ ≤
        Real.exp (-ε * (n : ℝ) ^ 2 + errorSmall n))
    (hresponse : ∀ᶠ n : ℕ in atTop, ∀ h : ℂ,
      ‖h‖ ≤ 2 * Real.exp (-a * (n : ℝ)) →
        ‖response n h‖ ≤ Real.exp (ρ * (n : ℝ) ^ 2 + errorResponse n)) :
    HasApproximationExponentLE ξ (degreeRate * a / (ε - ρ)) := by
  apply approximation_exponent_le_of_local_polynomial_decay ξ P B degreeRate D a (ε - ρ)
    (fun n => errorSmall n + errorResponse n) hdegreeRate ha (sub_pos.mpr hgap) hdegree
    (hasBoundedRationalJets_of_rootMultiplicity_le P B hnonzero hmult)
  · simpa only [add_div, add_zero] using herrorSmall.add herrorResponse
  · exact localPolynomialDecay_of_response ξ P response a ε ρ errorSmall errorResponse
      hidentity hsmall hresponse

end Zeta3.Transfer

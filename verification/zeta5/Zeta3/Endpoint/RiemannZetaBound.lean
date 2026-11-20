import Zeta3.Endpoint.CertifiedResponseRate

/-! Standard Riemann-zeta statements, with the remaining arithmetic input explicit. -/

noncomputable section
namespace Zeta3.Endpoint
open Zeta3.Transfer Filter

theorem riemannZeta_three_exponent_le_of_arithmetic_rate
    (hfinite : Certificate.FiniteNumericalEvidence) (harithmetic : ActualArithmeticRate) :
    HasApproximationExponentLE (riemannZeta 3).re Parameters.target := by
  have h := approximation_exponent_le_target_of_arithmetic_rate hfinite harithmetic
  rwa [Zeta5.Endpoint.realZeta_eq_re 3 (by norm_num)] at h

theorem riemannZeta_three_irrational_of_arithmetic_rate
    (hfinite : Certificate.FiniteNumericalEvidence) (harithmetic : ActualArithmeticRate) :
    Irrational (riemannZeta 3).re :=
  (riemannZeta_three_exponent_le_of_arithmetic_rate hfinite harithmetic).irrational

theorem riemannZeta_three_rational_separation_of_arithmetic_rate
    (hfinite : Certificate.FiniteNumericalEvidence) (harithmetic : ActualArithmeticRate) :
    ∀ ν : ℝ, Parameters.target<ν → ∃ Q : ℕ, ∀ q : ℕ, Q≤q → ∀ p : ℤ,
      (q:ℝ)^(-ν)≤|(riemannZeta 3).re-(p:ℝ)/(q:ℝ)| := by
  intro ν hν
  exact eventually_atTop.mp (riemannZeta_three_exponent_le_of_arithmetic_rate hfinite harithmetic ν hν)

end Zeta3.Endpoint

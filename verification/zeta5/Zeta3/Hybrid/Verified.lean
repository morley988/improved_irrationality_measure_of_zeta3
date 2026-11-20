import Zeta3.Endpoint.FiniteEvidence
import Zeta3.Hybrid.ExternalArb
import Zeta3.Hybrid.ExternalArithmetic

/-!
# The hybrid irrationality-exponent bound for the ordinary zeta value

The only nonstandard assumptions are the explicitly named external finite
numerical assertions. All mathematical hypotheses have been discharged.
The axiom report at the end exposes the trust boundary of this theorem.
-/

noncomputable section
namespace Zeta3.Hybrid

theorem zeta3_irrationality_exponent_bound :
    Transfer.HasApproximationExponentLE (riemannZeta 3).re Parameters.target :=
  Endpoint.riemannZeta_three_exponent_le_of_finiteEvidence
    ExternalArb.finiteEvidence ExternalArithmetic.finiteEvidence

theorem zeta3_irrational : Irrational (riemannZeta 3).re :=
  zeta3_irrationality_exponent_bound.irrational

theorem zeta3_rational_separation :
    ∀ ν : ℝ, Parameters.target<ν → ∃ Q : ℕ, ∀ q : ℕ, Q≤q → ∀ p : ℤ,
      (q:ℝ)^(-ν)≤|(riemannZeta 3).re-(p:ℝ)/(q:ℝ)| :=
  Endpoint.riemannZeta_three_rational_separation_of_finiteEvidence
    ExternalArb.finiteEvidence ExternalArithmetic.finiteEvidence

theorem target_strictly_below_4974 : Parameters.target<(2487/500:ℝ) :=
  Parameters.target_lt_4974

end Zeta3.Hybrid

#print axioms Zeta3.Hybrid.zeta3_irrationality_exponent_bound
#print axioms Zeta3.Hybrid.zeta3_irrational
#print axioms Zeta3.Hybrid.zeta3_rational_separation

import Zeta5.Arithmetic.LocalRestriction
import Zeta3.Arithmetic.LocalQuotient

/-! Cubic central-quotient bounds, with the extra prime power on the
actual maximal-class coefficient restriction kernel. -/
noncomputable section
namespace Zeta3.Arithmetic
open Polynomial Finset OddZeta.FourValue Zeta5.Construction Zeta3.Construction
open Zeta5.Arithmetic
variable {p : ℕ} [Fact p.Prime]

theorem normalizedCentralQuotient_momentNumerator_natDegree_le (N : ℕ) (g : ℚ[X]) :
    (bernoulliMomentNumerator (C ((N.factorial : ℚ) ^ 2) * centralQuotient N g)).natDegree ≤
      2 * (max g.natDegree N - N) + 3 := by
  apply (bernoulliMomentNumerator_natDegree_le _).trans
  have h := (natDegree_C_mul_le ((N.factorial : ℚ) ^ 2) (centralQuotient N g)).trans
    (centralQuotient_natDegree_le N g)
  omega

theorem centralQuotient_moment_bound {N : ℕ} {g : ℚ[X]}
    (hp : 2 < p) (hg : SquareValuedLower p 0 g)
    (hsmall : 2 * max g.natDegree N + 4 < p ^ 2) :
    PadicLower p (-3 - ((2 * (N % p) / p : ℕ) : ℤ))
      (Zeta3.Construction.polynomialMoment (C ((N.factorial : ℚ) ^ 2) * centralQuotient N g)) := by
  have hmax : N ≤ max g.natDegree N := le_max_right _ _
  apply normalized_quotient_moment_lower hp
    ((Fact.out : p.Prime).mod_two_eq_one_iff_ne_two.mpr (by omega))
    (by omega) (centralTail_integerValued hg N)
    (centralTail_negativeSquare_natDegree_le N g) (by omega)
    (normalizedCentralQuotient_momentNumerator_natDegree_le N g) (by omega)
    (centralTail_eq_denominator_mul_quotient N g)

theorem centralQuotient_moment_bound_on_kernel {N : ℕ} {g : ℚ[X]}
    (hp : 2 < p) (hg : SquareValuedLower p 0 g)
    (hsmall : 2 * max g.natDegree N + 4 < p ^ 2)
    (hkernel : ∀ c ∈ maximalReflectedClasses N p,
      PolynomialPadicLower p 1 (g.comp ((localAffine p c) ^ 2))) :
    PadicLower p (-2 - ((2 * (N % p) / p : ℕ) : ℤ))
      (Zeta3.Construction.polynomialMoment (C ((N.factorial : ℚ) ^ 2) * centralQuotient N g)) := by
  have hmax : N ≤ max g.natDegree N := le_max_right _ _
  apply normalized_quotient_moment_lower_on_kernel hp
    ((Fact.out : p.Prime).mod_two_eq_one_iff_ne_two.mpr (by omega))
    (by omega) (centralTail_integerValued hg N)
    (centralTail_negativeSquare_natDegree_le N g) (by omega)
    (fun c hc => centralTail_maximal_local_gain hg (by omega) hc (hkernel c hc))
    (normalizedCentralQuotient_momentNumerator_natDegree_le N g) (by omega)
    (centralTail_eq_denominator_mul_quotient N g)

end Zeta3.Arithmetic

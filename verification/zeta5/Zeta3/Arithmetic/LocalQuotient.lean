import Zeta5.Arithmetic.LocalQuotient
import Zeta3.Arithmetic.BernoulliMoments

/-! Cubic moment bounds for the actual normalized local quotient.
The denominator and integer-valued quotient arguments are moment-independent.
The cubic first derivative loses two further prime powers. -/
noncomputable section
namespace Zeta3.Arithmetic
open Polynomial Finset OddZeta.FourValue Zeta5.Construction Zeta3.Construction
open Zeta5.Arithmetic
variable {p : ℕ} [Fact p.Prime]

theorem normalized_quotient_moment_lower {N L M : ℕ} {F Q : ℚ[X]}
    (hp : 2 < p) (hodd : p % 2 = 1) (hN : N < p ^ 2)
    (hF : IntegerValuedAt p (F.comp (-(X ^ 2))))
    (hL : (F.comp (-(X ^ 2))).natDegree ≤ L) (hLp : L < p ^ 2)
    (hM : (bernoulliMomentNumerator (C ((N.factorial : ℚ) ^ 2) * Q)).natDegree ≤ M)
    (hMp : M + 1 < p ^ 2) (heq : F = denominator N * Q) :
    PadicLower p (-3 - ((2 * (N % p) / p : ℕ) : ℤ))
      (Zeta3.Construction.polynomialMoment (C ((N.factorial : ℚ) ^ 2) * Q)) := by
  have h := polynomialMoment_padicLower_of_integerValuedNumerator hp
    (bernoulliMomentNumerator_integerValued (normalized_quotient_integerValued hodd hN hF hL hLp heq))
    hM hMp
  convert h using 1
  omega

theorem normalized_quotient_moment_lower_on_kernel {N L M : ℕ} {F Q : ℚ[X]}
    (hp : 2 < p) (hodd : p % 2 = 1) (hN : N < p ^ 2)
    (hF : IntegerValuedAt p (F.comp (-(X ^ 2))))
    (hL : (F.comp (-(X ^ 2))).natDegree ≤ L) (hLp : L < p ^ 2)
    (hkernel : ∀ c ∈ maximalReflectedClasses N p,
      PolynomialPadicLower p 1 (F.comp (-(localAffine p c) ^ 2)))
    (hM : (bernoulliMomentNumerator (C ((N.factorial : ℚ) ^ 2) * Q)).natDegree ≤ M)
    (hMp : M + 1 < p ^ 2) (heq : F = denominator N * Q) :
    PadicLower p (-2 - ((2 * (N % p) / p : ℕ) : ℤ))
      (Zeta3.Construction.polynomialMoment (C ((N.factorial : ℚ) ^ 2) * Q)) := by
  have h := polynomialMoment_padicLower_of_integerValuedNumerator hp
    (bernoulliMomentNumerator_integerValued
      (normalized_quotient_integerValued_on_kernel hodd hN hF hL hLp hkernel heq)) hM hMp
  convert h using 1
  omega

end Zeta3.Arithmetic

import Zeta3.Arithmetic.MaximalSecondQuotient
import Zeta3.Arithmetic.BernoulliReduction
import Zeta3.Arithmetic.LocalFunctional

/-! The maximal and zero-class proper residues and the retained constant
quotient disappear in the second layer. The maximal local Bernoulli term
also vanishes, with its coefficient precision explicitly retained. -/
noncomputable section
namespace Zeta3.Arithmetic
open Polynomial Finset OddZeta.FourValue Zeta5.Arithmetic Zeta5.Construction
variable {p : ℕ} [Fact p.Prime]

theorem second_scaled_retained_quotient_vanish {N : ℕ} {g : ℚ[X]}
    (hp : 2 < p) (hg : SquareValuedLower p 0 g) (hsmall : 2 * N < p ^ 2) :
    PadicLower p 1 ((p : ℚ) ^ (2 + 2 * (N % p) / p) *
      Zeta3.Construction.polynomialMoment
        ((C ((N.factorial : ℚ) ^ 2) * (centralExpansion g N).comp (-X)) / denominator N)) := by
  have h := (prime_power_padicLower (p := p) (2 + 2 * (N % p) / p)).mul
    (normalized_centralExpansion_quotient_moment_bound hp hg hsmall)
  convert h using 1
  push_cast
  ring

theorem second_scaled_zero_residue_vanish {N i : ℕ} {g : ℚ[X]}
    (hp : 2 < p) (hi : 0 < i) (hiN : i ≤ N) (hpi : p ∣ i)
    (hsmall : 2 * N < p ^ 2) (hg : PadicLower p 0 (g.eval ((i : ℚ) ^ 2))) :
    PolynomialPadicLower p 1
      (C ((p : ℚ) ^ (2 + 2 * (N % p) / p)) * normalizedResidue N g i) := by
  have h := (PolynomialPadicLower.constant
    (prime_power_padicLower (p := p) (2 + 2 * (N % p) / p))).mul
    (normalizedResidue_zero_class_integral hp hi hiN hpi hsmall hg)
  have heps : 0 ≤ ((2 * (N % p) / p : ℕ) : ℤ) := Int.natCast_nonneg _
  exact h.mono (by omega)

theorem second_scaled_maximal_residue_vanish {N c i : ℕ} {g : ℚ[X]}
    (hp : 2 < p) (hc : c ∈ maximalReflectedClasses N p)
    (hi : i ∈ reflectedNodes N p c) (hsmall : 2 * N < p ^ 2)
    (hkernel : PolynomialPadicLower p 2 (g.comp ((localAffine p c) ^ 2))) :
    PolynomialPadicLower p 1
      (C ((p : ℚ) ^ (2 + 2 * (N % p) / p)) * normalizedResidue N g i) := by
  obtain ⟨hci, he⟩ := mem_filter.mp hc
  obtain ⟨hc0, hch⟩ := mem_Icc.mp hci
  have hgi := square_local_eval_at_reflected hc0 (by omega) hi hkernel
  have h := normalizedResidue_reflected_bound hp hc0 (by omega) hi hsmall hgi
  have hs := (PolynomialPadicLower.constant
    (prime_power_padicLower (p := p) (2 + 2 * (N % p) / p))).mul h
  rw [he] at hs
  convert hs using 1
  push_cast
  ring

def scaledQuotientNumerator (N p : ℕ) (g : ℚ[X]) : ℚ[X] :=
  C ((p : ℚ) ^ (2 * (N % p) / p)) *
    bernoulliMomentNumerator (C ((N.factorial : ℚ) ^ 2) * centralQuotient N g)

theorem scaledQuotientNumerator_integerValued {N : ℕ} {g : ℚ[X]}
    (hodd : p % 2 = 1) (hg : SquareValuedLower p 0 g)
    (hsmall : 2 * max g.natDegree N < p ^ 2)
    (hkernel : ∀ c ∈ maximalReflectedClasses N p,
      PolynomialPadicLower p 1 (g.comp ((localAffine p c) ^ 2))) :
    IntegerValuedAt p (scaledQuotientNumerator N p g) := by
  have hN : N ≤ max g.natDegree N := le_max_right _ _
  have hQ := normalized_quotient_integerValued_on_kernel hodd (by omega : N < p ^ 2)
    (centralTail_integerValued hg N) (centralTail_negativeSquare_natDegree_le N g) hsmall
    (fun c hc => centralTail_maximal_local_gain hg (by omega) hc (hkernel c hc))
    (centralTail_eq_denominator_mul_quotient N g)
  have hB := Zeta3.Arithmetic.bernoulliMomentNumerator_integerValued hQ
  intro z
  have h := (prime_power_padicLower (p := p) (2 * (N % p) / p)).mul (hB z)
  simpa only [scaledQuotientNumerator, eval_mul, eval_C, add_neg_cancel] using h

theorem scaledQuotientNumerator_maximal_vanish {N c L : ℕ} {g : ℚ[X]}
    (hp : 2 < p) (hg : SquareValuedLower p 0 g)
    (hsmall : 2 * max g.natDegree N < p ^ 2)
    (hkernel : ∀ c ∈ maximalReflectedClasses N p,
      PolynomialPadicLower p 1 (g.comp ((localAffine p c) ^ 2)))
    (hc : c ∈ maximalReflectedClasses N p)
    (hproduct : PolynomialPadicLower p 2 (g.comp ((localAffine p c) ^ 2)))
    (hL : (scaledQuotientNumerator N p g).natDegree ≤ L) (hLp : L < p ^ 2)
    (hE : L / p + 3 ≤ p) :
    PadicLower p 1 (bernoulliFunctional
      ((scaledQuotientNumerator N p g).comp (localAffine p c)).derivative) := by
  have hN : N ≤ max g.natDegree N := le_max_right _ _
  obtain ⟨a, ha, hQa⟩ := centralQuotient_maximal_second_constant hg (by omega) hc hproduct
  let Q := C ((p : ℚ) ^ (2 * (N % p) / p)) *
    (C ((N.factorial : ℚ) ^ 2) * centralQuotient N g).comp (-(localAffine p c) ^ 2)
  have hQ : PolynomialPadicLower p 0 Q := by
    have h := (hQa.mono (by norm_num : (0 : ℤ) ≤ 1)).add (PolynomialPadicLower.constant ha)
    simpa only [sub_add_cancel] using h
  have hlocal := localCubicProduct_constant_reduction (p := p) (c : ℤ) hQ ha hQa
  have he : (scaledQuotientNumerator N p g).comp (localAffine p c) = (localAffine p c) ^ 3 * Q := by
    simp only [scaledQuotientNumerator, bernoulliMomentNumerator, mul_comp, C_comp,
      pow_comp, X_comp, comp_assoc, neg_comp, Q]
    ring
  have hIv := scaledQuotientNumerator_integerValued
    ((Fact.out : p.Prime).mod_two_eq_one_iff_ne_two.mpr (by omega)) hg hsmall hkernel
  apply bernoulliFunctional_derivative_zero_of_constant_reduction _ (L / p) hp hE
    (fun j => integerValuedAt_local_coeff_precision hIv hL hLp (c : ℤ) j)
  intro j hj
  rw [he]
  have h := hlocal j
  simpa only [coeff_sub, coeff_C, if_neg (show j ≠ 0 by omega), sub_zero] using h

end Zeta3.Arithmetic

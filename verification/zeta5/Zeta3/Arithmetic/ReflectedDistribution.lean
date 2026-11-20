import Zeta3.Arithmetic.LocalDistribution
import Zeta3.Arithmetic.SecondVanishing
import Zeta3.Arithmetic.BernoulliReflection

/-! Exact pairing of the nonzero Bernoulli residue classes and the
vanishing zero class for the actual cubic quotient. -/
noncomputable section
namespace Zeta3.Arithmetic
open Polynomial Finset OddZeta.FourValue Zeta5.Arithmetic Zeta5.Construction
variable {p : ℕ} [Fact p.Prime]

theorem bernoulliMomentNumerator_odd (P : ℚ[X]) :
    (bernoulliMomentNumerator P).comp (-X) = -bernoulliMomentNumerator P := by
  simp only [bernoulliMomentNumerator, mul_comp, pow_comp, X_comp, comp_assoc, neg_comp]
  have he : (-(X : ℚ[X])) ^ 2 = X ^ 2 := by ring
  rw [he]
  ring

theorem scaledQuotientNumerator_odd (N p : ℕ) (g : ℚ[X]) :
    (scaledQuotientNumerator N p g).comp (-X) = -scaledQuotientNumerator N p g := by
  rw [scaledQuotientNumerator, mul_comp, C_comp, bernoulliMomentNumerator_odd]
  ring

theorem localAffine_reflection (p : ℕ) (c : ℤ) :
    -((localAffine p c).comp localReflection) = localAffine p ((p : ℤ) - c) := by
  simp only [localAffine, add_comp, C_comp, mul_comp, X_comp, localReflection, Int.cast_sub,
    Int.cast_natCast, C_sub]
  ring

theorem bernoulliDerivative_local_reflection (P : ℚ[X]) (hP : P.comp (-X) = -P)
    (p : ℕ) (c : ℤ) :
    bernoulliFunctional (P.comp (localAffine p ((p : ℤ) - c))).derivative =
      bernoulliFunctional (P.comp (localAffine p c)).derivative := by
  have hid : P.comp (localAffine p ((p : ℤ) - c)) = -(P.comp (localAffine p c)).comp localReflection := by
    calc
      _ = (P.comp (-X)).comp ((localAffine p c).comp localReflection) := by
        rw [comp_assoc, neg_comp, X_comp, localAffine_reflection]
      _ = _ := by rw [hP, neg_comp, comp_assoc]
  rw [hid, derivative_neg, derivative_comp_reflection, neg_neg, bernoulliFunctional_reflection]

theorem sum_odd_reflected (p : ℕ) (hodd : p % 2 = 1) (f : ℕ → ℚ)
    (hreflection : ∀ c, 0 < c → c < p → f (p - c) = f c) :
    (∑ c ∈ range p, f c) = f 0 + 2 * ∑ c ∈ Icc 1 ((p - 1) / 2), f c := by
  let n := (p - 1) / 2
  have hn : 2 * n + 1 = p := by dsimp [n]; omega
  have hsplit := sum_range_add_sum_Ico f (by omega : n + 1 ≤ p)
  have hlow := sum_range_add_sum_Ico f (by omega : 1 ≤ n + 1)
  have hhigh : (∑ c ∈ Ico (n + 1) p, f c) = ∑ c ∈ Ico 1 (n + 1), f c := by
    calc
      _ = ∑ c ∈ Ico (n + 1) p, f (p - c) := by
        apply sum_congr rfl
        intro c hc
        exact (hreflection c (by have := mem_Ico.mp hc; omega) (mem_Ico.mp hc).2).symm
      _ = ∑ c ∈ Ico (p + 1 - p) (p + 1 - (n + 1)), f c :=
        sum_Ico_reflect f (n + 1) (m := p) (n := p) (by omega)
      _ = _ := by
        have ha : p + 1 - p = 1 := by omega
        have hb : p + 1 - (n + 1) = n + 1 := by omega
        rw [ha, hb]
  have hset : Ico 1 (n + 1) = Icc 1 n := by ext c; simp [Nat.lt_succ_iff]
  rw [hhigh] at hsplit
  rw [hset] at hsplit hlow
  simp only [sum_range_one] at hlow
  change (∑ c ∈ range p, f c) = f 0 + 2 * ∑ c ∈ Icc 1 n, f c
  linarith

theorem bernoulliDerivative_sum_reflected (P : ℚ[X]) (hP : P.comp (-X) = -P)
    (hodd : p % 2 = 1) :
    (∑ c ∈ range p, bernoulliFunctional (P.comp (localAffine p (c : ℤ))).derivative) =
      bernoulliFunctional (P.comp (localAffine p 0)).derivative +
        2 * ∑ c ∈ Icc 1 ((p - 1) / 2),
          bernoulliFunctional (P.comp (localAffine p (c : ℤ))).derivative := by
  apply sum_odd_reflected p hodd
  intro c hc hcp
  have h := bernoulliDerivative_local_reflection P hP p (c : ℤ)
  simpa only [Nat.cast_sub hcp.le, Int.cast_natCast] using h

theorem bernoulliFunctional_derivative_weighted_lower (P : ℚ[X]) (w : ℤ)
    (hp : 2 < p) (hP : PolynomialPadicLower p w P) :
    PadicLower p (w - 1) (bernoulliFunctional P.derivative) := by
  rw [bernoulliFunctional_derivative_eq_sum]
  apply padicLower_sum
  intro j hj
  have h := ((hP j).mul (padicLower_nat (p := p) j)).mul (bernoulli_padicLower (p := p) (j - 1) hp)
  convert h using 1
  omega

theorem scaledQuotientNumerator_zero_class_vanish {N : ℕ} {g : ℚ[X]}
    (hp : 2 < p) (hg : SquareValuedLower p 0 g)
    (hsmall : 2 * max g.natDegree N < p ^ 2) :
    PadicLower p 1 (bernoulliFunctional
      ((scaledQuotientNumerator N p g).comp (localAffine p 0)).derivative) := by
  have hN : N ≤ max g.natDegree N := le_max_right _ _
  have hF : PolynomialPadicLower p 0 ((centralTail N g).comp (-(localAffine p 0) ^ 2)) := by
    have h := integerValuedAt_local_integral (centralTail_integerValued hg N)
      (centralTail_negativeSquare_natDegree_le N g) hsmall (0 : ℤ)
    simpa only [comp_assoc, neg_comp, pow_comp, X_comp] using h
  have hQ := normalized_quotient_comp_lower (by omega : N < p ^ 2) hF
    (centralTail_eq_denominator_mul_quotient N g)
  rw [physicalLocalMultiplicity_zero] at hQ
  have hQint : PolynomialPadicLower p 0
      ((C ((N.factorial : ℚ) ^ 2) * centralQuotient N g).comp (-(localAffine p 0) ^ 2)) := by
    convert hQ using 1
    push_cast
    ring
  have hpow := (prime_power_padicLower (p := p) (2 * (N % p) / p)).mono (Int.natCast_nonneg _)
  have hscaled := (PolynomialPadicLower.constant hpow).mul hQint
  have hX3 : PolynomialPadicLower p 3 ((localAffine p 0) ^ 3) := by
    have hp1 : PadicLower p 1 (p : ℚ) := by simpa using prime_power_padicLower (p := p) 1
    have hx := (PolynomialPadicLower.constant hp1).mul (polynomialPadicLower_X (p := p))
    simpa [localAffine] using hx.pow 3
  have hwhole := hX3.mul hscaled
  have he : (scaledQuotientNumerator N p g).comp (localAffine p 0) =
      (localAffine p 0) ^ 3 * (C ((p : ℚ) ^ (2 * (N % p) / p)) *
        (C ((N.factorial : ℚ) ^ 2) * centralQuotient N g).comp (-(localAffine p 0) ^ 2)) := by
    simp only [scaledQuotientNumerator, bernoulliMomentNumerator, mul_comp, C_comp,
      pow_comp, X_comp, comp_assoc, neg_comp]
    ring
  have hprec : PolynomialPadicLower p 3 ((scaledQuotientNumerator N p g).comp (localAffine p 0)) := by
    rw [he]
    simpa only [add_zero, zero_add] using hwhole
  exact (bernoulliFunctional_derivative_weighted_lower _ 3 hp hprec).mono (by norm_num)

end Zeta3.Arithmetic

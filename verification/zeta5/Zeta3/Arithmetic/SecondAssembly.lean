import Zeta3.Arithmetic.LocalSecondForm

/-! Global assembly of the second local residue form. The zero class,
maximal classes and retained interpolation quotient are proved to vanish;
the only surviving terms are the stated nonmaximal feature forms. -/
noncomputable section
namespace Zeta3.Arithmetic
open Polynomial Finset OddZeta.FourValue Zeta5.Arithmetic Zeta5.Construction
variable {p : ℕ} [Fact p.Prime]

def secondClassContribution (N p c : ℕ) (g : ℚ[X]) : ℚ :=
  (p : ℚ) ^ (2 + 2 * (N % p) / p) *
    (∑ i ∈ reflectedNodes N p c, (normalizedResidue N g i).coeff 0) +
  bernoulliFunctional ((scaledQuotientNumerator N p g).comp (localAffine p c)).derivative

def secondZeroContribution (N p : ℕ) (g : ℚ[X]) : ℚ :=
  (1 / 2) * bernoulliFunctional
    ((scaledQuotientNumerator N p g).comp (localAffine p 0)).derivative +
  (p : ℚ) ^ (2 + 2 * (N % p) / p) *
    Zeta3.Construction.polynomialMoment
      ((C ((N.factorial : ℚ) ^ 2) * (centralExpansion g N).comp (-X)) / denominator N) +
  (p : ℚ) ^ (2 + 2 * (N % p) / p) *
    ∑ i ∈ zeroClassNodes N p, (normalizedResidue N g i).coeff 0

theorem normalizedCentralFunctional_second_decomposition (N : ℕ) (g : ℚ[X])
    (hodd : p % 2 = 1) :
    (p : ℚ) ^ (2 + 2 * (N % p) / p) * (normalizedCentralFunctional N g).coeff 0 =
      secondZeroContribution N p g +
        ∑ c ∈ Icc 1 ((p - 1) / 2), secondClassContribution N p c g := by
  have hp : 0 < p := (Fact.out : p.Prime).pos
  have hd := polynomialMoment_scaled_distribution p (2 * (N % p) / p) hp
    (C ((N.factorial : ℚ) ^ 2) * centralQuotient N g)
  have hform : ∀ c : ℕ,
      C ((p : ℚ) ^ (2 * (N % p) / p)) *
        (bernoulliMomentNumerator (C ((N.factorial : ℚ) ^ 2) * centralQuotient N g)).comp
          (localAffine p c) = (scaledQuotientNumerator N p g).comp (localAffine p c) := by
    intro c
    simp only [scaledQuotientNumerator, mul_comp, C_comp]
  simp_rw [hform] at hd
  rw [bernoulliDerivative_sum_reflected _ (scaledQuotientNumerator_odd N p g) hodd] at hd
  rw [normalizedCentralFunctional_decomposition]
  simp only [coeff_add, coeff_C_zero, finsetSum_coeff]
  rw [sum_range_succ_eq_Ioc N (fun i => (normalizedResidue N g i).coeff 0),
    sum_reflected_partition N p hp hodd]
  unfold secondZeroContribution secondClassContribution
  rw [sum_add_distrib, ← mul_sum]
  linear_combination hd

theorem secondZeroContribution_vanish {N : ℕ} {g : ℚ[X]}
    (hp : 2 < p) (hg : SquareValuedLower p 0 g)
    (hsmall : 2 * max g.natDegree N < p ^ 2) :
    PadicLower p 1 (secondZeroContribution N p g) := by
  have hN : N ≤ max g.natDegree N := le_max_right _ _
  have hhalf : PadicLower p 0 (1 / 2 : ℚ) := by
    have h2 : ¬(p : ℤ) ∣ (2 : ℤ) := by
      intro hd
      have hd' : p ∣ 2 := by exact_mod_cast hd
      have hh := Nat.le_of_dvd (by norm_num : 0 < 2) hd'
      omega
    simpa only [one_div, Int.cast_ofNat] using inverse_int_integral_of_not_dvd (p := p) 2 h2
  have hzero : PadicLower p 1 ((1 / 2 : ℚ) * bernoulliFunctional
      ((scaledQuotientNumerator N p g).comp (localAffine p 0)).derivative) := by
    simpa only [zero_add] using hhalf.mul (scaledQuotientNumerator_zero_class_vanish hp hg hsmall)
  have hret := second_scaled_retained_quotient_vanish hp hg (by omega : 2 * N < p ^ 2)
  have hproper : PadicLower p 1 ((p : ℚ) ^ (2 + 2 * (N % p) / p) *
      ∑ i ∈ zeroClassNodes N p, (normalizedResidue N g i).coeff 0) := by
    rw [mul_sum]
    apply padicLower_sum
    intro i hi
    obtain ⟨hi, hpi⟩ := mem_filter.mp hi
    obtain ⟨hi0, hiN⟩ := mem_Ioc.mp hi
    have hgi : PadicLower p 0 (g.eval ((i : ℚ) ^ 2)) := by
      simpa only [Int.cast_natCast] using hg (i : ℤ)
    simpa only [coeff_C_mul] using
      second_scaled_zero_residue_vanish hp hi0 hiN hpi (by omega) hgi 0
  exact (hzero.add hret).add hproper

theorem secondClassContribution_maximal_vanish {N c L₀ : ℕ} {g : ℚ[X]}
    (hp : 2 < p) (hg : SquareValuedLower p 0 g)
    (hsmall : 2 * max g.natDegree N < p ^ 2)
    (hkernel : ∀ d ∈ maximalReflectedClasses N p,
      PolynomialPadicLower p 2 (g.comp ((localAffine p d) ^ 2)))
    (hc : c ∈ maximalReflectedClasses N p)
    (hL₀ : (scaledQuotientNumerator N p g).natDegree ≤ L₀) (hL₀p : L₀ < p ^ 2)
    (hE : L₀ / p + 3 ≤ p) :
    PadicLower p 1 (secondClassContribution N p c g) := by
  have hN : N ≤ max g.natDegree N := le_max_right _ _
  apply PadicLower.add
  · rw [mul_sum]
    apply padicLower_sum
    intro i hi
    simpa only [coeff_C_mul] using
      second_scaled_maximal_residue_vanish hp hc hi (by omega) (hkernel c hc) 0
  · exact scaledQuotientNumerator_maximal_vanish hp hg hsmall
      (fun d hd => (hkernel d hd).mono (by norm_num)) hc (hkernel c hc) hL₀ hL₀p hE

def secondFeatureSum (N p : ℕ) (F : ℕ → ℚ[X]) : ℚ :=
  ∑ c ∈ Icc 1 ((p - 1) / 2), if c ∈ maximalReflectedClasses N p then 0 else
    secondLocalMultiplier N p c * physicalLocalCubicFunctional N p c (F c)

theorem normalizedCentralFunctional_second_feature_reduction {N L₀ : ℕ} {g : ℚ[X]}
    (F : ℕ → ℚ[X]) (hp : 2 < p) (hg : SquareValuedLower p 0 g)
    (hsmall : 2 * max g.natDegree N < p ^ 2)
    (hkernel : ∀ d ∈ maximalReflectedClasses N p,
      PolynomialPadicLower p 2 (g.comp ((localAffine p d) ^ 2)))
    (hglocal : ∀ c ∈ Icc 1 ((p - 1) / 2),
      PolynomialPadicLower p 0 (g.comp ((localAffine p c) ^ 2)))
    (hF : ∀ c ∈ Icc 1 ((p - 1) / 2), c ∉ maximalReflectedClasses N p →
      PolynomialPadicLower p 0 (F c))
    (hGF : ∀ c ∈ Icc 1 ((p - 1) / 2), c ∉ maximalReflectedClasses N p →
      PolynomialPadicLower p 1 (g.comp ((localAffine p c) ^ 2) - F c))
    (hFdegree : ∀ c ∈ Icc 1 ((p - 1) / 2), c ∉ maximalReflectedClasses N p →
      (F c).natDegree ≤ (physicalLocalMonic N p c).natDegree + (p - 1))
    (hL₀ : (scaledQuotientNumerator N p g).natDegree ≤ L₀) (hL₀p : L₀ < p ^ 2)
    (hE : L₀ / p + 3 ≤ p) :
    PadicLower p 1 ((p : ℚ) ^ (2 + 2 * (N % p) / p) *
      (normalizedCentralFunctional N g).coeff 0 - secondFeatureSum N p F) := by
  have hodd := (Fact.out : p.Prime).mod_two_eq_one_iff_ne_two.mpr (by omega : p ≠ 2)
  rw [normalizedCentralFunctional_second_decomposition N g hodd, secondFeatureSum]
  have hsum : PadicLower p 1
      (∑ c ∈ Icc 1 ((p - 1) / 2), (secondClassContribution N p c g -
        (if c ∈ maximalReflectedClasses N p then 0 else
          secondLocalMultiplier N p c * physicalLocalCubicFunctional N p c (F c)))) := by
    apply padicLower_sum
    intro c hc
    by_cases hmax : c ∈ maximalReflectedClasses N p
    · rw [if_pos hmax, sub_zero]
      exact secondClassContribution_maximal_vanish hp hg hsmall hkernel hmax hL₀ hL₀p hE
    · rw [if_neg hmax]
      have hc' := mem_Icc.mp hc
      exact second_local_class_reduction_to_features hp hg hsmall
        (fun d hd => (hkernel d hd).mono (by norm_num)) hc'.1 (by omega) hmax
        (hglocal c hc) (hF c hc hmax) (hGF c hc hmax) (hFdegree c hc hmax) hL₀ hL₀p hE
  have h := (secondZeroContribution_vanish hp hg hsmall).add hsum
  rw [sum_sub_distrib] at h
  convert h using 1
  ring

end Zeta3.Arithmetic

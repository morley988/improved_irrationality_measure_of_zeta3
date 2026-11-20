import Zeta5.Arithmetic.LocalFunctional
import Zeta3.Arithmetic.LocalRestriction
import Zeta3.Arithmetic.Moments

/-! The actual cubic normalized central functional: quotient, retained
central truncation, and physical residue terms are all bounded together.
The restriction kernel gains one prime power in every contribution. -/
noncomputable section
namespace Zeta3.Arithmetic
open Polynomial Finset OddZeta.FourValue Zeta5.Construction Zeta3.Construction
open Zeta5.Arithmetic
variable {p : ℕ} [Fact p.Prime]

theorem normalized_centralExpansion_quotient_moment_bound {N : ℕ} {g : ℚ[X]}
    (hp : 2 < p) (hg : SquareValuedLower p 0 g) (hsmall : 2 * N < p ^ 2) :
    PadicLower p (-1 - ((2 * (N % p) / p : ℕ) : ℤ))
      (Zeta3.Construction.polynomialMoment ((C ((N.factorial : ℚ) ^ 2) * (centralExpansion g N).comp (-X)) /
        denominator N)) := by
  have hI := (normalized_centralExpansion_integral_bound hg hsmall).comp_integral
    (polynomialPadicLower_X (p := p)).neg
  rw [mul_comp, C_comp] at hI
  have hD : PolynomialPadicLower p 0 (denominator N) := by
    rw [← denominatorInt_map]
    exact polynomialPadicLower_integer_map _
  have h := polynomialMoment_weighted_lower hp
    (polynomialPadicLower_divByMonic_nonpos hI hD (denominator_monic N))
  convert h using 1
  omega

def normalizedResidue (N : ℕ) (g : ℚ[X]) (i : ℕ) : ℚ[X] :=
  C ((N.factorial : ℚ) ^ 2 * g.eval ((i : ℚ) ^ 2) /
    (denominator N).derivative.eval (pole i)) * Zeta3.Construction.stieltjes i

theorem normalizedResidue_bound {N i : ℕ} {g : ℚ[X]} {w v z : ℤ}
    (hN : N < p ^ 2) (hg : PadicLower p w (g.eval ((i : ℚ) ^ 2)))
    (hden : padicValRat p ((denominator N).derivative.eval (pole i)) ≤ v)
    (hk : PolynomialPadicLower p z (Zeta3.Construction.stieltjes i)) :
    PolynomialPadicLower p (2 * ((N / p : ℕ) : ℤ) + w - v + z) (normalizedResidue N g i) := by
  have hinv : PadicLower p (-v) (((denominator N).derivative.eval (pole i))⁻¹) := by
    right
    rw [padicValRat.inv]
    omega
  have hs := ((factorial_square_padicLower hN).mul hg).mul hinv
  simpa only [normalizedResidue, div_eq_mul_inv, sub_eq_add_neg] using
    (PolynomialPadicLower.constant hs).mul hk

theorem normalizedResidue_reflected_bound {N c i : ℕ} {g : ℚ[X]} {w : ℤ}
    (hp : 2 < p) (hc : 0 < c) (hcp : 2 * c < p)
    (hi : i ∈ reflectedNodes N p c) (hsmall : 2 * N < p ^ 2)
    (hg : PadicLower p w (g.eval ((i : ℚ) ^ 2))) :
    PolynomialPadicLower p (w + 2 * ((N / p : ℕ) : ℤ) - reflectedSize N p c - 2)
      (normalizedResidue N g i) := by
  obtain ⟨hi0, hiN, _⟩ := mem_reflectedNodes.mp hi
  have hd := denominator_derivative_reflected_valuation N c i (by omega) hc hcp hi (by omega)
  have h := normalizedResidue_bound (by omega : N < p ^ 2) hg hd.le
    (stieltjes_polynomial_padicLower i hp hi0 (by omega))
  convert h using 1
  omega

theorem normalizedResidue_zero_class_integral {N i : ℕ} {g : ℚ[X]}
    (hp : 2 < p) (hi : 0 < i) (hiN : i ≤ N) (hpi : p ∣ i)
    (hsmall : 2 * N < p ^ 2) (hg : PadicLower p 0 (g.eval ((i : ℚ) ^ 2))) :
    PolynomialPadicLower p 0 (normalizedResidue N g i) := by
  have h := normalizedResidue_bound (by omega : N < p ^ 2) hg
    (denominator_derivative_zero_class_bound (by omega) hi hiN hpi hsmall)
    (stieltjes_polynomial_multiple_p i hp hi (by omega) hpi)
  exact h.mono (by omega)

theorem normalizedResidue_global_bound {N i : ℕ} {g : ℚ[X]}
    (hp : 2 < p) (hi : 0 < i) (hiN : i ≤ N) (hsmall : 2 * N < p ^ 2)
    (hg : SquareValuedLower p 0 g) :
    PolynomialPadicLower p (-3 - ((2 * (N % p) / p : ℕ) : ℤ)) (normalizedResidue N g i) := by
  have heps : 0 ≤ ((2 * (N % p) / p : ℕ) : ℤ) := Int.natCast_nonneg _
  have hgi : PadicLower p 0 (g.eval ((i : ℚ) ^ 2)) := by
    simpa only [Int.cast_natCast] using hg (i : ℤ)
  by_cases hpi : p ∣ i
  · exact (normalizedResidue_zero_class_integral hp hi hiN hpi hsmall hgi).mono (by omega)
  · let c := reflectedLabel p i
    have hodd := (Fact.out : p.Prime).mod_two_eq_one_iff_ne_two.mpr (by omega : p ≠ 2)
    have hc : 0 < c := Nat.pos_of_ne_zero ((reflectedLabel_eq_zero p i (by omega)).not.mpr hpi)
    have hchalf : c ≤ (p - 1) / 2 := reflectedLabel_le_half p i (by omega) hodd
    have hcp : 2 * c < p := by omega
    have himem : i ∈ reflectedNodes N p c :=
      mem_reflectedNodes.mpr ⟨hi, hiN, (reflectedLabel_eq_iff p i c (by omega) hc hcp).mp rfl⟩
    have hsize := reflectedSize_le_max N p c hodd hc hchalf
    have hsize' : (reflectedSize N p c : ℤ) ≤
        2 * ((N / p : ℕ) : ℤ) + 1 + ((2 * (N % p) / p : ℕ) : ℤ) := by exact_mod_cast hsize
    exact (normalizedResidue_reflected_bound hp hc hcp himem hsmall hgi).mono (by omega)

theorem normalizedResidue_global_bound_on_kernel {N i : ℕ} {g : ℚ[X]}
    (hp : 2 < p) (hi : 0 < i) (hiN : i ≤ N) (hsmall : 2 * N < p ^ 2)
    (hg : SquareValuedLower p 0 g)
    (hkernel : ∀ c ∈ maximalReflectedClasses N p,
      PolynomialPadicLower p 1 (g.comp ((localAffine p c) ^ 2))) :
    PolynomialPadicLower p (-2 - ((2 * (N % p) / p : ℕ) : ℤ)) (normalizedResidue N g i) := by
  have heps : 0 ≤ ((2 * (N % p) / p : ℕ) : ℤ) := Int.natCast_nonneg _
  have hgi : PadicLower p 0 (g.eval ((i : ℚ) ^ 2)) := by
    simpa only [Int.cast_natCast] using hg (i : ℤ)
  by_cases hpi : p ∣ i
  · exact (normalizedResidue_zero_class_integral hp hi hiN hpi hsmall hgi).mono (by omega)
  · let c := reflectedLabel p i
    have hodd := (Fact.out : p.Prime).mod_two_eq_one_iff_ne_two.mpr (by omega : p ≠ 2)
    have hc : 0 < c := Nat.pos_of_ne_zero ((reflectedLabel_eq_zero p i (by omega)).not.mpr hpi)
    have hchalf : c ≤ (p - 1) / 2 := reflectedLabel_le_half p i (by omega) hodd
    have hcp : 2 * c < p := by omega
    have himem : i ∈ reflectedNodes N p c :=
      mem_reflectedNodes.mpr ⟨hi, hiN, (reflectedLabel_eq_iff p i c (by omega) hc hcp).mp rfl⟩
    have hsize := reflectedSize_le_max N p c hodd hc hchalf
    have hsize' : (reflectedSize N p c : ℤ) ≤
        2 * ((N / p : ℕ) : ℤ) + 1 + ((2 * (N % p) / p : ℕ) : ℤ) := by exact_mod_cast hsize
    by_cases hmax : c ∈ maximalReflectedClasses N p
    · have hgain := square_local_eval_at_reflected hc hcp himem (hkernel c hmax)
      exact (normalizedResidue_reflected_bound hp hc hcp himem hsmall hgain).mono (by omega)
    · have hne : reflectedSize N p c ≠ 2 * (N / p) + 1 + 2 * (N % p) / p := by
        intro he
        exact hmax (mem_filter.mpr ⟨mem_Icc.mpr ⟨hc, hchalf⟩, he⟩)
      have hne' : (reflectedSize N p c : ℤ) ≠
          2 * ((N / p : ℕ) : ℤ) + 1 + ((2 * (N % p) / p : ℕ) : ℤ) := by exact_mod_cast hne
      exact (normalizedResidue_reflected_bound hp hc hcp himem hsmall hgi).mono (by omega)

def normalizedCentralFunctional (N : ℕ) (g : ℚ[X]) : ℚ[X] :=
  Zeta3.Construction.numeratorFunctional N (C ((N.factorial : ℚ) ^ 2) * g.comp (-X))

theorem normalizedCentralFunctional_eq (N : ℕ) (g : ℚ[X]) :
    normalizedCentralFunctional N g =
      C ((N.factorial : ℚ) ^ 2) * Zeta3.Construction.numeratorFunctional N (g.comp (-X)) := by
  simpa only [normalizedCentralFunctional, smul_eq_C_mul] using
    (Zeta3.Construction.numeratorFunctional N).map_smul ((N.factorial : ℚ) ^ 2) (g.comp (-X))

theorem normalizedCentralFunctional_decomposition (N : ℕ) (g : ℚ[X]) :
    normalizedCentralFunctional N g =
      C (Zeta3.Construction.polynomialMoment (C ((N.factorial : ℚ) ^ 2) * centralQuotient N g)) +
      C (Zeta3.Construction.polynomialMoment ((C ((N.factorial : ℚ) ^ 2) * (centralExpansion g N).comp (-X)) /
        denominator N)) + ∑ i ∈ range N, normalizedResidue N g (i + 1) := by
  have hsplit : C ((N.factorial : ℚ) ^ 2) * g.comp (-X) =
      C ((N.factorial : ℚ) ^ 2) * centralTail N g +
      C ((N.factorial : ℚ) ^ 2) * (centralExpansion g N).comp (-X) := by
    rw [centralTail, sub_comp]
    ring
  have hq : (C ((N.factorial : ℚ) ^ 2) * g.comp (-X)) / denominator N =
      C ((N.factorial : ℚ) ^ 2) * centralQuotient N g +
      (C ((N.factorial : ℚ) ^ 2) * (centralExpansion g N).comp (-X)) / denominator N := by
    have hadd := (monicQuotientMap (denominator N) (denominator_monic N)).map_add
      (C ((N.factorial : ℚ) ^ 2) * centralTail N g)
      (C ((N.factorial : ℚ) ^ 2) * (centralExpansion g N).comp (-X))
    simp only [monicQuotientMap_apply] at hadd
    rw [hsplit, hadd, centralTail_eq_denominator_mul_quotient]
    have hm : C ((N.factorial : ℚ) ^ 2) * (denominator N * centralQuotient N g) =
        (C ((N.factorial : ℚ) ^ 2) * centralQuotient N g) * denominator N := by ring
    rw [hm, mul_div_cancel_right₀ _ (denominator_ne_zero N)]
  rw [normalizedCentralFunctional, Zeta3.Construction.numeratorFunctional_apply, hq]
  have hmoment := Zeta3.Construction.polynomialMomentMap.map_add
    (C ((N.factorial : ℚ) ^ 2) * centralQuotient N g)
    ((C ((N.factorial : ℚ) ^ 2) * (centralExpansion g N).comp (-X)) / denominator N)
  simp only [Zeta3.Construction.polynomialMomentMap_apply] at hmoment
  rw [hmoment, C_add]
  congr 1
  apply sum_congr rfl
  intro i hi
  simp only [normalizedResidue, eval_mul, eval_C, eval_comp, eval_neg, eval_X, pole, neg_neg]

theorem normalizedCentralFunctional_padicLower {N : ℕ} {g : ℚ[X]}
    (hp : 2 < p) (hg : SquareValuedLower p 0 g)
    (hsmall : 2 * max g.natDegree N + 4 < p ^ 2) :
    PolynomialPadicLower p (-3 - ((2 * (N % p) / p : ℕ) : ℤ))
      (normalizedCentralFunctional N g) := by
  have hmax : N ≤ max g.natDegree N := le_max_right _ _
  rw [normalizedCentralFunctional_decomposition]
  apply PolynomialPadicLower.add
  · apply PolynomialPadicLower.add
    · exact PolynomialPadicLower.constant (centralQuotient_moment_bound hp hg hsmall)
    · exact (PolynomialPadicLower.constant
        (normalized_centralExpansion_quotient_moment_bound hp hg (by omega))).mono (by omega)
  · apply PolynomialPadicLower.sum
    intro i hi
    exact normalizedResidue_global_bound hp (by omega) (by simpa using mem_range.mp hi) (by omega) hg

theorem normalizedCentralFunctional_padicLower_on_kernel {N : ℕ} {g : ℚ[X]}
    (hp : 2 < p) (hg : SquareValuedLower p 0 g)
    (hsmall : 2 * max g.natDegree N + 4 < p ^ 2)
    (hkernel : ∀ c ∈ maximalReflectedClasses N p,
      PolynomialPadicLower p 1 (g.comp ((localAffine p c) ^ 2))) :
    PolynomialPadicLower p (-2 - ((2 * (N % p) / p : ℕ) : ℤ))
      (normalizedCentralFunctional N g) := by
  have hmax : N ≤ max g.natDegree N := le_max_right _ _
  rw [normalizedCentralFunctional_decomposition]
  apply PolynomialPadicLower.add
  · apply PolynomialPadicLower.add
    · exact PolynomialPadicLower.constant (centralQuotient_moment_bound_on_kernel hp hg hsmall hkernel)
    · exact (PolynomialPadicLower.constant
        (normalized_centralExpansion_quotient_moment_bound hp hg (by omega))).mono (by omega)
  · apply PolynomialPadicLower.sum
    intro i hi
    exact normalizedResidue_global_bound_on_kernel hp (by omega)
      (by simpa using mem_range.mp hi) (by omega) hg hkernel

end Zeta3.Arithmetic

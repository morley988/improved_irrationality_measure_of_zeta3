import Zeta3.Arithmetic.SecondResidues
import Zeta3.Arithmetic.SecondVanishing
import Zeta3.Arithmetic.WeightedDivision

/-! The nonmaximal Bernoulli contribution factors through any integral
representative of the actual local feature polynomial. Reduction is passed
through the derivative using the full Newton precision, including its
high-degree tail. -/
noncomputable section
namespace Zeta3.Arithmetic
open Polynomial Finset OddZeta.FourValue Zeta5.Arithmetic Zeta5.Construction
variable {p : ℕ} [Fact p.Prime]

theorem second_local_moment_reduction_to_features {N c L₀ : ℕ} {g F : ℚ[X]}
    (hp : 2 < p) (hg : SquareValuedLower p 0 g)
    (hsmall : 2 * max g.natDegree N < p ^ 2)
    (hkernel : ∀ d ∈ maximalReflectedClasses N p,
      PolynomialPadicLower p 1 (g.comp ((localAffine p d) ^ 2)))
    (hc : 0 < c) (hcp : 2 * c < p) (hnot : c ∉ maximalReflectedClasses N p)
    (hglocal : PolynomialPadicLower p 0 (g.comp ((localAffine p c) ^ 2)))
    (hF : PolynomialPadicLower p 0 F)
    (hGF : PolynomialPadicLower p 1 (g.comp ((localAffine p c) ^ 2) - F))
    (hFdegree : F.natDegree ≤ (physicalLocalMonic N p c).natDegree + (p - 1))
    (hL₀ : (scaledQuotientNumerator N p g).natDegree ≤ L₀) (hL₀p : L₀ < p ^ 2)
    (hE : L₀ / p + 3 ≤ p) :
    PadicLower p 1
      (bernoulliFunctional ((scaledQuotientNumerator N p g).comp (localAffine p c)).derivative -
        (secondLocalMultiplier N p c / 2) *
          bernoulliFunctional ((F / physicalLocalMonic N p c).derivative)) := by
  have hN : N ≤ max g.natDegree N := le_max_right _ _
  have hodd := (Fact.out : p.Prime).mod_two_eq_one_iff_ne_two.mpr (by omega : p ≠ 2)
  obtain ⟨a, ha, hQa⟩ := centralQuotient_nonmaximal_second_reduction hg (by omega)
    hc hcp hodd hnot hglocal
  let L := physicalLocalMonic N p (c : ℤ)
  let G := g.comp ((localAffine p c) ^ 2)
  let v : ℚ := localNormalizationUnit N p * ((physicalLocalUnit N p c).coeff 0)⁻¹
  let Q := C ((p : ℚ) ^ (2 * (N % p) / p)) *
    (C ((N.factorial : ℚ) ^ 2) * centralQuotient N g).comp (-(localAffine p c) ^ 2)
  have hv : PadicLower p 0 v := by
    simpa only [zero_add] using
      (localNormalizationUnit_integral (p := p) (N := N) (by omega)).mul
      (physicalLocalUnit_inverse_constant_integral N (c : ℤ))
  have hLint := physicalLocalMonic_integral (p := p) N (c : ℤ)
  have hLmonic := physicalLocalMonic_monic (p := p) N (c : ℤ)
  have hdiv := polynomialPadicLower_quotient_congruence hGF hLint hLmonic
  have hdivScaled : PolynomialPadicLower p 1 (C v * (G / L - F / L)) := by
    simpa only [zero_add] using (PolynomialPadicLower.constant hv).mul hdiv
  have hQrep : PolynomialPadicLower p 1 (Q - C v * (F / L - C a)) := by
    have he : Q - C v * (F / L - C a) =
        (Q - C v * (G / L - C a)) + C v * (G / L - F / L) := by ring
    rw [he]
    exact hQa.add hdivScaled
  have hFdiv : PolynomialPadicLower p 0 (F / L) := by
    rw [← divByMonic_eq_div _ hLmonic]
    exact polynomialPadicLower_divByMonic hF hLint hLmonic
  have hRint : PolynomialPadicLower p 0 (C v * (F / L - C a)) := by
    have ht : PolynomialPadicLower p 0 (F / L - C a) := hFdiv.add (PolynomialPadicLower.constant ha).neg
    simpa only [zero_add] using (PolynomialPadicLower.constant hv).mul ht
  have hQint : PolynomialPadicLower p 0 Q := by
    have h := (hQrep.mono (by norm_num : (0 : ℤ) ≤ 1)).add hRint
    simpa only [sub_add_cancel] using h
  let R := C ((c : ℚ) ^ 3 * v) * (F / L - C a)
  have hc3 : PadicLower p 0 ((c : ℚ) ^ 3) := padicIntegral_pow (padicLower_nat c) 3
  have hPcongr : PolynomialPadicLower p 1 ((localAffine p c) ^ 3 * Q - R) := by
    have h₁ : PolynomialPadicLower p 1 (((localAffine p c) ^ 3 - C ((c : ℚ) ^ 3)) * Q) := by
      simpa only [add_zero, Int.cast_natCast] using (localAffine_pow_sub_constant (p := p) (c : ℤ) 3).mul hQint
    have h₂ : PolynomialPadicLower p 1 (C ((c : ℚ) ^ 3) * (Q - C v * (F / L - C a))) := by
      simpa only [zero_add] using (PolynomialPadicLower.constant hc3).mul hQrep
    have he : (localAffine p c) ^ 3 * Q - R =
        ((localAffine p c) ^ 3 - C ((c : ℚ) ^ 3)) * Q +
          C ((c : ℚ) ^ 3) * (Q - C v * (F / L - C a)) := by dsimp [R]; rw [C_mul]; ring
    rw [he]
    exact h₁.add h₂
  have he : (scaledQuotientNumerator N p g).comp (localAffine p c) = (localAffine p c) ^ 3 * Q := by
    simp only [scaledQuotientNumerator, bernoulliMomentNumerator, mul_comp, C_comp,
      pow_comp, X_comp, comp_assoc, neg_comp, Q]
    ring
  have hFdivdegree : (F / L).natDegree ≤ p - 1 := by
    rw [← divByMonic_eq_div _ hLmonic, natDegree_divByMonic _ hLmonic]
    omega
  have hRdegree : R.natDegree ≤ p - 1 := by
    apply (natDegree_C_mul_le _ _).trans
    apply (natDegree_sub_le _ _).trans
    simpa only [natDegree_C, Nat.max_zero] using hFdivdegree
  have hIv := scaledQuotientNumerator_integerValued hodd hg hsmall hkernel
  have h := bernoulliFunctional_derivative_integral_congruence
    ((scaledQuotientNumerator N p g).comp (localAffine p c)) R (L₀ / p) hp hE
    (fun j => integerValuedAt_local_coeff_precision hIv hL₀ hL₀p (c : ℤ) j) hRdegree
    (by intro j hj; simpa only [he, coeff_sub] using hPcongr j)
  have hRval : bernoulliFunctional R.derivative =
      (secondLocalMultiplier N p c / 2) * bernoulliFunctional (F / L).derivative := by
    simp only [R, derivative_C_mul, derivative_sub, derivative_C, sub_zero,
      bernoulliFunctional_C_mul]
    dsimp only [v, secondLocalMultiplier]
    ring
  simpa only [hRval, L] using h

end Zeta3.Arithmetic

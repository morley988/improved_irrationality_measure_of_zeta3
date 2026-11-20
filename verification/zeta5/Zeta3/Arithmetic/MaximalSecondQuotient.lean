import Zeta3.Arithmetic.SecondInterpolation
import Zeta3.Arithmetic.LocalUnitReduction

/-! On both maximal restriction kernels the normalized physical quotient,
multiplied by p^epsilon, is constant modulo p. All quotient and unit-factor
congruences here refer to the actual central truncation and denominator. -/
noncomputable section
namespace Zeta3.Arithmetic
open Polynomial Finset OddZeta.FourValue Zeta5.Arithmetic Zeta5.Construction
variable {p : ℕ} [Fact p.Prime]

theorem centralQuotient_maximal_second_constant {N c : ℕ} {g : ℚ[X]}
    (hg : SquareValuedLower p 0 g) (hsmall : 2 * N < p ^ 2)
    (hc : c ∈ maximalReflectedClasses N p)
    (hkernel : PolynomialPadicLower p 2 (g.comp ((localAffine p c) ^ 2))) :
    ∃ b : ℚ, PadicLower p 0 b ∧ PolynomialPadicLower p 1
      (C ((p : ℚ) ^ (2 * (N % p) / p)) *
        (C ((N.factorial : ℚ) ^ 2) * centralQuotient N g).comp (-(localAffine p c) ^ 2) - C b) := by
  let e := 2 * (N % p) / p
  let d := 2 * (N / p) + e
  let L := physicalLocalMonic N p (c : ℤ)
  let U := physicalLocalUnit N p (c : ℤ)
  let G := g.comp ((localAffine p c) ^ 2)
  let I := (centralExpansion g N).comp ((localAffine p c) ^ 2)
  let Q := (centralQuotient N g).comp (-(localAffine p c) ^ 2)
  let F := C ((p : ℚ)⁻¹) * (G - I)
  let V := C ((p : ℚ) ^ d) * Q
  obtain ⟨a, ha, hI⟩ := centralExpansion_maximal_second_reduction hg hsmall hc hkernel
  have hp0 : (p : ℚ) ≠ 0 := by exact_mod_cast (Fact.out : p.Prime).ne_zero
  have hinv : PadicLower p (-1) ((p : ℚ)⁻¹) := by
    simpa using inverse_prime_power_padicLower (p := p) 1
  have hG : PolynomialPadicLower p 1 (C ((p : ℚ)⁻¹) * G) := by
    simpa using (PolynomialPadicLower.constant hinv).mul hkernel
  have hFcongr : PolynomialPadicLower p 1 (F - C (-a) * L) := by
    have he : F - C (-a) * L = C ((p : ℚ)⁻¹) * G -
        (C ((p : ℚ)⁻¹) * I - C a * L) := by
      dsimp [F]
      rw [C_neg]
      ring
    rw [he, sub_eq_add_neg]
    exact hG.add hI.neg
  have hLint := physicalLocalMonic_integral (p := p) N (c : ℤ)
  have hLmonic := physicalLocalMonic_monic (p := p) N (c : ℤ)
  have hUint := physicalLocalUnit_integral (p := p) N (c : ℤ)
  have hU0 := physicalLocalUnit_constant_ne_zero (p := p) N (c : ℤ)
  have hUinv := physicalLocalUnit_inverse_constant_integral (p := p) N (c : ℤ)
  have hF : PolynomialPadicLower p 0 F := by
    have hCa : PolynomialPadicLower p 0 (C (-a) * L) := by
      simpa only [add_zero] using (PolynomialPadicLower.constant ha.neg).mul hLint
    have h := (hFcongr.mono (by norm_num : (0 : ℤ) ≤ 1)).add hCa
    simpa only [sub_add_cancel] using h
  have hmult : physicalLocalMultiplicity N p (c : ℤ) = d + 1 := by
    obtain ⟨hci, he⟩ := mem_filter.mp hc
    obtain ⟨hc0, hch⟩ := mem_Icc.mp hci
    rw [physicalLocalMultiplicity_eq_reflectedSize N p c hc0 (by omega), he]
    dsimp [d, e]
    omega
  have htail : G - I = (denominator N).comp (-(localAffine p c) ^ 2) * Q := by
    rw [← centralTail_comp_square, centralTail_eq_denominator_mul_quotient, mul_comp]
  have hfactor : F = L * U * V := by
    dsimp only [F, V]
    rw [htail, denominator_local_factorization, hmult, pow_succ, C_mul]
    dsimp only [L, U]
    have he : C ((p : ℚ)⁻¹) * C (p : ℚ) = (1 : ℚ[X]) := by
      rw [← C_mul, inv_mul_cancel₀ hp0, C_1]
    calc
      _ = (C ((p : ℚ)⁻¹) * C (p : ℚ)) *
          (physicalLocalMonic N p (c : ℤ) * physicalLocalUnit N p (c : ℤ) * (C ((p : ℚ) ^ d) * Q)) := by ring
      _ = _ := by rw [he, one_mul]
  have hVint : PolynomialPadicLower p 0 V := by
    have hUV := polynomialPadicLower_quotient_of_monic hF hLint hLmonic
      (show F = L * (U * V) by rw [hfactor]; ring)
    exact polynomialPadicLower_quotient_of_unit_constant hUV hUint hU0 hUinv rfl
  have hVc := localQuotient_congr_constant hVint hLint hLmonic hUinv hU0
    (physicalLocalUnit_sub_constant N (c : ℤ)) hFcongr hfactor
  let u : ℚ := ((N.factorial : ℚ) ^ 2) * ((p : ℚ) ^ (2 * (N / p)))⁻¹
  have hu : PadicLower p 0 u := by
    have h := (factorial_square_padicLower (p := p) (by omega : N < p ^ 2)).mul
      (inverse_prime_power_padicLower (p := p) (2 * (N / p)))
    simpa [u] using h
  have hb : PadicLower p 0 (u * (-a / U.coeff 0)) := by
    simpa only [div_eq_mul_inv, zero_add] using hu.mul (ha.neg.mul hUinv)
  refine ⟨u * (-a / U.coeff 0), hb, ?_⟩
  have h := (PolynomialPadicLower.constant hu).mul hVc
  have he : C u * V = C ((p : ℚ) ^ e) * (C ((N.factorial : ℚ) ^ 2) * Q) := by
    dsimp only [u, V, d]
    rw [pow_add, C_mul]
    have hpq : (p : ℚ) ^ (2 * (N / p)) ≠ 0 := pow_ne_zero _ hp0
    have hcancel : C (((p : ℚ) ^ (2 * (N / p)))⁻¹) * C ((p : ℚ) ^ (2 * (N / p))) = 1 := by
      rw [← C_mul, inv_mul_cancel₀ hpq, C_1]
    calc
      _ = (C (((p : ℚ) ^ (2 * (N / p)))⁻¹) * C ((p : ℚ) ^ (2 * (N / p)))) *
        (C ((p : ℚ) ^ e) * (C ((N.factorial : ℚ) ^ 2) * Q)) := by
          rw [C_mul]; ring
      _ = _ := by rw [hcancel, one_mul]
  rw [mul_sub, he, ← C_mul] at h
  simpa only [e, Q, mul_comp, C_comp, zero_add] using h

end Zeta3.Arithmetic

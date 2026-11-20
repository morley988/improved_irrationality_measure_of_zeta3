import Zeta5.Arithmetic.LocalFunctional

/-! Monic quotient maps preserve coefficientwise divisibility by p. -/
noncomputable section
namespace Zeta3.Arithmetic
open Polynomial OddZeta.FourValue Zeta5.Arithmetic Zeta5.Construction
variable {p : ℕ} [Fact p.Prime]

theorem quotient_C_mul (P L : ℚ[X]) (hL : L.Monic) (a : ℚ) :
    (C a * P) / L = C a * (P / L) := by
  simpa only [smul_eq_C_mul, monicQuotientMap_apply] using (monicQuotientMap L hL).map_smul a P

theorem quotient_sub (P Q L : ℚ[X]) (hL : L.Monic) :
    (P - Q) / L = P / L - Q / L := by
  simpa only [monicQuotientMap_apply] using (monicQuotientMap L hL).map_sub P Q

theorem polynomialPadicLower_quotient_one {P L : ℚ[X]}
    (hP : PolynomialPadicLower p 1 P) (hL : PolynomialPadicLower p 0 L) (hmonic : L.Monic) :
    PolynomialPadicLower p 1 (P / L) := by
  have hinv : PadicLower p (-1) ((p : ℚ)⁻¹) := by simpa using inverse_prime_power_padicLower (p := p) 1
  have hscaled : PolynomialPadicLower p 0 (C ((p : ℚ)⁻¹) * P) := by
    simpa using (PolynomialPadicLower.constant hinv).mul hP
  have hq : PolynomialPadicLower p 0 ((C ((p : ℚ)⁻¹) * P) / L) := by
    rw [← divByMonic_eq_div _ hmonic]
    exact polynomialPadicLower_divByMonic hscaled hL hmonic
  have hp1 : PadicLower p 1 (p : ℚ) := by simpa using prime_power_padicLower (p := p) 1
  have h := (PolynomialPadicLower.constant hp1).mul hq
  rw [quotient_C_mul _ _ hmonic, ← mul_assoc, ← C_mul,
    mul_inv_cancel₀ (by exact_mod_cast (Fact.out : p.Prime).ne_zero : (p : ℚ) ≠ 0), C_1, one_mul] at h
  simpa using h

theorem polynomialPadicLower_quotient_congruence {P Q L : ℚ[X]}
    (hPQ : PolynomialPadicLower p 1 (P - Q))
    (hL : PolynomialPadicLower p 0 L) (hmonic : L.Monic) :
    PolynomialPadicLower p 1 (P / L - Q / L) := by
  rw [← quotient_sub P Q L hmonic]
  exact polynomialPadicLower_quotient_one hPQ hL hmonic

end Zeta3.Arithmetic

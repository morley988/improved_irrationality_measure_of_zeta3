import Zeta5.Arithmetic.LocalFunctional

/-! Reduction of the explicit physical unit factor to its constant term.
The quotient congruence below is polynomial algebra over the local integers. -/
noncomputable section
namespace Zeta3.Arithmetic
open Polynomial Finset OddZeta.FourValue Zeta5.Arithmetic
variable {p : ℕ} [Fact p.Prime]

theorem polynomialPadicLower_mul_sub_constant {F G : ℚ[X]}
    (hF : PolynomialPadicLower p 0 F) (hG : PolynomialPadicLower p 0 G)
    (hF' : PolynomialPadicLower p 1 (F - C (F.coeff 0)))
    (hG' : PolynomialPadicLower p 1 (G - C (G.coeff 0))) :
    PolynomialPadicLower p 1 (F * G - C ((F * G).coeff 0)) := by
  have h₁ : PolynomialPadicLower p 1 ((F - C (F.coeff 0)) * G) := by simpa using hF'.mul hG
  have h₂ : PolynomialPadicLower p 1 (C (F.coeff 0) * (G - C (G.coeff 0))) := by
    simpa using (PolynomialPadicLower.constant (hF 0)).mul hG'
  have he : F * G - C ((F * G).coeff 0) =
      (F - C (F.coeff 0)) * G + C (F.coeff 0) * (G - C (G.coeff 0)) := by
    rw [mul_coeff_zero, C_mul]
    ring
  rw [he]
  exact h₁.add h₂

theorem localLinearFactor_sub_constant (c r : ℤ) :
    PolynomialPadicLower p 1
      (localLinearFactor p c r - C ((localLinearFactor p c r).coeff 0)) := by
  have he : localLinearFactor p c r - C ((localLinearFactor p c r).coeff 0) = C (p : ℚ) * X := by
    simp [localLinearFactor, localAffine]
  rw [he]
  have hp1 : PadicLower p 1 (p : ℚ) := by simpa using prime_power_padicLower (p := p) 1
  simpa using (PolynomialPadicLower.constant hp1).mul polynomialPadicLower_X

theorem localUnitFactor_sub_constant {ι : Type*} [DecidableEq ι]
    (c : ℤ) (s : Finset ι) (r : ι → ℤ) :
    PolynomialPadicLower p 1
      (localUnitFactor p c s r - C ((localUnitFactor p c s r).coeff 0)) := by
  unfold localUnitFactor
  let t := s.filter (fun i => ¬(p : ℤ) ∣ c - r i)
  change PolynomialPadicLower p 1
    ((∏ i ∈ t, localLinearFactor p c (r i)) - C ((∏ i ∈ t, localLinearFactor p c (r i)).coeff 0))
  induction t using Finset.induction_on with
  | empty => simpa using (PolynomialPadicLower.zero (p := p) 1)
  | @insert i t hi ih =>
    rw [prod_insert hi]
    apply polynomialPadicLower_mul_sub_constant (localLinearFactor_integral c (r i))
      (by
        have h := PolynomialPadicLower.prod (p := p) t (fun j => localLinearFactor p c (r j))
          (fun _ => 0) (fun j _ => localLinearFactor_integral c (r j))
        simpa using h)
      (localLinearFactor_sub_constant c (r i)) ih

theorem physicalLocalUnit_sub_constant (N : ℕ) (c : ℤ) :
    PolynomialPadicLower p 1
      (physicalLocalUnit N p c - C ((physicalLocalUnit N p c).coeff 0)) := by
  have hs : PadicLower p 0 ((-1 : ℚ) ^ N) := by
    simpa using padicLower_int (p := p) ((-1 : ℤ) ^ N)
  have h := (PolynomialPadicLower.constant hs).mul
    (localUnitFactor_sub_constant (p := p) c Finset.univ (@signedPhysicalRoot N))
  convert h using 1
  · norm_num
  · simp only [physicalLocalUnit, coeff_C_mul, C_mul]
    ring

theorem localQuotient_congr_constant {P L U Q : ℚ[X]} {a : ℚ}
    (hQ : PolynomialPadicLower p 0 Q)
    (hL : PolynomialPadicLower p 0 L) (hmonic : L.Monic)
    (hUinv : PadicLower p 0 ((U.coeff 0)⁻¹)) (hU0 : U.coeff 0 ≠ 0)
    (hUconstant : PolynomialPadicLower p 1 (U - C (U.coeff 0)))
    (hP : PolynomialPadicLower p 1 (P - C a * L)) (heq : P = L * U * Q) :
    PolynomialPadicLower p 1 (Q - C (a / U.coeff 0)) := by
  have hLU : P - C a * L = L * (U * Q - C a) := by rw [heq]; ring
  have hUQ := polynomialPadicLower_quotient_of_monic hP hL hmonic hLU
  have htail : PolynomialPadicLower p 1 ((U - C (U.coeff 0)) * Q) := by
    simpa using hUconstant.mul hQ
  have hmain : PolynomialPadicLower p 1 (C (U.coeff 0) * Q - C a) := by
    have he : C (U.coeff 0) * Q - C a = (U * Q - C a) - (U - C (U.coeff 0)) * Q := by ring
    rw [he, sub_eq_add_neg]
    exact hUQ.add htail.neg
  have h := (PolynomialPadicLower.constant hUinv).mul hmain
  have he : C ((U.coeff 0)⁻¹) * (C (U.coeff 0) * Q - C a) = Q - C (a / U.coeff 0) := by
    rw [mul_sub, ← mul_assoc, ← C_mul, inv_mul_cancel₀ hU0, C_1, one_mul, ← C_mul]
    congr 2
    field_simp
  simpa only [he, zero_add] using h

theorem localQuotient_congr_polynomial {P L U Q R : ℚ[X]}
    (hQ : PolynomialPadicLower p 0 Q)
    (hL : PolynomialPadicLower p 0 L) (hmonic : L.Monic)
    (hUinv : PadicLower p 0 ((U.coeff 0)⁻¹)) (hU0 : U.coeff 0 ≠ 0)
    (hUconstant : PolynomialPadicLower p 1 (U - C (U.coeff 0)))
    (hP : PolynomialPadicLower p 1 (P - L * R)) (heq : P = L * U * Q) :
    PolynomialPadicLower p 1 (Q - C ((U.coeff 0)⁻¹) * R) := by
  have hLU : P - L * R = L * (U * Q - R) := by rw [heq]; ring
  have hUQ := polynomialPadicLower_quotient_of_monic hP hL hmonic hLU
  have htail : PolynomialPadicLower p 1 ((U - C (U.coeff 0)) * Q) := by
    simpa using hUconstant.mul hQ
  have hmain : PolynomialPadicLower p 1 (C (U.coeff 0) * Q - R) := by
    have he : C (U.coeff 0) * Q - R = (U * Q - R) - (U - C (U.coeff 0)) * Q := by ring
    rw [he, sub_eq_add_neg]
    exact hUQ.add htail.neg
  have h := (PolynomialPadicLower.constant hUinv).mul hmain
  have he : C ((U.coeff 0)⁻¹) * (C (U.coeff 0) * Q - R) =
      Q - C ((U.coeff 0)⁻¹) * R := by
    rw [mul_sub, ← mul_assoc, ← C_mul, inv_mul_cancel₀ hU0, C_1, one_mul]
  simpa only [he, zero_add] using h

end Zeta3.Arithmetic

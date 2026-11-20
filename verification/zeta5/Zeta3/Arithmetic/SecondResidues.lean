import Zeta3.Arithmetic.PhysicalLevels
import Zeta3.Arithmetic.LocalFunctional

/-! Reduction of the actual cubic proper fractions on nonmaximal classes. -/
noncomputable section
namespace Zeta3.Arithmetic
open Polynomial Finset OddZeta.FourValue Zeta5.Arithmetic Zeta5.Construction
variable {p : ℕ} [Fact p.Prime]

def localNormalizationUnit (N p : ℕ) : ℚ :=
  ((N.factorial : ℚ) ^ 2) * ((p : ℚ) ^ (2 * (N / p)))⁻¹

theorem localNormalizationUnit_integral {N : ℕ} (hN : N < p ^ 2) :
    PadicLower p 0 (localNormalizationUnit N p) := by
  have h := (factorial_square_padicLower (p := p) hN).mul
    (inverse_prime_power_padicLower (p := p) (2 * (N / p)))
  simpa [localNormalizationUnit] using h

theorem signedPhysicalRoot_square {N : ℕ} (i : Fin N × Bool) :
    (signedPhysicalRoot i : ℚ) ^ 2 = ((i.1.val + 1 : ℕ) : ℚ) ^ 2 := by
  rcases i with ⟨i, b⟩
  cases b <;> simp [signedPhysicalRoot] <;> ring

theorem second_residue_local_identity {N c : ℕ} (g : ℚ[X])
    {i : Fin N × Bool}
    (hi : i ∈ divisibleRootIndices p c Finset.univ (@signedPhysicalRoot N))
    (hmult : physicalLocalMultiplicity N p c = 2 * (N / p) + 2 * (N % p) / p) :
    (p : ℚ) ^ (2 + 2 * (N % p) / p) * (normalizedResidue N g (i.1.val + 1)).coeff 0 =
      (-2 * (signedPhysicalRoot i : ℚ)) * localNormalizationUnit N p *
      (g.comp ((localAffine p c) ^ 2)).eval (physicalLocalLevel p c i : ℚ) *
      ((physicalLocalMonic N p c).derivative.eval (physicalLocalLevel p c i : ℚ))⁻¹ *
      ((physicalLocalUnit N p c).eval (physicalLocalLevel p c i : ℚ))⁻¹ *
      ((p : ℚ) ^ 3 * Zeta3.Construction.stieltjesConstant (i.1.val + 1)) := by
  let x : ℚ := signedPhysicalRoot i
  let D : ℚ := (denominator N).derivative.eval (-x ^ 2)
  let L : ℚ := (physicalLocalMonic N p c).derivative.eval (physicalLocalLevel p c i : ℚ)
  let U : ℚ := (physicalLocalUnit N p c).eval (physicalLocalLevel p c i : ℚ)
  have hp0 : (p : ℚ) ≠ 0 := by exact_mod_cast (Fact.out : p.Prime).ne_zero
  have hx0 : x ≠ 0 := by
    dsimp only [x]
    exact_mod_cast signedPhysicalRoot_ne_zero i
  have hfac : (-2 * (p : ℚ) * x) ≠ 0 := mul_ne_zero (mul_ne_zero (by norm_num) hp0) hx0
  have hiden := denominator_derivative_local_identity (p := p) N (c : ℤ) hi
  rw [hmult] at hiden
  change (-2 * (p : ℚ) * x) * D = (p : ℚ) ^ (2 * (N / p) + 2 * (N % p) / p) * L * U at hiden
  have hD : D = ((p : ℚ) ^ (2 * (N / p) + 2 * (N % p) / p) * L * U) /
      (-2 * (p : ℚ) * x) := (eq_div_iff hfac).mpr (by rw [mul_comm]; exact hiden)
  have hDinv : D⁻¹ = (-2 * (p : ℚ) * x) *
      ((p : ℚ) ^ (2 * (N / p) + 2 * (N % p) / p))⁻¹ * L⁻¹ * U⁻¹ := by
    rw [hD, inv_div, div_eq_mul_inv, mul_inv_rev, mul_inv_rev]
    ring
  have hscale : (p : ℚ) ^ (2 + 2 * (N % p) / p) * (N.factorial : ℚ) ^ 2 *
      (-2 * (p : ℚ) * x) * ((p : ℚ) ^ (2 * (N / p) + 2 * (N % p) / p))⁻¹ =
      (-2 * x) * localNormalizationUnit N p * (p : ℚ) ^ 3 := by
    unfold localNormalizationUnit
    rw [pow_add, pow_add]
    field_simp
    <;> ring
  have heval : (g.comp ((localAffine p c) ^ 2)).eval (physicalLocalLevel p c i : ℚ) =
      g.eval (x ^ 2) := by
    simp only [eval_comp, eval_pow, localAffine, eval_add, eval_C, eval_mul, eval_X]
    rw [physicalLocalLevel_reconstruct hi]
  have hsquare := signedPhysicalRoot_square i
  have hcoef : (normalizedResidue N g (i.1.val + 1)).coeff 0 =
      ((N.factorial : ℚ) ^ 2 * g.eval (x ^ 2) * D⁻¹) *
        Zeta3.Construction.stieltjesConstant (i.1.val + 1) := by
    simp only [normalizedResidue, coeff_C_mul, Zeta3.Construction.stieltjes, coeff_add,
      coeff_C_zero, coeff_mul_C, coeff_X_zero, zero_mul, add_zero, div_eq_mul_inv, D, pole, x, hsquare]
  rw [hcoef, hDinv, heval]
  change _ = (-2 * x) * localNormalizationUnit N p * g.eval (x ^ 2) * L⁻¹ * U⁻¹ * _
  linear_combination g.eval (x ^ 2) * L⁻¹ * U⁻¹ *
    Zeta3.Construction.stieltjesConstant (i.1.val + 1) * hscale

theorem second_residue_reduction_at_signed_node {N c : ℕ} {g : ℚ[X]}
    (hp : 2 < p) (hc : 0 < c) (hcp : 2 * c < p)
    (hsmall : 2 * N < p ^ 2)
    (hglocal : PolynomialPadicLower p 0 (g.comp ((localAffine p c) ^ 2)))
    {i : Fin N × Bool}
    (hi : i ∈ divisibleRootIndices p c Finset.univ (@signedPhysicalRoot N))
    (hmult : physicalLocalMultiplicity N p c = 2 * (N / p) + 2 * (N % p) / p) :
    PadicLower p 1
      ((p : ℚ) ^ (2 + 2 * (N % p) / p) * (normalizedResidue N g (i.1.val + 1)).coeff 0 -
       (2 * (signedPhysicalRoot i : ℚ) ^ 3 * localNormalizationUnit N p *
        (g.comp ((localAffine p c) ^ 2)).eval (physicalLocalLevel p c i : ℚ) *
        ((physicalLocalMonic N p c).derivative.eval (physicalLocalLevel p c i : ℚ))⁻¹ *
        ((physicalLocalUnit N p c).eval (physicalLocalLevel p c i : ℚ))⁻¹ *
        harmonicLevel (physicalLocalLevel p c i))) := by
  have himem : i.1.val + 1 ∈ reflectedNodes N p c := by
    apply mem_reflectedNodes.mpr
    refine ⟨by omega, by have := i.1.isLt; omega, ?_⟩
    have hd := (divisible_signedPhysicalRoot_iff hc (by omega) i).mp (mem_filter.mp hi).2
    cases hb : i.2 <;> simp only [hb, Bool.false_eq_true, if_false, if_true] at hd
    · exact Or.inr hd
    · exact Or.inl hd
  have hnot := reflected_node_not_dvd hc hcp himem
  have hH := stieltjesConstant_prime_reduction hp hnot
  have hG := hglocal.eval_integral (padicLower_int (physicalLocalLevel p c i))
  have hU := physicalLocalUnit_eval_inverse_integral (p := p) N (c : ℤ) (physicalLocalLevel p c i)
  have hL := physicalLocalMonic_derivative_inverse_integral hsmall hi
  have hx : PadicLower p 0 (-2 * (signedPhysicalRoot i : ℚ)) := by
    simpa only [Int.cast_mul, Int.cast_neg, Int.cast_ofNat] using
      padicLower_int (p := p) (-2 * signedPhysicalRoot i)
  have hmul := (((hx.mul (localNormalizationUnit_integral (p := p) (N := N) (by omega))).mul hG).mul hL).mul hU
  have h := hmul.mul hH
  rw [second_residue_local_identity g hi hmult, harmonicLevel_physical hc (by omega) hi]
  have hidx : i.1.val + 1 - 1 = i.1.val := by omega
  rw [hidx] at h
  have hs := signedPhysicalRoot_square i
  convert h.mono (by norm_num : (1 : ℤ) ≤ 0 + 0 + 0 + 0 + 0 + 3) using 1
  rw [← hs]
  ring

def secondLocalMultiplier (N p c : ℕ) : ℚ :=
  2 * (c : ℚ) ^ 3 * localNormalizationUnit N p * ((physicalLocalUnit N p c).coeff 0)⁻¹

theorem secondLocalMultiplier_integral {N c : ℕ} (hsmall : N < p ^ 2) :
    PadicLower p 0 (secondLocalMultiplier N p c) := by
  have hc3 : PadicLower p 0 ((c : ℚ) ^ 3) := padicIntegral_pow (padicLower_nat c) 3
  simpa only [secondLocalMultiplier, zero_add, Nat.cast_ofNat] using
    (((padicLower_nat (p := p) 2).mul hc3).mul (localNormalizationUnit_integral hsmall)).mul
      (physicalLocalUnit_inverse_constant_integral N (c : ℤ))

theorem second_residue_reduction_to_features {N c : ℕ} {g F : ℚ[X]}
    (hp : 2 < p) (hc : 0 < c) (hcp : 2 * c < p)
    (hsmall : 2 * N < p ^ 2)
    (hglocal : PolynomialPadicLower p 0 (g.comp ((localAffine p c) ^ 2)))
    (hF : PolynomialPadicLower p 0 F)
    (hGF : PolynomialPadicLower p 1 (g.comp ((localAffine p c) ^ 2) - F))
    {i : Fin N × Bool}
    (hi : i ∈ divisibleRootIndices p c Finset.univ (@signedPhysicalRoot N))
    (hmult : physicalLocalMultiplicity N p c = 2 * (N / p) + 2 * (N % p) / p) :
    PadicLower p 1
      ((p : ℚ) ^ (2 + 2 * (N % p) / p) * (normalizedResidue N g (i.1.val + 1)).coeff 0 -
        secondLocalMultiplier N p c * F.eval (physicalLocalLevel p c i : ℚ) *
        ((physicalLocalMonic N p c).derivative.eval (physicalLocalLevel p c i : ℚ))⁻¹ *
        harmonicLevel (physicalLocalLevel p c i)) := by
  have hfirst := second_residue_reduction_at_signed_node hp hc hcp hsmall hglocal hi hmult
  let a := physicalLocalLevel p (c : ℤ) i
  let x : ℚ := signedPhysicalRoot i
  let G := g.comp ((localAffine p c) ^ 2)
  let U := physicalLocalUnit N p (c : ℤ)
  have hGv : PadicLower p 0 (G.eval (a : ℚ)) := hglocal.eval_integral (padicLower_int a)
  have hFv := hF.eval_integral (padicLower_int a)
  have hGFv : PadicLower p 1 (G.eval (a : ℚ) - F.eval (a : ℚ)) := by
    simpa only [eval_sub] using hGF.eval_integral (padicLower_int a)
  have hUinv := physicalLocalUnit_eval_inverse_integral (p := p) N (c : ℤ) a
  have hU0inv := physicalLocalUnit_inverse_constant_integral (p := p) N (c : ℤ)
  have hUcong := physicalLocalUnit_eval_inverse_congr_constant (p := p) N (c : ℤ) a
  have hGU := padicLower_mul_sub_mul hGv hU0inv hGFv hUcong
  have hx : PadicLower p 0 x := padicLower_int (signedPhysicalRoot i)
  have hcint : PadicLower p 0 (c : ℚ) := padicLower_nat c
  have hxc : PadicLower p 1 (x - (c : ℚ)) := by
    have he := physicalLocalLevel_mul hi
    have hd : (p : ℤ) ∣ signedPhysicalRoot i - (c : ℤ) := ⟨a, he.symm⟩
    simpa only [Int.cast_sub, Int.cast_natCast] using padicLower_int_of_dvd (p := p) _ hd
  have hcube := padicLower_pow_sub_pow hx hcint hxc 3
  have hcore := padicLower_mul_sub_mul (padicIntegral_pow hx 3)
    (by simpa only [zero_add] using hFv.mul hU0inv) hcube hGU
  have hH : PadicLower p 0 (harmonicLevel a) := by
    rw [harmonicLevel_physical hc (by omega) hi]
    apply harmonicThree_integral
    have hiN := i.1.isLt
    apply (Nat.div_lt_iff_lt_mul (Fact.out : p.Prime).pos).mpr
    nlinarith
  have hL := physicalLocalMonic_derivative_inverse_integral hsmall hi
  have hscalar := (((padicLower_nat (p := p) 2).mul
    (localNormalizationUnit_integral (p := p) (N := N) (by omega))).mul hL).mul hH
  have hsecond := hscalar.mul hcore
  have h := hfirst.add (by simpa only [zero_add] using hsecond)
  convert h using 1
  dsimp only [secondLocalMultiplier, a, x, G, U]
  ring

end Zeta3.Arithmetic

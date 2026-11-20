import Zeta3.Arithmetic.SecondInterpolation
import Zeta3.Arithmetic.LocalUnitReduction

/-! The actual central truncation on a nonmaximal reflected class is its
interpolation remainder, up to a constant multiple of the local nodal
polynomial modulo p. -/
noncomputable section
namespace Zeta3.Arithmetic
open Polynomial Finset OddZeta.FourValue Zeta5.Arithmetic Zeta5.Construction
variable {p : ℕ} [Fact p.Prime]

theorem double_div_eq (N : ℕ) :
    2 * N / p = 2 * (N / p) + 2 * (N % p) / p := by
  have hp : 0 < p := (Fact.out : p.Prime).pos
  have hd := Nat.mod_add_div N p
  conv_lhs => rw [← hd]
  rw [mul_add, show 2 * (p * (N / p)) = p * (2 * (N / p)) by ring,
    Nat.add_mul_div_left _ _ hp]
  omega

theorem physicalLocalMultiplicity_nonmaximal {N c : ℕ}
    (hc : 0 < c) (hcp : 2 * c < p) (hodd : p % 2 = 1)
    (hnot : c ∉ maximalReflectedClasses N p) :
    physicalLocalMultiplicity N p c = 2 * N / p := by
  rw [physicalLocalMultiplicity_eq_reflectedSize N p c hc hcp, double_div_eq]
  have hne : reflectedSize N p c ≠ 2 * (N / p) + 1 + 2 * (N % p) / p := by
    intro he
    apply hnot
    exact mem_filter.mpr ⟨mem_Icc.mpr ⟨hc, by omega⟩, he⟩
  have hp : 0 < p := (Fact.out : p.Prime).pos
  rw [reflected_epsilon N p hp] at hne ⊢
  unfold reflectedSize at hne ⊢
  split_ifs at hne ⊢ <;> omega

theorem eval_modByMonic_of_root (G L : ℚ[X]) (x : ℚ) (hroot : L.eval x = 0) :
    (G %ₘ L).eval x = G.eval x := by
  have h := congrArg (fun P : ℚ[X] => P.eval x) (modByMonic_add_div G L)
  simpa only [eval_add, eval_mul, hroot, zero_mul, add_zero] using h

theorem centralExpansion_nonmaximal_reduction {N c : ℕ} {g : ℚ[X]}
    (hg : SquareValuedLower p 0 g) (hsmall : 2 * N < p ^ 2)
    (hc : 0 < c) (hcp : 2 * c < p) (hodd : p % 2 = 1)
    (hnot : c ∉ maximalReflectedClasses N p)
    (hglocal : PolynomialPadicLower p 0 (g.comp ((localAffine p c) ^ 2))) :
    ∃ a : ℚ, PadicLower p 0 a ∧ PolynomialPadicLower p 1
      ((centralExpansion g N).comp ((localAffine p c) ^ 2) -
        (g.comp ((localAffine p c) ^ 2)) %ₘ physicalLocalMonic N p c -
        C a * physicalLocalMonic N p c) := by
  let L := physicalLocalMonic N p (c : ℤ)
  let G := g.comp ((localAffine p c) ^ 2)
  let I := (centralExpansion g N).comp ((localAffine p c) ^ 2)
  let P := I - G %ₘ L
  let s := divisibleRootIndices p c Finset.univ (@signedPhysicalRoot N)
  have hIv : IntegerValuedAt p ((centralExpansion g N).comp (X ^ 2)) := by
    intro z
    simpa only [eval_comp, eval_pow, eval_X] using centralExpansion_squareValuedLower hg N z
  have hdeg : ((centralExpansion g N).comp (X ^ 2)).natDegree ≤ 2 * N := by
    rw [natDegree_comp, natDegree_X_pow]
    have := centralExpansion_natDegree_le g N
    omega
  have hIint : PolynomialPadicLower p 0 I := by
    simpa only [I, comp_assoc, pow_comp, X_comp] using
      integerValuedAt_local_integral hIv hdeg hsmall (c : ℤ)
  have hRint : PolynomialPadicLower p 0 (G %ₘ L) :=
    polynomialPadicLower_modByMonic hglocal (physicalLocalMonic_integral N _)
      (physicalLocalMonic_monic N _)
  have hPint : PolynomialPadicLower p 0 P := by
    exact hIint.add hRint.neg
  have hsize : s.card = 2 * N / p := physicalLocalMultiplicity_nonmaximal hc hcp hodd hnot
  refine ⟨P.coeff s.card, hPint _, ?_⟩
  apply polynomialPadicLower_sub_top_nodal s (physicalLocalLevel p (c : ℤ)) P L
    (physicalLocalMonic_monic N _) (physicalLocalMonic_natDegree N _)
    (fun _ hi => physicalLocalMonic_eval_level N _ hi)
    (physicalLocalLevel_unit_differences (c : ℤ) hsmall)
  · intro k hk
    have hhigh := integerValuedAt_local_coeff_precision hIv hdeg hsmall (c : ℤ) k
    simp only [comp_assoc, pow_comp, X_comp] at hhigh
    have hRdeg : (G %ₘ L).degree < s.card := by
      have h := degree_modByMonic_lt G (physicalLocalMonic_monic (p := p) N (c : ℤ))
      rw [degree_eq_natDegree (physicalLocalMonic_monic (p := p) N (c : ℤ)).ne_zero,
        physicalLocalMonic_natDegree] at h
      exact h
    have hRzero : (G %ₘ L).coeff k = 0 := by
      rw [degree_lt_iff_coeff_zero] at hRdeg
      exact hRdeg k (by omega)
    simp only [P, coeff_sub, hRzero, sub_zero]
    exact hhigh.mono (by omega)
  · intro i hi
    have hroot := physicalLocalMonic_eval_level (p := p) N (c : ℤ) hi
    have he := centralSquareLocal_eval_level N g c hi
    simp only [P, eval_sub, eval_modByMonic_of_root G L _ hroot]
    rw [he, sub_self]
    exact PadicLower.zero _

theorem centralQuotient_nonmaximal_second_reduction {N c : ℕ} {g : ℚ[X]}
    (hg : SquareValuedLower p 0 g) (hsmall : 2 * N < p ^ 2)
    (hc : 0 < c) (hcp : 2 * c < p) (hodd : p % 2 = 1)
    (hnot : c ∉ maximalReflectedClasses N p)
    (hglocal : PolynomialPadicLower p 0 (g.comp ((localAffine p c) ^ 2))) :
    ∃ a : ℚ, PadicLower p 0 a ∧ PolynomialPadicLower p 1
      (C ((p : ℚ) ^ (2 * (N % p) / p)) *
        (C ((N.factorial : ℚ) ^ 2) * centralQuotient N g).comp (-(localAffine p c) ^ 2) -
       C (((N.factorial : ℚ) ^ 2) * ((p : ℚ) ^ (2 * (N / p)))⁻¹ *
           ((physicalLocalUnit N p c).coeff 0)⁻¹) *
         ((g.comp ((localAffine p c) ^ 2)) / physicalLocalMonic N p c - C a)) := by
  let e := 2 * (N % p) / p
  let d := 2 * (N / p) + e
  let L := physicalLocalMonic N p (c : ℤ)
  let U := physicalLocalUnit N p (c : ℤ)
  let G := g.comp ((localAffine p c) ^ 2)
  let I := (centralExpansion g N).comp ((localAffine p c) ^ 2)
  let Q := (centralQuotient N g).comp (-(localAffine p c) ^ 2)
  let F := G - I
  let V := C ((p : ℚ) ^ d) * Q
  obtain ⟨a, ha, hI⟩ := centralExpansion_nonmaximal_reduction hg hsmall hc hcp hodd hnot hglocal
  have hp0 : (p : ℚ) ≠ 0 := by exact_mod_cast (Fact.out : p.Prime).ne_zero
  have hLint := physicalLocalMonic_integral (p := p) N (c : ℤ)
  have hLmonic := physicalLocalMonic_monic (p := p) N (c : ℤ)
  have hUint := physicalLocalUnit_integral (p := p) N (c : ℤ)
  have hU0 := physicalLocalUnit_constant_ne_zero (p := p) N (c : ℤ)
  have hUinv := physicalLocalUnit_inverse_constant_integral (p := p) N (c : ℤ)
  have hFcongr : PolynomialPadicLower p 1 (F - L * (G /ₘ L - C a)) := by
    have hdiv := modByMonic_add_div G L
    have he : F - L * (G /ₘ L - C a) = -(I - G %ₘ L - C a * L) := by
      dsimp [F]
      linear_combination -hdiv
    rw [he]
    exact hI.neg
  have hIv : IntegerValuedAt p ((centralExpansion g N).comp (X ^ 2)) := by
    intro z
    simpa only [eval_comp, eval_pow, eval_X] using centralExpansion_squareValuedLower hg N z
  have hdeg : ((centralExpansion g N).comp (X ^ 2)).natDegree ≤ 2 * N := by
    rw [natDegree_comp, natDegree_X_pow]
    have := centralExpansion_natDegree_le g N
    omega
  have hIint : PolynomialPadicLower p 0 I := by
    simpa only [I, comp_assoc, pow_comp, X_comp] using
      integerValuedAt_local_integral hIv hdeg hsmall (c : ℤ)
  have hF : PolynomialPadicLower p 0 F := hglocal.add hIint.neg
  have hmult : physicalLocalMultiplicity N p (c : ℤ) = d := by
    rw [physicalLocalMultiplicity_nonmaximal hc hcp hodd hnot, double_div_eq]
  have htail : G - I = (denominator N).comp (-(localAffine p c) ^ 2) * Q := by
    rw [← centralTail_comp_square, centralTail_eq_denominator_mul_quotient, mul_comp]
  have hfactor : F = L * U * V := by
    dsimp only [F, V]
    rw [htail, denominator_local_factorization, hmult]
    dsimp only [L, U]
    ring
  have hVint : PolynomialPadicLower p 0 V := by
    have hUV := polynomialPadicLower_quotient_of_monic hF hLint hLmonic
      (show F = L * (U * V) by rw [hfactor]; ring)
    exact polynomialPadicLower_quotient_of_unit_constant hUV hUint hU0 hUinv rfl
  have hVc := localQuotient_congr_polynomial hVint hLint hLmonic hUinv hU0
    (physicalLocalUnit_sub_constant N (c : ℤ)) hFcongr hfactor
  let u : ℚ := ((N.factorial : ℚ) ^ 2) * ((p : ℚ) ^ (2 * (N / p)))⁻¹
  have hu : PadicLower p 0 u := by
    have h := (factorial_square_padicLower (p := p) (by omega : N < p ^ 2)).mul
      (inverse_prime_power_padicLower (p := p) (2 * (N / p)))
    simpa [u] using h
  refine ⟨a, ha, ?_⟩
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
  rw [mul_sub, he, ← mul_assoc, ← C_mul, divByMonic_eq_div G hLmonic] at h
  convert h using 1
  · norm_num
  · simp only [e, Q, G, L, U, u, mul_comp, C_comp, C_mul]
    ring

end Zeta3.Arithmetic

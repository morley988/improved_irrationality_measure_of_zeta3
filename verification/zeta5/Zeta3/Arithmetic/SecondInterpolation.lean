import Zeta3.Arithmetic.LocalPrecision
import Zeta5.Arithmetic.LocalRestriction

/-!
# Second-order interpolation on maximal physical classes

A polynomial with one additional retained coefficient and vanishing values
is congruent to a constant times the local nodal polynomial. Applied to the
central truncation divided by p, this is the interpolation fact needed to
remove maximal classes from the second reduced form.
-/
noncomputable section
namespace Zeta3.Arithmetic
open Polynomial Finset OddZeta.FourValue Zeta5.Arithmetic Zeta5.Construction
variable {p : ℕ} [Fact p.Prime]

theorem polynomialPadicLower_sub_top_nodal {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (v : ι → ℤ) (P L : ℚ[X])
    (hL : L.Monic) (hdegree : L.natDegree = s.card)
    (hLzero : ∀ i ∈ s, L.eval (v i : ℚ) = 0)
    (hdiff : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → ¬(p : ℤ) ∣ v i - v j)
    (hhigh : ∀ k, s.card < k → PadicLower p 1 (P.coeff k))
    (heval : ∀ i ∈ s, PadicLower p 1 (P.eval (v i : ℚ))) :
    PolynomialPadicLower p 1 (P - C (P.coeff s.card) * L) := by
  apply polynomialPadicLower_of_high_coeff_of_eval s v hdiff
  · intro k hk
    rw [coeff_sub, coeff_C_mul]
    by_cases he : k = s.card
    · rw [he, ← hdegree, hL.coeff_natDegree, mul_one, sub_self]
      exact PadicLower.zero _
    · have hk' : L.natDegree < k := by omega
      rw [coeff_eq_zero_of_natDegree_lt hk', mul_zero, sub_zero]
      exact hhigh k (by omega)
  · intro i hi
    simpa only [eval_sub, eval_mul, eval_C, hLzero i hi, mul_zero, sub_zero] using heval i hi

theorem physicalLocalMonic_eval_level (N : ℕ) (c : ℤ) {i : Fin N × Bool}
    (hi : i ∈ divisibleRootIndices p c Finset.univ (@signedPhysicalRoot N)) :
    (physicalLocalMonic N p c).eval (physicalLocalLevel p c i : ℚ) = 0 := by
  unfold physicalLocalMonic localMonicFactor
  rw [eval_prod]
  apply prod_eq_zero hi
  simp only [eval_add, eval_X, eval_C, physicalLocalLevel]
  have he : (c - signedPhysicalRoot i) / (p : ℤ) =
      -((signedPhysicalRoot i - c) / (p : ℤ)) := by
    rw [show c - signedPhysicalRoot i = -(signedPhysicalRoot i - c) by ring,
      Int.neg_ediv_of_dvd (by
        simpa only [neg_sub] using dvd_neg.mpr (mem_filter.mp hi).2)]
  rw [he, Int.cast_neg, add_neg_cancel]

theorem physicalLocalMultiplicity_maximal {N c : ℕ}
    (hc : c ∈ maximalReflectedClasses N p) :
    physicalLocalMultiplicity N p c = 2 * N / p + 1 := by
  obtain ⟨hci, he⟩ := mem_filter.mp hc
  obtain ⟨hc0, hch⟩ := mem_Icc.mp hci
  rw [physicalLocalMultiplicity_eq_reflectedSize N p c hc0 (by omega), he]
  have hp : 0 < p := (Fact.out : p.Prime).pos
  have hd := Nat.mod_add_div N p
  conv_rhs => rw [← hd]
  rw [mul_add, show 2 * (p * (N / p)) = p * (2 * (N / p)) by ring,
    Nat.add_mul_div_left _ _ hp]
  omega

theorem centralExpansion_maximal_second_reduction {N c : ℕ} {g : ℚ[X]}
    (hg : SquareValuedLower p 0 g) (hsmall : 2 * N < p ^ 2)
    (hc : c ∈ maximalReflectedClasses N p)
    (hkernel : PolynomialPadicLower p 2 (g.comp ((localAffine p c) ^ 2))) :
    ∃ a : ℚ, PadicLower p 0 a ∧
      PolynomialPadicLower p 1
        (C ((p : ℚ)⁻¹) * (centralExpansion g N).comp ((localAffine p c) ^ 2) -
          C a * physicalLocalMonic N p c) := by
  let I := (centralExpansion g N).comp ((localAffine p c) ^ 2)
  let J := C ((p : ℚ)⁻¹) * I
  let s := divisibleRootIndices p c Finset.univ (@signedPhysicalRoot N)
  have hI : PolynomialPadicLower p 1 I :=
    centralExpansion_maximal_local_gain hg hsmall hc (hkernel.mono (by norm_num))
  have hinv : PadicLower p (-1) ((p : ℚ)⁻¹) := by
    simpa using inverse_prime_power_padicLower (p := p) 1
  have hJ : PolynomialPadicLower p 0 J := by
    simpa [J] using (PolynomialPadicLower.constant hinv).mul hI
  refine ⟨J.coeff s.card, hJ _, ?_⟩
  apply polynomialPadicLower_sub_top_nodal s (physicalLocalLevel p (c : ℤ)) J
    (physicalLocalMonic N p c) (physicalLocalMonic_monic N _)
    (physicalLocalMonic_natDegree N _) (fun _ hi => physicalLocalMonic_eval_level N _ hi)
    (physicalLocalLevel_unit_differences (c : ℤ) hsmall)
  · intro k hk
    have hsize : s.card = 2 * N / p + 1 := physicalLocalMultiplicity_maximal hc
    have hIv : IntegerValuedAt p ((centralExpansion g N).comp (X ^ 2)) := by
      intro z
      simpa only [eval_comp, eval_pow, eval_X] using centralExpansion_squareValuedLower hg N z
    have hdeg : ((centralExpansion g N).comp (X ^ 2)).natDegree ≤ 2 * N := by
      rw [natDegree_comp, natDegree_X_pow]
      have := centralExpansion_natDegree_le g N
      omega
    have hprec := integerValuedAt_local_coeff_precision hIv hdeg hsmall (c : ℤ) k
    simp only [comp_assoc, pow_comp, X_comp] at hprec
    have hv := hinv.mul hprec
    change PadicLower p 1 (J.coeff k)
    simpa only [J, I, coeff_C_mul] using hv.mono (by omega)
  · intro i hi
    have he : I.eval (physicalLocalLevel p c i : ℚ) =
        (g.comp ((localAffine p c) ^ 2)).eval (physicalLocalLevel p c i : ℚ) :=
      centralSquareLocal_eval_level N g c hi
    have hv := hinv.mul (hkernel.eval_integral (padicLower_int (physicalLocalLevel p c i)))
    simpa only [J, eval_mul, eval_C, he, show (-1 + 2 : ℤ) = 1 by norm_num] using hv

end Zeta3.Arithmetic

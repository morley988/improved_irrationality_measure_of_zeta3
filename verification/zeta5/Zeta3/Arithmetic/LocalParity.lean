import Zeta3.Arithmetic.LocalSecondForm

/-! Exact reflection cancellation for the physical eta=1 local form.
The cancellation is proved over the rationals before residue reduction. -/
noncomputable section
namespace Zeta3.Arithmetic
open Polynomial Finset OddZeta.FourValue Zeta5.Arithmetic Zeta5.Construction

theorem derivative_eval_reflection {L : ℚ[X]} (hL : L.comp localReflection = L) (x : ℚ) :
    L.derivative.eval (-1 - x) = -L.derivative.eval x := by
  have h := congrArg derivative hL
  rw [derivative_comp_reflection] at h
  have he := congrArg (fun P : ℚ[X] => P.eval x) h
  simp only [eval_neg, eval_comp, localReflection_eval] at he
  linarith

theorem nodeCubicFunctional_reflection (S : Finset ℤ) (L P : ℚ[X])
    (hS : ∀ a ∈ S, -1 - a ∈ S) (hmonic : L.Monic)
    (hL : L.comp localReflection = L) :
    nodeCubicFunctional S L (P.comp localReflection) = -nodeCubicFunctional S L P := by
  unfold nodeCubicFunctional
  rw [bernoulliFunctional_derivative_div_reflection P L hmonic hL]
  have hs : (∑ a ∈ S, (P.comp localReflection).eval (a : ℚ) *
      (L.derivative.eval (a : ℚ))⁻¹ * harmonicLevel a) =
      -(∑ a ∈ S, P.eval (a : ℚ) * (L.derivative.eval (a : ℚ))⁻¹ * harmonicLevel a) := by
    rw [← sum_neg_distrib]
    apply sum_bij (fun a _ => -1 - a)
    · intro a ha
      exact hS a ha
    · intro a ha b hb he
      omega
    · intro b hb
      refine ⟨-1 - b, hS b hb, ?_⟩
      omega
    · intro a ha
      simp only [eval_comp, localReflection_eval, Int.cast_sub, Int.cast_neg, Int.cast_one,
        derivative_eval_reflection hL, inv_neg, harmonicLevel_reflection]
      ring
  rw [hs]
  ring

theorem nodeCubicFunctional_invariant_zero (S : Finset ℤ) (L P : ℚ[X])
    (hS : ∀ a ∈ S, -1 - a ∈ S) (hmonic : L.Monic)
    (hL : L.comp localReflection = L) (hP : P.comp localReflection = P) :
    nodeCubicFunctional S L P = 0 := by
  have h := nodeCubicFunctional_reflection S L P hS hmonic hL
  rw [hP] at h
  linarith

variable {p : ℕ} [Fact p.Prime]

theorem physicalLevels_nonmaximal_low (N c : ℕ)
    (hc : 0 < c) (hcp : 2 * c < p) (hodd : p % 2 = 1)
    (hσ : 2 * (N % p) < p) (hnot : c ∉ maximalReflectedClasses N p) :
    physicalLevels N p c = Icc (-((N / p : ℕ) : ℤ)) (((N / p : ℕ) : ℤ) - 1) := by
  have hcσ : N % p < c := by
    by_contra hle
    apply hnot
    apply mem_filter.mpr
    refine ⟨mem_Icc.mpr ⟨hc, by omega⟩, ?_⟩
    rw [reflected_epsilon N p (Fact.out : p.Prime).pos, if_pos hσ]
    unfold reflectedSize
    split_ifs <;> omega
  exact physicalLevels_low_interval N c hc hcp hσ hcσ

theorem physicalLocalCubicFunctional_reflection (N c : ℕ) (P : ℚ[X])
    (hc : 0 < c) (hcp : 2 * c < p) (hodd : p % 2 = 1)
    (hσ : 2 * (N % p) < p) (hnot : c ∉ maximalReflectedClasses N p) :
    physicalLocalCubicFunctional N p c (P.comp localReflection) =
      -physicalLocalCubicFunctional N p c P := by
  apply nodeCubicFunctional_reflection
  · intro a ha
    rw [physicalLevels_nonmaximal_low N c hc hcp hodd hσ hnot] at ha ⊢
    simp only [mem_Icc] at ha ⊢
    omega
  · exact physicalLocalMonic_monic N (c : ℤ)
  · rw [physicalLocalMonic_nonmaximal_low N c hc hcp hodd hσ hnot]
    exact evenLocalRootPolynomial_reflection _

theorem physicalLocalCubicFunctional_same_parity_zero (N c a b i j : ℕ)
    (hc : 0 < c) (hcp : 2 * c < p) (hodd : p % 2 = 1)
    (hσ : 2 * (N % p) < p) (hnot : c ∉ maximalReflectedClasses N p)
    (hij : Even (i + j)) :
    physicalLocalCubicFunctional N p c
      ((evenLocalRootPolynomial a * centeredLocalMonomial i) *
       (evenLocalRootPolynomial b * centeredLocalMonomial j)) = 0 := by
  let P := (evenLocalRootPolynomial a * centeredLocalMonomial i) *
    (evenLocalRootPolynomial b * centeredLocalMonomial j)
  have hP : P.comp localReflection = P := by
    simp only [P, mul_comp, evenLocalRootPolynomial_reflection, centeredLocalMonomial_reflection]
    have he : C ((-1 : ℚ) ^ i) * C ((-1 : ℚ) ^ j) = (1 : ℚ[X]) := by
      rw [← map_mul, ← pow_add, hij.neg_one_pow, map_one]
    calc
      _ = (C ((-1 : ℚ) ^ i) * C ((-1 : ℚ) ^ j)) *
        ((evenLocalRootPolynomial a * centeredLocalMonomial i) *
         (evenLocalRootPolynomial b * centeredLocalMonomial j)) := by ring
      _ = _ := by rw [he, one_mul]
  have h := physicalLocalCubicFunctional_reflection N c P hc hcp hodd hσ hnot
  rw [hP] at h
  linarith

end Zeta3.Arithmetic

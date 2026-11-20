import Zeta3.Arithmetic.BernoulliReflection
import Zeta3.Construction.Functional

/-!
# The rational cubic functional on a reflected interval

The interval {-q-1,...,q} is enumerated by the pairs (j,-j-1).
This makes both its exact node polynomial and the harmonic weight symmetry
explicit. The resulting functional is the eta=1 universal cubic functional.
-/
noncomputable section
namespace Zeta3.Arithmetic
open Polynomial Finset Zeta5.Arithmetic Zeta3.Construction

def evenLocalRootPolynomial (a : ℕ) : ℚ[X] :=
  ∏ j ∈ range a, (X + C (j + 1 : ℚ)) * (X - C (j : ℚ))

theorem evenLocalRootPolynomial_monic (a : ℕ) : (evenLocalRootPolynomial a).Monic := by
  apply monic_prod_of_monic
  intro j hj
  exact (monic_X_add_C _).mul (monic_X_sub_C _)

theorem evenLocalRootPolynomial_reflection (a : ℕ) :
    (evenLocalRootPolynomial a).comp localReflection = evenLocalRootPolynomial a := by
  rw [evenLocalRootPolynomial, Polynomial.prod_comp]
  apply prod_congr rfl
  intro j hj
  simp only [mul_comp, add_comp, sub_comp, X_comp, C_comp, localReflection]
  simp only [map_add, map_one]
  ring

theorem evenLocalRootPolynomial_derivative_reflection (a : ℕ) (x : ℚ) :
    (evenLocalRootPolynomial a).derivative.eval (-1 - x) =
      -(evenLocalRootPolynomial a).derivative.eval x := by
  have h := congrArg derivative (evenLocalRootPolynomial_reflection a)
  rw [derivative_comp_reflection] at h
  have he := congrArg (fun P : ℚ[X] => P.eval x) h
  simp only [eval_neg, eval_comp, localReflection_eval] at he
  linarith

def universalCubicFunctional (q : ℕ) (P : ℚ[X]) : ℚ :=
  (∑ j ∈ range (q + 1), harmonicThree j *
    (P.eval (j : ℚ) / (evenLocalRootPolynomial (q + 1)).derivative.eval (j : ℚ) +
     P.eval (-1 - (j : ℚ)) /
       (evenLocalRootPolynomial (q + 1)).derivative.eval (-1 - (j : ℚ)))) +
  (1 / 2) * bernoulliFunctional ((P / evenLocalRootPolynomial (q + 1)).derivative)

theorem universalCubicFunctional_reflection (q : ℕ) (P : ℚ[X]) :
    universalCubicFunctional q (P.comp localReflection) = -universalCubicFunctional q P := by
  unfold universalCubicFunctional
  rw [bernoulliFunctional_derivative_div_reflection P _
    (evenLocalRootPolynomial_monic _) (evenLocalRootPolynomial_reflection _)]
  have hs : (∑ j ∈ range (q + 1), harmonicThree j *
      ((P.comp localReflection).eval (j : ℚ) /
        (evenLocalRootPolynomial (q + 1)).derivative.eval (j : ℚ) +
       (P.comp localReflection).eval (-1 - (j : ℚ)) /
        (evenLocalRootPolynomial (q + 1)).derivative.eval (-1 - (j : ℚ)))) =
      -(∑ j ∈ range (q + 1), harmonicThree j *
      (P.eval (j : ℚ) / (evenLocalRootPolynomial (q + 1)).derivative.eval (j : ℚ) +
       P.eval (-1 - (j : ℚ)) /
        (evenLocalRootPolynomial (q + 1)).derivative.eval (-1 - (j : ℚ)))) := by
    rw [← sum_neg_distrib]
    apply sum_congr rfl
    intro j hj
    simp only [eval_comp, localReflection_eval,
      evenLocalRootPolynomial_derivative_reflection, div_neg]
    rw [show (-1 - (-1 - (j : ℚ))) = j by ring]
    ring
  rw [hs]
  ring

theorem universalCubicFunctional_invariant_zero (q : ℕ) (P : ℚ[X])
    (hP : P.comp localReflection = P) : universalCubicFunctional q P = 0 := by
  have h := universalCubicFunctional_reflection q P
  rw [hP] at h
  linarith

def centeredLocalMonomial (j : ℕ) : ℚ[X] := (X + C (1 / 2 : ℚ)) ^ j

theorem centeredLocalMonomial_reflection (j : ℕ) :
    (centeredLocalMonomial j).comp localReflection =
      C ((-1 : ℚ) ^ j) * centeredLocalMonomial j := by
  unfold centeredLocalMonomial
  rw [pow_comp, add_comp, X_comp, C_comp]
  have he : localReflection + C (1 / 2 : ℚ) = -(X + C (1 / 2 : ℚ)) := by
    unfold localReflection
    have hc : C (1 / 2 : ℚ) + C (1 / 2 : ℚ) = (1 : ℚ[X]) := by
      rw [← map_add]; norm_num
    linear_combination hc
  rw [he, neg_pow]
  simp

theorem universalCubicFunctional_same_parity_zero (q a b i j : ℕ)
    (hij : Even (i + j)) :
    universalCubicFunctional q
      ((evenLocalRootPolynomial a * centeredLocalMonomial i) *
       (evenLocalRootPolynomial b * centeredLocalMonomial j)) = 0 := by
  apply universalCubicFunctional_invariant_zero
  simp only [mul_comp, evenLocalRootPolynomial_reflection, centeredLocalMonomial_reflection]
  have he : C ((-1 : ℚ) ^ i) * C ((-1 : ℚ) ^ j) = (1 : ℚ[X]) := by
    rw [← map_mul, ← pow_add, hij.neg_one_pow, map_one]
  calc
    _ = (C ((-1 : ℚ) ^ i) * C ((-1 : ℚ) ^ j)) *
      ((evenLocalRootPolynomial a * centeredLocalMonomial i) *
       (evenLocalRootPolynomial b * centeredLocalMonomial j)) := by ring
    _ = _ := by rw [he, one_mul]

end Zeta3.Arithmetic

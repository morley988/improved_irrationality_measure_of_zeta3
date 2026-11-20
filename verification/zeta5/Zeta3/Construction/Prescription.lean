import Zeta3.Construction.Functional

/-!
# Reproduction of the cubic simple-pole prescription

The fixed-denominator implementation is checked on the simple poles.  Thus
both defining parts of the manuscript's functional (polynomial moments and
simple-pole values) agree with the actual linear map used in the determinant.
-/

noncomputable section
namespace Zeta3.Construction
open Polynomial
open Zeta5.Construction

def simplePoleNumerator (N i : ℕ) : ℚ[X] :=
  denominator N / (X - C (pole (i + 1)))

theorem simplePoleNumerator_eq_nodal_erase {N i : ℕ} (hi : i < N) :
    simplePoleNumerator N i =
      Lagrange.nodal ((Finset.range N).erase i) (fun j => pole (j + 1)) := by
  rw [simplePoleNumerator, denominator_eq_nodal]
  exact (Lagrange.nodal_erase_eq_nodal_div (Finset.mem_range.mpr hi)).symm

theorem simplePoleNumerator_quotient_zero {N i : ℕ} (hi : i < N) :
    simplePoleNumerator N i / denominator N = 0 := by
  rw [← divByMonic_eq_div _ (denominator_monic N)]
  apply (divByMonic_eq_zero_iff (denominator_monic N)).mpr
  rw [simplePoleNumerator_eq_nodal_erase hi, denominator_eq_nodal,
    Lagrange.degree_nodal, Lagrange.degree_nodal]
  exact_mod_cast Finset.card_erase_lt_of_mem (Finset.mem_range.mpr hi)

theorem simplePoleNumerator_eval_self {N i : ℕ} (hi : i < N) :
    (simplePoleNumerator N i).eval (pole (i + 1)) =
      (denominator N).derivative.eval (pole (i + 1)) := by
  rw [simplePoleNumerator_eq_nodal_erase hi, denominator_eq_nodal]
  exact (Lagrange.eval_nodal_derivative_eval_node_eq
    (s := Finset.range N) (v := fun j : ℕ => pole (j + 1)) (i := i)
    (Finset.mem_range.mpr hi)).symm

theorem simplePoleNumerator_eval_other {N i j : ℕ} (hi : i < N) (hj : j < N)
    (hji : j ≠ i) :
    (simplePoleNumerator N i).eval (pole (j + 1)) = 0 := by
  rw [simplePoleNumerator_eq_nodal_erase hi]
  exact Lagrange.eval_nodal_at_node
    (s := (Finset.range N).erase i) (v := fun k : ℕ => pole (k + 1)) (i := j)
    (Finset.mem_erase.mpr ⟨hji, Finset.mem_range.mpr hj⟩)

/-- The cubic simple-pole value is reproduced exactly by the implementation. -/
theorem numeratorFunctional_simplePole_prescription {N i : ℕ} (hi : i < N) :
    numeratorFunctional N (simplePoleNumerator N i) = stieltjes (i + 1) := by
  rw [numeratorFunctional_apply, simplePoleNumerator_quotient_zero hi]
  simp only [polynomialMoment, sum_zero_index, C_0, zero_add]
  rw [Finset.sum_eq_single i]
  · rw [simplePoleNumerator_eval_self hi,
      div_self (denominator_derivative_at_pole_ne_zero hi), C_1, one_mul]
  · intro j hj hji
    rw [simplePoleNumerator_eval_other hi (Finset.mem_range.mp hj) hji,
      zero_div, C_0, zero_mul]
  · intro hnot
    exact False.elim (hnot (Finset.mem_range.mpr hi))

end Zeta3.Construction

import Zeta5.Arithmetic.BernoulliDistribution
import Mathlib.Algebra.Polynomial.FieldDivision

/-! Exact reflection of Bernoulli evaluation and polynomial division.
These identities underlie the parity improvement in the second layer. -/
noncomputable section
namespace Zeta3.Arithmetic
open Polynomial Finset Zeta5.Arithmetic

def localReflection : ℚ[X] := -1 - X

@[simp] theorem localReflection_comp_self :
    localReflection.comp localReflection = X := by
  simp [localReflection, sub_comp]

@[simp] theorem localReflection_derivative : localReflection.derivative = -1 := by
  simp [localReflection]

@[simp] theorem localReflection_eval (x : ℚ) : localReflection.eval x = -1 - x := by
  simp [localReflection]

theorem bernoulliFunctional_reflection (P : ℚ[X]) :
    bernoulliFunctional (P.comp localReflection) = bernoulliFunctional P := by
  let L : ℚ[X] →ₗ[ℚ] ℚ :=
    bernoulliFunctional.comp ((Polynomial.aeval localReflection).toLinearMap)
  have he : L = bernoulliFunctional := by
    apply bernoulliFunctional_unique
    intro Q
    change bernoulliFunctional ((Q.comp (X + 1) - Q).comp localReflection) = _
    have hid : (Q.comp (X + 1) - Q).comp localReflection =
        -((Q.comp (-X)).comp (X + 1) - Q.comp (-X)) := by
      simp only [sub_comp, comp_assoc]
      have h₁ : (X + 1 : ℚ[X]).comp localReflection = -X := by
        simp [localReflection, add_comp]; ring
      have h₂ : (-X : ℚ[X]).comp (X + 1) = localReflection := by
        simp [localReflection, neg_comp]; ring
      rw [h₁, h₂]
      ring
    rw [hid, map_neg, bernoulliFunctional_difference, derivative_comp]
    simp
  exact congrArg (fun F : ℚ[X] →ₗ[ℚ] ℚ => F P) he

theorem derivative_comp_reflection (P : ℚ[X]) :
    (P.comp localReflection).derivative = -(P.derivative.comp localReflection) := by
  rw [derivative_comp, localReflection_derivative]
  simp

theorem degree_comp_reflection (P : ℚ[X]) :
    (P.comp localReflection).degree = P.degree := by
  have hd : localReflection.degree = 1 := by
    rw [localReflection, show (-1 - X : ℚ[X]) = C (-1) + C (-1) * X by simp; ring]
    simpa using degree_add_eq_right_of_degree_lt (by simp : (C (-1) : ℚ[X]).degree < (C (-1) * X : ℚ[X]).degree)
  rw [degree_comp (by rw [hd]; decide), hd, mul_one]

theorem div_comp_reflection (P L : ℚ[X]) (hL : L.Monic)
    (hLS : L.comp localReflection = L) :
    (P.comp localReflection) / L = (P / L).comp localReflection := by
  have h := div_modByMonic_unique ((P /ₘ L).comp localReflection)
    ((P %ₘ L).comp localReflection) hL
    ⟨by
      calc
        _ = ((P %ₘ L) + L * (P /ₘ L)).comp localReflection := by
          rw [add_comp, mul_comp, hLS]
        _ = P.comp localReflection := by rw [modByMonic_add_div]
      , by rw [degree_comp_reflection]; exact degree_modByMonic_lt P hL⟩
  simpa only [divByMonic_eq_div _ hL] using h.1

theorem bernoulliFunctional_derivative_div_reflection (P L : ℚ[X]) (hL : L.Monic)
    (hLS : L.comp localReflection = L) :
    bernoulliFunctional (((P.comp localReflection) / L).derivative) =
      -bernoulliFunctional ((P / L).derivative) := by
  rw [div_comp_reflection P L hL hLS, derivative_comp_reflection, map_neg,
    bernoulliFunctional_reflection]

end Zeta3.Arithmetic

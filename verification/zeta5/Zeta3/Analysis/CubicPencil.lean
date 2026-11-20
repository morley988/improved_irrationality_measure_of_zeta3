import Zeta3.Analysis.CubicPushforward
import Zeta5.Analysis.PhysicalMeasurePencil

/-!
# Cubic integral interpretation from the explicit Stieltjes identity

The actual cubic density and moments have already been proved. The one
remaining identity at positive integer poles is an explicit proposition,
subsequently discharged in CubicStieltjes. This file declares no axiom.
-/

noncomputable section
namespace Zeta3.Analysis.PhysicalMeasure
open Real Set MeasureTheory Filter Polynomial Zeta3.Construction
open Zeta5.Construction (denominator pole)
open scoped Topology BigOperators

/-- The one remaining analytic identity at the poles needed by the pencil.
This is a proposition, not an assumption or axiom of the development. -/
def StieltjesAtPositiveIntegers (z : ℝ) : Prop :=
  ∀ i : ℕ, 0 < i → stieltjesTransform (i : ℝ) = (stieltjes i).eval₂ (Rat.castHom ℝ) z

/-- Once the explicit Stieltjes identity is proved, the whole fixed-denominator
functional has its intended integral interpretation. -/
theorem momentFunctional_eq_numeratorFunctional {z : ℝ}
    (hStieltjes : StieltjesAtPositiveIntegers z) (N : ℕ) (P : ℚ[X]) :
    momentFunctional N (P.map (Rat.castHom ℝ)) =
      (numeratorFunctional N P).eval₂ (Rat.castHom ℝ) z := by
  let a (i : ℕ) : ℝ :=
    ((P.eval (pole (i + 1)) / (denominator N).derivative.eval (pole (i + 1)) : ℚ) : ℝ)
  have hi (i : ℕ) : Integrable (fun t : ℝ => a i / (t + ((i + 1 : ℕ) : ℝ) ^ 2))
      physicalMeasure := by
    simpa only [div_eq_mul_inv, one_mul] using
      (physicalMeasure_stieltjes_integrable (y := ((i + 1 : ℕ) : ℝ)) (by positivity)).const_mul (a i)
  rw [momentFunctional_eq_measure_integral]
  calc
    _ = ∫ t : ℝ, ((P / denominator N).map (Rat.castHom ℝ)).eval t +
        ∑ i ∈ Finset.range N, a i / (t + ((i + 1 : ℕ) : ℝ) ^ 2) ∂physicalMeasure := by
      apply integral_congr_ae
      filter_upwards [physicalMeasure_ae_pos] with t ht
      exact Zeta5.Analysis.PhysicalMeasure.real_partialFractions N P ht.le
    _ = (Zeta3.Construction.polynomialMoment (P / denominator N) : ℝ) +
        ∑ i ∈ Finset.range N, a i * stieltjesTransform ((i + 1 : ℕ) : ℝ) := by
      rw [integral_add (physicalMeasure_polynomial_integrable _)
        (integrable_finsetSum _ (fun i _ => hi i)), physicalMeasure_polynomial_integral,
        integral_finsetSum _ (fun i _ => hi i)]
      congr 1
      apply Finset.sum_congr rfl
      intro i hi'
      simp only [div_eq_mul_inv, one_mul, integral_const_mul, stieltjesTransform]
    _ = _ := by
      rw [numeratorFunctional_apply]
      simp only [eval₂_add, eval₂_C, eval₂_finsetSum, eval₂_mul]
      congr 1
      apply Finset.sum_congr rfl
      intro i hi'
      rw [hStieltjes (i + 1) (by omega)]
      rfl

end Zeta3.Analysis.PhysicalMeasure

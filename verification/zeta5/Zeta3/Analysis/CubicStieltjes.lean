import Zeta3.Analysis.CubicStieltjesCoth
import Zeta3.Analysis.CubicZetaTail
import Zeta3.Analysis.CubicPencil

/-!
# The exact physical cubic Stieltjes identity

The cubic rational functional is identified with its actual positive measure
at ζ(3). All convergence, termwise integration, two Laplace integrations by
parts, coth partial fractions, and Cauchy integrals have been proved.
-/

noncomputable section
namespace Zeta3.Analysis.PhysicalMeasure
open Real Set MeasureTheory Polynomial Zeta3.Construction
open scoped BigOperators

theorem cothSecondTerm_integral (n : ℕ) {y : ℝ} (hy : 0 < y) :
    (∫ x : ℝ in Ioi 0, cothSecondTerm n y x) =
      Real.pi / (((n + 1 : ℕ) : ℝ) + y) ^ 3 :=
  Zeta3.Analysis.product_secondCauchyKernel_integral (by positivity) hy

theorem stieltjesTransform_hurwitz {y : ℝ} (hy : 0 < y) :
    stieltjesTransform y = y ^ 2 * hurwitzThree y - 1 / (2 * y) - 1 / 2 := by
  rw [stieltjesTransform_coth hy, Zeta3.Analysis.secondCauchyKernel_integral hy,
    Zeta3.Analysis.linear_secondCauchyKernel_integral hy]
  have hsum : (∑' n : ℕ, ∫ x : ℝ in Ioi 0, cothSecondTerm n y x) =
      Real.pi * (hurwitzThree y - 1 / y ^ 3) := by
    calc
      _ = ∑' n : ℕ, Real.pi * (1 / (((n + 1 : ℕ) : ℝ) + y) ^ 3) := by
        apply tsum_congr
        intro n
        rw [cothSecondTerm_integral n hy]
        ring
      _ = Real.pi * ∑' n : ℕ, 1 / (((n + 1 : ℕ) : ℝ) + y) ^ 3 := tsum_mul_left
      _ = _ := by rw [hurwitzThree_shift hy]; ring
  rw [hsum]
  field_simp [hy.ne', Real.pi_ne_zero]
  ring

theorem stieltjesTransform_nat {i : ℕ} (hi : 0 < i) :
    stieltjesTransform (i : ℝ) =
      (stieltjes i).eval₂ (Rat.castHom ℝ) (Zeta5.Endpoint.realZeta 3) := by
  rw [stieltjesTransform_hurwitz (by exact_mod_cast hi), hurwitzThree_nat hi]
  simp only [stieltjes, stieltjesConstant, eval₂_add, eval₂_C, eval₂_mul, eval₂_X,
    Rat.coe_castHom, Rat.cast_sub, Rat.cast_neg, Rat.cast_mul, Rat.cast_pow,
    Rat.cast_natCast, Rat.cast_div, Rat.cast_one, Rat.cast_ofNat]
  ring

theorem stieltjesAtPositiveIntegers_realZetaThree :
    StieltjesAtPositiveIntegers (Zeta5.Endpoint.realZeta 3) :=
  fun _ hi => stieltjesTransform_nat hi

theorem momentFunctional_eq_numeratorFunctional_realZetaThree (N : ℕ) (P : ℚ[X]) :
    momentFunctional N (P.map (Rat.castHom ℝ)) =
      (numeratorFunctional N P).eval₂ (Rat.castHom ℝ) (Zeta5.Endpoint.realZeta 3) :=
  momentFunctional_eq_numeratorFunctional stieltjesAtPositiveIntegers_realZetaThree N P

end Zeta3.Analysis.PhysicalMeasure

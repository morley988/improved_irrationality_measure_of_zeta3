import Zeta3.Construction.CenteredProducts

/-! Every rational function with an integer square-free denominator belongs
to the actual simple-pole subspace, including functions with a polynomial part. -/

noncomputable section
namespace Zeta3.Construction.Rational
open Polynomial
open scoped RatFunc
variable {K : Type*} [Field K] [CharZero K]

theorem integer_nodal_fraction_expansion (s : Finset ℤ) (p : K[X]) :
    algebraMap K[X] (RatFunc K) p /
        algebraMap K[X] (RatFunc K) (Lagrange.nodal s (Int.cast : ℤ → K)) =
      algebraMap K[X] (RatFunc K) (p / Lagrange.nodal s (Int.cast : ℤ → K)) +
        ∑ i ∈ s, (p.eval (i : K) /
          (Lagrange.nodal s (Int.cast : ℤ → K)).derivative.eval (i : K)) •
            rationalPole (i : K) 1 := by
  let D : K[X] := Lagrange.nodal s (Int.cast : ℤ → K)
  have hD : algebraMap K[X] (RatFunc K) D ≠ 0 :=
    RatFunc.algebraMap_ne_zero (Lagrange.nodal_monic (s := s) (v := Int.cast)).ne_zero
  have h := congrArg (algebraMap K[X] (RatFunc K))
    (Zeta5.Construction.partialFraction_polynomial_identity s (Int.cast : ℤ → K)
      Int.cast_injective.injOn p)
  change algebraMap K[X] (RatFunc K) p =
    algebraMap K[X] (RatFunc K) ((p / D) * D + ∑ i ∈ s,
      C (p.eval (i : K) / D.derivative.eval (i : K)) * (D / (X - C (i : K)))) at h
  simp only [map_add, map_mul, map_sum] at h
  change algebraMap K[X] (RatFunc K) p / algebraMap K[X] (RatFunc K) D = _
  rw [h, add_div, mul_div_cancel_right₀ _ hD, Finset.sum_div]
  congr 1
  apply Finset.sum_congr rfl
  intro i hi
  have he : algebraMap K[X] (RatFunc K) (D / (X - C (i : K))) /
      algebraMap K[X] (RatFunc K) D = rationalPole (i : K) 1 := by
    change algebraMap K[X] (RatFunc K)
        (Lagrange.nodal s (Int.cast : ℤ → K) / (X - C (i : K))) /
      algebraMap K[X] (RatFunc K) (Lagrange.nodal s (Int.cast : ℤ → K)) = _
    rw [← Lagrange.nodal_erase_eq_nodal_div (s := s) (v := (Int.cast : ℤ → K)) hi,
      Lagrange.nodal_eq_mul_nodal_erase (s := s) (v := (Int.cast : ℤ → K)) hi, map_mul]
    have hE : algebraMap K[X] (RatFunc K) (Lagrange.nodal (s.erase i) (Int.cast : ℤ → K)) ≠ 0 :=
      RatFunc.algebraMap_ne_zero (Lagrange.nodal_monic (s := s.erase i) (v := Int.cast)).ne_zero
    simp only [rationalPole, pow_one, div_eq_mul_inv, mul_inv_rev]
    rw [← mul_assoc, mul_inv_cancel₀ hE, one_mul]
  rw [mul_div_assoc, he, RatFunc.algebraMap_C, RatFunc.smul_eq_C_mul]

theorem integer_nodal_fraction_mem_simpleRational (s : Finset ℤ) (p : K[X]) :
    algebraMap K[X] (RatFunc K) p /
      algebraMap K[X] (RatFunc K) (Lagrange.nodal s (Int.cast : ℤ → K)) ∈ simpleRational := by
  rw [integer_nodal_fraction_expansion]
  apply simpleRational.add_mem (polynomial_mem_simpleRational _)
  apply simpleRational.sum_mem
  intro i hi
  exact simpleRational.smul_mem _ (pole_mem_simpleRational i)

theorem centered_fraction_mem_simpleRational (N : ℕ) (p : K[X]) :
    algebraMap K[X] (RatFunc K) p /
      algebraMap K[X] (RatFunc K) (centeredDenominator N) ∈ simpleRational := by
  rw [centeredDenominator_integerProduct]
  exact integer_nodal_fraction_mem_simpleRational (poleWindow N) p

end Zeta3.Construction.Rational

import Zeta3.Arithmetic.SecondInterpolation
import Zeta3.Arithmetic.LocalUnitReduction
import Zeta3.Arithmetic.HarmonicReduction

/-! Physical residues in local signed coordinates. The denominator's
local derivative and both inverse unit factors are proved from the exact
factorization; no asymptotic or modular identity is assumed. -/
noncomputable section
namespace Zeta3.Arithmetic
open Polynomial Finset OddZeta.FourValue Zeta5.Arithmetic Zeta5.Construction
variable {p : ℕ} [Fact p.Prime]

theorem physicalLocalMonic_eq_nodal (N : ℕ) (c : ℤ) :
    physicalLocalMonic N p c = Lagrange.nodal
      (divisibleRootIndices p c Finset.univ (@signedPhysicalRoot N))
      (fun i => (physicalLocalLevel p c i : ℚ)) := by
  unfold physicalLocalMonic localMonicFactor Lagrange.nodal
  apply prod_congr rfl
  intro i hi
  have he : (c - signedPhysicalRoot i) / (p : ℤ) =
      -((signedPhysicalRoot i - c) / (p : ℤ)) := by
    rw [show c - signedPhysicalRoot i = -(signedPhysicalRoot i - c) by ring,
      Int.neg_ediv_of_dvd (by
        simpa only [neg_sub] using dvd_neg.mpr (mem_filter.mp hi).2)]
  rw [he, Int.cast_neg, C_neg]
  rfl

theorem physicalLocalMonic_derivative_inverse_integral {N : ℕ} {c : ℤ}
    (hsmall : 2 * N < p ^ 2) {i : Fin N × Bool}
    (hi : i ∈ divisibleRootIndices p c Finset.univ (@signedPhysicalRoot N)) :
    PadicLower p 0 (((physicalLocalMonic N p c).derivative.eval
      (physicalLocalLevel p c i : ℚ))⁻¹) := by
  rw [physicalLocalMonic_eq_nodal, ← Lagrange.nodalWeight_eq_eval_derivative_nodal (v := fun j => (physicalLocalLevel p c j : ℚ)) hi]
  unfold Lagrange.nodalWeight
  have h := padicLower_prod (p := p)
    ((divisibleRootIndices p c Finset.univ (@signedPhysicalRoot N)).erase i)
    (fun j => ((physicalLocalLevel p c i : ℚ) - (physicalLocalLevel p c j : ℚ))⁻¹)
    (fun _ => 0) (by
      intro j hj
      obtain ⟨hji, hjs⟩ := mem_erase.mp hj
      have hdiff := physicalLocalLevel_unit_differences (p := p) c hsmall i hi j hjs hji.symm
      simpa only [Int.cast_sub] using inverse_int_integral_of_not_dvd (p := p) _ hdiff)
  simpa using h

theorem localUnitFactor_eval_inverse_integral {ι : Type*} [DecidableEq ι]
    (c a : ℤ) (s : Finset ι) (r : ι → ℤ) :
    PadicLower p 0 ((localUnitFactor p c s r).eval (a : ℚ))⁻¹ := by
  rw [localUnitFactor, eval_prod, ← prod_inv_distrib]
  have h := padicLower_prod (p := p) (s.filter (fun i => ¬(p : ℤ) ∣ c - r i))
    (fun i => ((localLinearFactor p c (r i)).eval (a : ℚ))⁻¹) (fun _ => 0) (by
      intro i hi
      have hnot := (mem_filter.mp hi).2
      have hnot' : ¬(p : ℤ) ∣ c + p * a - r i := by
        intro hd
        have h := dvd_sub hd (dvd_mul_right (p : ℤ) a)
        apply hnot
        have he : c + (p : ℤ) * a - r i - p * a = c - r i := by ring
        rwa [he] at h
      have hval : (localLinearFactor p c (r i)).eval (a : ℚ) = ((c + p * a - r i : ℤ) : ℚ) := by
        simp [localLinearFactor, localAffine]
      rw [hval]
      exact inverse_int_integral_of_not_dvd _ hnot')
  simpa using h

theorem physicalLocalUnit_eval_inverse_integral (N : ℕ) (c a : ℤ) :
    PadicLower p 0 ((physicalLocalUnit N p c).eval (a : ℚ))⁻¹ := by
  rw [physicalLocalUnit, eval_mul, eval_C, mul_inv_rev]
  have hs : PadicLower p 0 (((-1 : ℚ) ^ N)⁻¹) := by
    rw [← inv_pow]
    norm_num only [inv_neg, inv_one]
    simpa using padicLower_int (p := p) ((-1 : ℤ) ^ N)
  simpa only [zero_add] using (localUnitFactor_eval_inverse_integral (p := p) c a
    Finset.univ (@signedPhysicalRoot N)).mul hs

theorem physicalLocalUnit_eval_ne_zero (N : ℕ) (c a : ℤ) :
    (physicalLocalUnit N p c).eval (a : ℚ) ≠ 0 := by
  rw [physicalLocalUnit, eval_mul, eval_C]
  apply mul_ne_zero (pow_ne_zero _ (by norm_num))
  rw [localUnitFactor, eval_prod]
  apply prod_ne_zero_iff.mpr
  intro i hi hz
  have hz' : c + (p : ℤ) * a - signedPhysicalRoot i = 0 := by
    have he : (localLinearFactor p c (signedPhysicalRoot i)).eval (a : ℚ) =
        ((c + p * a - signedPhysicalRoot i : ℤ) : ℚ) := by simp [localLinearFactor, localAffine]
    rw [he] at hz
    exact_mod_cast hz
  have hd : (p : ℤ) ∣ c - signedPhysicalRoot i := by
    refine ⟨-a, ?_⟩
    linarith
  exact (mem_filter.mp hi).2 hd

theorem physicalLocalUnit_eval_congr_constant (N : ℕ) (c a : ℤ) :
    PadicLower p 1 ((physicalLocalUnit N p c).eval (a : ℚ) -
      (physicalLocalUnit N p c).coeff 0) := by
  simpa only [eval_sub, eval_C] using
    (physicalLocalUnit_sub_constant (p := p) N c).eval_integral (padicLower_int a)

theorem physicalLocalUnit_eval_inverse_congr_constant (N : ℕ) (c a : ℤ) :
    PadicLower p 1 (((physicalLocalUnit N p c).eval (a : ℚ))⁻¹ -
      ((physicalLocalUnit N p c).coeff 0)⁻¹) :=
  padicLower_inv_sub_inv (physicalLocalUnit_eval_ne_zero N c a)
    (physicalLocalUnit_constant_ne_zero N c)
    (physicalLocalUnit_eval_inverse_integral N c a)
    (physicalLocalUnit_inverse_constant_integral N c)
    (physicalLocalUnit_eval_congr_constant N c a)

theorem denominator_derivative_local_identity (N : ℕ) (c : ℤ)
    {i : Fin N × Bool}
    (hi : i ∈ divisibleRootIndices p c Finset.univ (@signedPhysicalRoot N)) :
    (-2 * (p : ℚ) * (signedPhysicalRoot i : ℚ)) *
      (denominator N).derivative.eval (-((signedPhysicalRoot i : ℚ) ^ 2)) =
      (p : ℚ) ^ physicalLocalMultiplicity N p c *
        (physicalLocalMonic N p c).derivative.eval (physicalLocalLevel p c i : ℚ) *
        (physicalLocalUnit N p c).eval (physicalLocalLevel p c i : ℚ) := by
  have h := congrArg (fun P : ℚ[X] => P.derivative.eval (physicalLocalLevel p c i : ℚ))
    (denominator_local_factorization (p := p) N c)
  have hroot := physicalLocalMonic_eval_level (p := p) N c hi
  have he : (localAffine p c).eval (physicalLocalLevel p c i : ℚ) = (signedPhysicalRoot i : ℚ) := by
    simpa only [localAffine, eval_add, eval_C, eval_mul, eval_X] using physicalLocalLevel_reconstruct hi
  have hAff : (localAffine p c).derivative = C (p : ℚ) := by simp [localAffine]
  simp only [derivative_comp, derivative_neg, derivative_pow, hAff, derivative_add, derivative_C,
    derivative_mul, derivative_X, zero_mul, mul_one, zero_add, eval_mul, eval_comp, eval_neg,
    eval_pow, eval_C, he, hroot, eval_add, mul_zero, add_zero, pow_one] at h
  norm_num only at h
  convert h using 1 <;> ring

end Zeta3.Arithmetic

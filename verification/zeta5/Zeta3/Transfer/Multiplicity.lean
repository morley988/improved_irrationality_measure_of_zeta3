import Zeta3.Transfer.IntegerJets
import Mathlib.Algebra.Polynomial.FieldDivision
import Mathlib.Algebra.Polynomial.Eval.SMul
import Mathlib.Tactic.Push

/-!
# From bounded root multiplicity to bounded nonzero integer jets

This is the algebraic link between a Pearson multiplicity theorem and the
analytic transfer theorem. The multiplicity bound itself remains an explicit
model-specific hypothesis.
-/

noncomputable section
namespace Zeta3.Transfer
open Polynomial

theorem hasseDeriv_map_int_real (P : ℤ[X]) (m : ℕ) :
    (hasseDeriv m P).map (Int.castRingHom ℝ) =
      hasseDeriv m (P.map (Int.castRingHom ℝ)) := by
  ext k
  simp [hasseDeriv_coeff]

theorem exists_nonzero_hasse_eval_of_rootMultiplicity_le
    (P : ℤ[X]) (x : ℝ) (B : ℕ) (hP : P ≠ 0)
    (hmult : (P.map (Int.castRingHom ℝ)).rootMultiplicity x ≤ B) :
    ∃ m ≤ B, (hasseDeriv m P).eval₂ (Int.castRingHom ℝ) x ≠ 0 := by
  by_contra h
  push Not at h
  have hmap : P.map (Int.castRingHom ℝ) ≠ 0 :=
    (Polynomial.map_ne_zero_iff (Int.cast_injective (α := ℝ))).mpr hP
  have hroot : B < (P.map (Int.castRingHom ℝ)).rootMultiplicity x := by
    apply Polynomial.lt_rootMultiplicity_of_isRoot_iterate_derivative hmap
    intro m hm
    change (((Polynomial.derivative : ℝ[X] → ℝ[X])^[m])
      (P.map (Int.castRingHom ℝ))).eval x = 0
    have hpoly : m.factorial • hasseDeriv m (P.map (Int.castRingHom ℝ)) =
        (Polynomial.derivative : ℝ[X] → ℝ[X])^[m]
          (P.map (Int.castRingHom ℝ)) := by
      simpa only [LinearMap.smul_apply] using
        congrFun (Polynomial.factorial_smul_hasseDeriv (R := ℝ) (k := m))
          (P.map (Int.castRingHom ℝ))
    rw [← hpoly, Polynomial.eval_smul, ← hasseDeriv_map_int_real, Polynomial.eval_map,
      h m hm, smul_zero]
  exact (not_lt_of_ge hmult) hroot

theorem hasBoundedRationalJets_of_rootMultiplicity_le
    (P : ℕ → ℤ[X]) (B : ℕ) (hP : ∀ n, P n ≠ 0)
    (hmult : ∀ (n : ℕ) (p : ℤ) (q : ℕ), 0 < q →
      ((P n).map (Int.castRingHom ℝ)).rootMultiplicity ((p : ℝ) / (q : ℝ)) ≤ B) :
    HasBoundedRationalJets P B := by
  intro n p q hq
  exact exists_nonzero_hasse_eval_of_rootMultiplicity_le (P n)
    ((p : ℝ) / (q : ℝ)) B (hP n) (hmult n p q hq)

end Zeta3.Transfer

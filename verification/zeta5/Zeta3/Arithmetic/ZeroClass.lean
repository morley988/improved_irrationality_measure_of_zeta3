import Zeta5.Arithmetic.ZeroClass
import Zeta3.Arithmetic.ReflectedMinors

/-! Both positive root factors contain X, giving four prime powers in
the zero residue class. The cubic Stieltjes term costs only one. -/
noncomputable section
namespace Zeta3.Arithmetic
open Polynomial OddZeta.FourValue Zeta5.Construction
open Zeta5.Arithmetic
variable {p : ℕ} [Fact p.Prime]

theorem positiveFactor_zero_class_gain (m i : ℕ) (hm : 0 < m) (hpi : p ∣ i) :
    PadicLower p 2 ((Zeta3.Construction.positiveFactor m).eval (pole i)) := by
  have hX : (X : ℤ[X]) ∣ commonRootInt m := by
    have h := Finset.dvd_prod_of_mem (fun a : ℕ => (X + C ((a : ℤ) ^ 2) : ℤ[X]))
      (Finset.mem_range.mpr hm)
    norm_num at h
    simpa [commonRootInt] using h
  obtain ⟨Q, hQ⟩ := hX
  have hi : PadicLower p 1 (i : ℚ) := by
    simpa using padicLower_int_of_dvd (p := p) (i : ℤ) (by exact_mod_cast hpi)
  have hi2 : PadicLower p 2 (-((i : ℚ) ^ 2)) := by
    simpa only [pow_two, show (1 : ℤ) + 1 = 2 from rfl] using (hi.mul hi).neg
  have hq := padicLower_int (p := p) (Q.eval (-((i : ℤ) ^ 2)))
  have hprod := hi2.mul hq
  rw [positiveFactor_eval_eq_integer, hQ, eval_mul, eval_X]
  push_cast
  simpa only [add_zero] using hprod

theorem zero_class_atom_integral (N m₁ m₂ r i : ℕ) (hp : 2 < p)
    (hm₁ : 0 < m₁) (hm₂ : 0 < m₂) (hi : 0 < i) (hiN : i ≤ N) (hpi : p ∣ i)
    (hN : N < 3 * p) (hsmall : 2 * N < p ^ 2) :
    ∀ k l : Fin r, PolynomialPadicLower p 0 (mixedMonomialAtom N m₁ m₂ r i k l) := by
  have hroot : PadicLower p 4
      ((Zeta3.Construction.positiveFactor m₁).eval (pole i) *
        (Zeta3.Construction.positiveFactor m₂).eval (pole i)) :=
    (positiveFactor_zero_class_gain m₁ i hm₁ hpi).mul
      (positiveFactor_zero_class_gain m₂ i hm₂ hpi)
  have hw := mixedMonomialAtomWeight_bound N m₁ m₂ i 4 (-1) 2 hroot
    (stieltjes_polynomial_multiple_p i hp hi (by omega) hpi)
    (denominator_derivative_zero_class_le_two N i hp hi hiN hpi hN hsmall)
  have hw0 : PolynomialPadicLower p 0 (mixedMonomialAtomWeight N m₁ m₂ i) := hw.mono (by norm_num)
  intro k l
  have hx := (polynomialPadicLower_integer_map (p := p)
    (C (-((i : ℤ) ^ 2)) : ℤ[X])).pow (k.val + l.val)
  have hx0 : PolynomialPadicLower p 0 (C ((pole i) ^ (k.val + l.val))) := by
    simpa [pole, map_pow] using hx
  exact hw0.mul hx0

end Zeta3.Arithmetic

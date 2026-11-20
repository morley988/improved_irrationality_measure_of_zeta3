import Zeta3.Construction.PearsonDegrees
import Mathlib.Analysis.Polynomial.Order
import Mathlib.Analysis.Complex.Polynomial.Basic

/-!
# Positivity forced by integral roots of the square lift

A positive real root t would produce the nonreal root i√t of p(-y²).
If all roots of that lift are integers, every real root of p is nonpositive.
Monicity then fixes the sign on the positive real axis.
-/

noncomputable section
namespace Zeta3.Transfer
open Polynomial
open Zeta3.Construction.Pearson

theorem real_root_nonpos_of_squareLift_roots_real (p : ℝ[X])
    (hroots : ∀ z : ℂ, (squareLift (p.map Complex.ofRealHom)).eval z = 0 → z.im = 0)
    (t : ℝ) (ht : p.eval t = 0) : t ≤ 0 := by
  by_contra hnonpos
  have hpos : 0 < t := lt_of_not_ge hnonpos
  let z : ℂ := Complex.I * (Real.sqrt t : ℂ)
  have hzsq : -(z ^ 2) = (t : ℂ) := by
    dsimp [z]
    rw [mul_pow, Complex.I_sq, neg_mul, one_mul, neg_neg, ← Complex.ofReal_pow,
      Real.sq_sqrt hpos.le]
  have hzroot : (squareLift (p.map Complex.ofRealHom)).eval z = 0 := by
    simp only [squareLift, eval_comp, eval_neg, eval_pow, eval_X, hzsq]
    have he := eval_map_apply (p := p) (f := Complex.ofRealHom) t
    simpa only [Complex.ofRealHom_eq_coe, ht, map_zero] using he
  have hzim := hroots z hzroot
  have hs : Real.sqrt t = 0 := by simpa [z] using hzim
  exact (ne_of_gt (Real.sqrt_pos.mpr hpos)) hs

theorem real_root_nonpos_of_squareLift_roots_integer (p : ℝ[X])
    (hroots : ∀ z : ℂ, (squareLift (p.map Complex.ofRealHom)).eval z = 0 →
      ∃ j : ℤ, z = (j : ℂ))
    (t : ℝ) (ht : p.eval t = 0) : t ≤ 0 := by
  apply real_root_nonpos_of_squareLift_roots_real p _ t ht
  intro z hz
  obtain ⟨j, rfl⟩ := hroots z hz
  simp

theorem monic_eval_pos_of_squareLift_roots_integer (p : ℝ[X]) (hp : p.Monic)
    (hroots : ∀ z : ℂ, (squareLift (p.map Complex.ofRealHom)).eval z = 0 →
      ∃ j : ℤ, z = (j : ℂ))
    (t : ℝ) (ht : 0 < t) : 0 < p.eval t := by
  apply zero_lt_eval_of_roots_lt_of_leadingCoeff_nonneg
  · intro y hy
    exact (real_root_nonpos_of_squareLift_roots_integer p hroots y hy).trans_lt ht
  · rw [hp.leadingCoeff]
    norm_num

theorem squareLift_map_real_complex (p : ℝ[X]) :
    (squareLift p).map Complex.ofRealHom = squareLift (p.map Complex.ofRealHom) := by
  simp [squareLift, Polynomial.map_comp]

theorem operatorQ_map_real_complex (B p : ℝ[X]) :
    (operatorQ B p).map Complex.ofRealHom =
      operatorQ (B.map Complex.ofRealHom) (p.map Complex.ofRealHom) := by
  simp [operatorQ, evenPart, Polynomial.map_comp]

theorem operatorR_map_real_complex (B p : ℝ[X]) :
    (operatorR B p).map Complex.ofRealHom =
      operatorR (B.map Complex.ofRealHom) (p.map Complex.ofRealHom) := by
  simp [operatorR, operatorD, Polynomial.map_comp]

theorem polynomialB_map_real_complex (N m₁ m₂ : ℕ) :
    (polynomialB N m₁ m₂ : ℝ[X]).map Complex.ofRealHom =
      (polynomialB N m₁ m₂ : ℂ[X]) := by
  simp [polynomialB]

theorem monic_eval_pos_of_cubic_divisibilities (N m₁ m₂ : ℕ)
    (p : ℝ[X]) (hp : p.Monic)
    (hQ : squareLift p ∣ operatorQ (polynomialB N m₁ m₂) (squareLift p))
    (hR : squareLift p ∣ operatorR (polynomialB N m₁ m₂) (squareLift p))
    (t : ℝ) (ht : 0 < t) : 0 < p.eval t := by
  apply monic_eval_pos_of_squareLift_roots_integer p hp _ t ht
  have hQc : squareLift (p.map Complex.ofRealHom) ∣
      operatorQ (polynomialB N m₁ m₂) (squareLift (p.map Complex.ofRealHom)) := by
    simpa only [squareLift_map_real_complex, operatorQ_map_real_complex,
      polynomialB_map_real_complex] using Polynomial.map_dvd Complex.ofRealHom hQ
  have hRc : squareLift (p.map Complex.ofRealHom) ∣
      operatorR (polynomialB N m₁ m₂) (squareLift (p.map Complex.ofRealHom)) := by
    simpa only [squareLift_map_real_complex, operatorR_map_real_complex,
      polynomialB_map_real_complex] using Polynomial.map_dvd Complex.ofRealHom hR
  have hne : squareLift (p.map Complex.ofRealHom) ≠ 0 := by
    intro hzero
    obtain hz | ⟨_, hc⟩ := comp_eq_zero_iff.mp hzero
    · exact (Polynomial.map_ne_zero hp.ne_zero) hz
    · have hh := congrArg (fun P : ℂ[X] => P.coeff 2) hc
      norm_num at hh
  intro z hz
  exact cubic_kernel_roots_integer N m₁ m₂ _ hne (squareLift_even _) hQc hRc hz

end Zeta3.Transfer

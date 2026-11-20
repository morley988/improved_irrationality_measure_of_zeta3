import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# The convex logarithmic kernel for the rational angular deficit

The factorization of the second derivative is an exact polynomial identity.
Consequently midpoint quadrature is a theorem, not a numerical convexity test.
-/

noncomputable section
open Set
namespace Zeta3.Analysis

def rationalAngularDen (y x : ℝ) : ℝ := (1-x^2)^2 + 2*y*x^2

def rationalAngularKernel (y x : ℝ) : ℝ :=
  Real.log (rationalAngularDen y x) - 2*Real.log (1-x^2)

def rationalAngularSlope (y x : ℝ) : ℝ :=
  4*y*x*(1+x^2)/((1-x^2)*rationalAngularDen y x)

def rationalAngularCurvatureNumerator (y x : ℝ) : ℝ :=
  (1-y/2)*(1-x^2)^2*(3*x^4+8*x^2+1) +
  (y/2)*(3*x^8+6*x^6+4*x^4+2*x^2+1)

def rationalAngularCurvature (y x : ℝ) : ℝ :=
  4*y*rationalAngularCurvatureNumerator y x / ((1-x^2)^2*rationalAngularDen y x^2)

theorem rationalAngular_one_sub_sq_pos {x : ℝ} (hx : 0 ≤ x) (hx1 : x < 1) :
    0 < 1-x^2 := by
  nlinarith [mul_pos (sub_pos.mpr hx1) (by linarith : 0 < 1+x)]

theorem rationalAngularDen_pos {y x : ℝ} (hy : 0 ≤ y) (hx : 0 ≤ x) (hx1 : x < 1) :
    0 < rationalAngularDen y x := by
  have ha := rationalAngular_one_sub_sq_pos hx hx1
  unfold rationalAngularDen
  positivity

theorem rationalAngularKernel_formula {y x : ℝ}
    (hy : 0 ≤ y) (hx : 0 ≤ x) (hx1 : x < 1) :
    rationalAngularKernel y x = Real.log (1+2*y*x^2/(1-x^2)^2) := by
  have ha := rationalAngular_one_sub_sq_pos hx hx1
  have hd := rationalAngularDen_pos hy hx hx1
  have hr : 1+2*y*x^2/(1-x^2)^2 = rationalAngularDen y x/(1-x^2)^2 := by
    unfold rationalAngularDen
    field_simp
  rw [hr, Real.log_div hd.ne' (pow_ne_zero 2 ha.ne'), Real.log_pow]
  rfl

theorem rationalAngularDen_hasDerivAt (y x : ℝ) :
    HasDerivAt (rationalAngularDen y) (4*x*(x^2+y-1)) x := by
  have h := (((hasDerivAt_id x).pow 2).const_sub 1).pow 2 |>.add
    (((hasDerivAt_id x).pow 2).const_mul (2*y))
  convert! h using 1
  simp only [Pi.pow_apply, Pi.mul_apply, Pi.add_apply, Pi.sub_apply, Pi.div_apply, id_eq, Nat.cast_ofNat, Nat.reduceSub, pow_one, mul_one, zero_sub]
  ring

theorem rationalAngularKernel_hasDerivAt {y x : ℝ}
    (hy : 0 ≤ y) (hx : 0 ≤ x) (hx1 : x < 1) :
    HasDerivAt (rationalAngularKernel y) (rationalAngularSlope y x) x := by
  have ha := rationalAngular_one_sub_sq_pos hx hx1
  have hd := rationalAngularDen_pos hy hx hx1
  have h := ((rationalAngularDen_hasDerivAt y x).log hd.ne').sub
    (((((hasDerivAt_id x).pow 2).const_sub 1).log ha.ne').const_mul 2)
  convert! h using 1
  simp only [Pi.pow_apply, Pi.mul_apply, Pi.add_apply, Pi.sub_apply, Pi.div_apply, id_eq, Nat.cast_ofNat, Nat.reduceSub, pow_one, mul_one, zero_sub]
  unfold rationalAngularSlope rationalAngularDen
  field_simp
  <;> ring

theorem rationalAngularSlope_hasDerivAt {y x : ℝ}
    (hy : 0 ≤ y) (hx : 0 ≤ x) (hx1 : x < 1) :
    HasDerivAt (rationalAngularSlope y) (rationalAngularCurvature y x) x := by
  have ha := rationalAngular_one_sub_sq_pos hx hx1
  have hd := rationalAngularDen_pos hy hx hx1
  have hn := ((hasDerivAt_id x).const_mul (4*y)).mul
    (((hasDerivAt_id x).pow 2).const_add 1)
  have hden := (((hasDerivAt_id x).pow 2).const_sub 1).mul
    (rationalAngularDen_hasDerivAt y x)
  have h := hn.div hden (mul_ne_zero ha.ne' hd.ne')
  convert! h using 1
  simp only [Pi.pow_apply, Pi.mul_apply, Pi.add_apply, Pi.sub_apply, Pi.div_apply, id_eq, Nat.cast_ofNat, Nat.reduceSub, pow_one, mul_one, zero_sub]
  unfold rationalAngularCurvature rationalAngularCurvatureNumerator rationalAngularDen
  field_simp
  <;> ring

theorem rationalAngularSlope_nonneg {y x : ℝ}
    (hy : 0 ≤ y) (hx : 0 ≤ x) (hx1 : x < 1) :
    0 ≤ rationalAngularSlope y x := by
  have ha := rationalAngular_one_sub_sq_pos hx hx1
  have hd := rationalAngularDen_pos hy hx hx1
  unfold rationalAngularSlope
  positivity

theorem rationalAngularCurvature_nonneg {y x : ℝ}
    (hy : 0 ≤ y) (hy2 : y ≤ 2) (hx : 0 ≤ x) (hx1 : x < 1) :
    0 ≤ rationalAngularCurvature y x := by
  have ha := rationalAngular_one_sub_sq_pos hx hx1
  have hd := rationalAngularDen_pos hy hx hx1
  have hc : 0 ≤ 1-y/2 := by linarith
  unfold rationalAngularCurvature rationalAngularCurvatureNumerator
  positivity

theorem rationalAngularKernel_continuousOn {y R : ℝ} (hy : 0 ≤ y) (hR : R < 1) :
    ContinuousOn (rationalAngularKernel y) (Icc 0 R) := by
  intro x hx
  exact (rationalAngularKernel_hasDerivAt hy hx.1 (hx.2.trans_lt hR)).continuousAt.continuousWithinAt

theorem rationalAngularKernel_monotoneOn {y R : ℝ} (hy : 0 ≤ y) (hR : R < 1) :
    MonotoneOn (rationalAngularKernel y) (Icc 0 R) := by
  apply monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc 0 R)
    (rationalAngularKernel_continuousOn hy hR)
    (fun x hx => (rationalAngularKernel_hasDerivAt hy
      (interior_subset hx).1 ((interior_subset hx).2.trans_lt hR)).hasDerivWithinAt)
  intro x hx
  exact rationalAngularSlope_nonneg hy (interior_subset hx).1 ((interior_subset hx).2.trans_lt hR)

theorem rationalAngularKernel_convexOn {y R : ℝ}
    (hy : 0 ≤ y) (hy2 : y ≤ 2) (hR : R < 1) :
    ConvexOn ℝ (Icc 0 R) (rationalAngularKernel y) := by
  apply convexOn_of_hasDerivWithinAt2_nonneg (convex_Icc 0 R)
    (rationalAngularKernel_continuousOn hy hR)
    (fun x hx => (rationalAngularKernel_hasDerivAt hy
      (interior_subset hx).1 ((interior_subset hx).2.trans_lt hR)).hasDerivWithinAt)
    (fun x hx => (rationalAngularSlope_hasDerivAt hy
      (interior_subset hx).1 ((interior_subset hx).2.trans_lt hR)).hasDerivWithinAt)
  intro x hx
  exact rationalAngularCurvature_nonneg hy hy2
    (interior_subset hx).1 ((interior_subset hx).2.trans_lt hR)

end Zeta3.Analysis

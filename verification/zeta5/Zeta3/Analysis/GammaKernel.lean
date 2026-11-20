import Zeta3.Analysis.PhysicalMass
import Mathlib.Analysis.SpecialFunctions.Log.Deriv

/-!
# Elementary kernels in the physical response formula

The logarithms are expanded for differentiation.  The formula lemmas identify
them with the literal quotients evaluated by the external Arb certificate.
-/

namespace Zeta3.Analysis

noncomputable section

def gammaRadical (a b : ℝ) : ℝ := Real.sqrt (a ^ 2 + b ^ 2)

def gammaLog (u b : ℝ) : ℝ := Real.log (u + gammaRadical u b) - Real.log b

def gammaArc (u b : ℝ) : ℝ := Real.log (b + gammaRadical u b) - Real.log u

def gammaAuxJ (u a b : ℝ) : ℝ :=
  Real.log (gammaRadical u b + gammaRadical a b) - Real.log (u + a) -
    (a / u) * (Real.log (u * gammaRadical a b + a * gammaRadical u b) -
      Real.log a - Real.log (gammaRadical u b + u))

theorem gammaRadical_pos {a b : ℝ} (ha : 0 < a) : 0 < gammaRadical a b := by
  unfold gammaRadical
  positivity

theorem gammaRadical_sq (a b : ℝ) : gammaRadical a b ^ 2 = a ^ 2 + b ^ 2 := by
  exact Real.sq_sqrt (by positivity)

theorem gammaRadical_hasDerivAt {a b : ℝ} (ha : 0 < a) :
    HasDerivAt (gammaRadical a) (b / gammaRadical a b) b := by
  have harg : a ^ 2 + b ^ 2 ≠ 0 := by positivity
  have d := (((hasDerivAt_id b).pow 2).const_add (a ^ 2)).sqrt harg
  convert! d using 1
  simp [gammaRadical]
  ring

theorem gammaLog_formula {u b : ℝ} (hu : 0 < u) (hb : 0 < b) :
    gammaLog u b = Real.log ((u + gammaRadical u b) / b) := by
  have hw := gammaRadical_pos (b := b) hu
  rw [Real.log_div (by positivity) hb.ne']
  rfl

theorem gammaArc_formula {u b : ℝ} (hu : 0 < u) (hb : 0 < b) :
    gammaArc u b = Real.log ((b + gammaRadical u b) / u) := by
  have hw := gammaRadical_pos (b := b) hu
  rw [Real.log_div (by positivity) hu.ne']
  rfl

theorem gammaAuxJ_formula {u a b : ℝ} (hu : 0 < u) (ha : 0 < a) :
    gammaAuxJ u a b =
      Real.log ((gammaRadical u b + gammaRadical a b) / (u + a)) -
      (a / u) * Real.log ((u * gammaRadical a b + a * gammaRadical u b) /
        (a * (gammaRadical u b + u))) := by
  have hw := gammaRadical_pos (b := b) hu
  have hr := gammaRadical_pos (b := b) ha
  rw [Real.log_div (by positivity) (by positivity),
    Real.log_div (by positivity) (by positivity),
    Real.log_mul ha.ne' (by positivity)]
  unfold gammaAuxJ
  ring

theorem gammaLog_hasDerivAt {u b : ℝ} (hu : 0 < u) (hb : 0 < b) :
    HasDerivAt (gammaLog u) (-u / (b * gammaRadical u b)) b := by
  have hw := gammaRadical_pos (b := b) hu
  have hsq := gammaRadical_sq u b
  have d := (((gammaRadical_hasDerivAt (b := b) hu).const_add u).log (by positivity)).sub
    ((hasDerivAt_id b).log hb.ne')
  convert! d using 1
  simp only [id_eq]
  field_simp
  nlinarith [hsq]

theorem gammaArc_hasDerivAt {u b : ℝ} (hu : 0 < u) (hb : 0 < b) :
    HasDerivAt (gammaArc u) (1 / gammaRadical u b) b := by
  have hw := gammaRadical_pos (b := b) hu
  have d := (((hasDerivAt_id b).add (gammaRadical_hasDerivAt (b := b) hu)).log
    (by simpa only [Pi.add_apply, id_eq] using (add_pos hb hw).ne')).sub_const (Real.log u)
  convert! d using 1
  simp only [Pi.add_apply, id_eq]
  field_simp
  ring

private theorem gamma_ratio_identity {u a w r b : ℝ}
    (hu : 0 < u) (ha : 0 < a) (hw : 0 < w) (hr : 0 < r)
    (hrel : w ^ 2 - r ^ 2 = u ^ 2 - a ^ 2) :
    (u * (b / r) + a * (b / w)) / (u * r + a * w) - (b / w) / (w + u) =
      u * b / (w * r * (r + a)) := by
  have hnum : ((u * w + a * r) * (w + u) - r * (u * r + a * w)) * (r + a) =
      u * (u * r + a * w) * (w + u) := by
    linear_combination u * r * hrel
  have haux : (u * w + a * r) / (r * (u * r + a * w)) - 1 / (w + u) =
      u / (r * (r + a)) := by
    rw [div_sub_div _ _ (by positivity : r * (u * r + a * w) ≠ 0)
      (by positivity : w + u ≠ 0)]
    simp only [mul_one]
    apply (div_eq_div_iff (by positivity) (by positivity)).2
    calc
      ((u * w + a * r) * (w + u) - r * (u * r + a * w)) * (r * (r + a)) =
          r * (((u * w + a * r) * (w + u) - r * (u * r + a * w)) * (r + a)) := by ring
      _ = r * (u * (u * r + a * w) * (w + u)) := by rw [hnum]
      _ = u * (r * (u * r + a * w) * (w + u)) := by ring
  calc
    _ = (b / w) * ((u * w + a * r) / (r * (u * r + a * w)) - 1 / (w + u)) := by
      field_simp
    _ = (b / w) * (u / (r * (r + a))) := by rw [haux]
    _ = _ := by field_simp

theorem gammaLogSum_hasDerivAt {u a b : ℝ} (hu : 0 < u) (ha : 0 < a) :
    HasDerivAt (fun x => Real.log (gammaRadical u x + gammaRadical a x))
      (b / (gammaRadical u b * gammaRadical a b)) b := by
  have hw := gammaRadical_pos (b := b) hu
  have hr := gammaRadical_pos (b := b) ha
  have d := ((gammaRadical_hasDerivAt (b := b) hu).add
    (gammaRadical_hasDerivAt (b := b) ha)).log
    (by simpa only [Pi.add_apply] using (add_pos hw hr).ne')
  convert! d using 1
  simp only [Pi.add_apply]
  field_simp
  ring

theorem gammaLogRatio_hasDerivAt {u a b : ℝ} (hu : 0 < u) (ha : 0 < a) :
    HasDerivAt (fun x => Real.log (u * gammaRadical a x + a * gammaRadical u x) -
      Real.log (gammaRadical u x + u))
      (u * b / (gammaRadical u b * gammaRadical a b * (gammaRadical a b + a))) b := by
  have hw := gammaRadical_pos (b := b) hu
  have hr := gammaRadical_pos (b := b) ha
  have dnum := ((gammaRadical_hasDerivAt (b := b) ha).const_mul u).add
    ((gammaRadical_hasDerivAt (b := b) hu).const_mul a)
  have d := (dnum.log (by
    change u * gammaRadical a b + a * gammaRadical u b ≠ 0
    positivity)).sub
    (((gammaRadical_hasDerivAt (b := b) hu).add_const u).log (by positivity))
  have hrel : gammaRadical u b ^ 2 - gammaRadical a b ^ 2 = u ^ 2 - a ^ 2 := by
    rw [gammaRadical_sq, gammaRadical_sq]
    ring
  convert! d using 1
  simpa only [Pi.add_apply] using (gamma_ratio_identity (b := b) hu ha hw hr hrel).symm

theorem gammaAuxJ_hasDerivAt {u a b : ℝ} (hu : 0 < u) (ha : 0 < a) :
    HasDerivAt (gammaAuxJ u a) (b / (gammaRadical u b * (gammaRadical a b + a))) b := by
  have hw := gammaRadical_pos (b := b) hu
  have hr := gammaRadical_pos (b := b) ha
  have d := ((gammaLogSum_hasDerivAt (b := b) hu ha).sub_const (Real.log (u + a))).sub
    (((gammaLogRatio_hasDerivAt (b := b) hu ha).sub_const (Real.log a)).const_mul (a / u))
  convert! d using 1
  · funext x
    simp only [Pi.sub_apply]
    unfold gammaAuxJ
    ring
  · field_simp
    ring

theorem gammaAuxJ_derivative_rewrite {u a b : ℝ}
    (hu : 0 < u) (ha : 0 < a) (hb : 0 < b) :
    b / (gammaRadical u b * (gammaRadical a b + a)) =
      (gammaRadical a b - a) / (b * gammaRadical u b) := by
  have hw := gammaRadical_pos (b := b) hu
  have hr := gammaRadical_pos (b := b) ha
  have hrat : b / (gammaRadical a b + a) = (gammaRadical a b - a) / b := by
    apply (div_eq_div_iff (by positivity) hb.ne').2
    nlinarith [gammaRadical_sq a b]
  calc
    _ = (b / (gammaRadical a b + a)) / gammaRadical u b := by field_simp
    _ = _ := by rw [hrat]; field_simp

theorem gammaLog_pos {u b : ℝ} (hu : 0 < u) (hb : 0 < b) : 0 < gammaLog u b := by
  have hw : b < gammaRadical u b := Zeta5.Analysis.sqrt_sum_sq_gt_right hu hb.le
  rw [gammaLog_formula hu hb]
  apply Real.log_pos
  apply (one_lt_div hb).2
  linarith

end

end Zeta3.Analysis

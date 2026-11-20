import Zeta3.Analysis.AngularMass
import Zeta5.Analysis.AbelKernel

/-!
# The angular equilibrium's positive radial density and Abel transform

The finite-charge angular measure can be constructed as a positive mixture
of squared arcsine laws.  This avoids an unproved Cauchy-transform inversion:
its radial density is half the derivative of the actual angular mass at a².
-/

noncomputable section
namespace Zeta3.Analysis
open Real Set MeasureTheory
open scoped BigOperators

variable {n : ℕ}

def angularRadialWeight (c : ℝ) (K e : Fin n → ℝ) (a : ℝ) : ℝ :=
  a * angularMassSlope c K e (a ^ 2)

def angularRadialBound (c : ℝ) (K e : Fin n → ℝ) : ℝ :=
  c / 2 + ∑ j, K j / (2 * e j)

def angularField (c : ℝ) (K e : Fin n → ℝ) (y : ℝ) : ℝ :=
  c * y + ∑ j, K j * Real.log (1 + y / e j)

def angularEquilibriumSlope (c : ℝ) (K e : Fin n → ℝ) (y : ℝ) : ℝ :=
  c * y / 2 + ∑ j, K j * y / (2 * (e j + y ^ 2))

theorem angularRadialWeight_continuous {c : ℝ} {K e : Fin n → ℝ}
    (he : ∀ j, 0 < e j) : Continuous (angularRadialWeight c K e) := by
  unfold angularRadialWeight angularMassSlope
  apply continuous_id.mul
  apply continuous_const.add
  apply continuous_finset_sum
  intro j _
  apply continuous_const.div
  · fun_prop
  · intro a
    have hs := angular_sqrt_pos (he j) (sq_nonneg a)
    exact mul_ne_zero (mul_ne_zero (by norm_num) (he j).ne') (pow_ne_zero _ hs.ne')

theorem angularRadialWeight_nonneg {c : ℝ} {K e : Fin n → ℝ}
    (hc : 0 < c) (hK : ∀ j, 0 ≤ K j) (he : ∀ j, 0 < e j)
    {a : ℝ} (ha : 0 ≤ a) : 0 ≤ angularRadialWeight c K e a := by
  exact mul_nonneg ha (angularMassSlope_pos hc hK he (sq_nonneg a)).le

theorem angularRadialBound_pos {c : ℝ} {K e : Fin n → ℝ}
    (hc : 0 < c) (hK : ∀ j, 0 ≤ K j) (he : ∀ j, 0 < e j) :
    0 < angularRadialBound c K e := by
  have hs : 0 ≤ ∑ j, K j / (2 * e j) := by
    apply Finset.sum_nonneg
    intro j _
    exact div_nonneg (hK j) (mul_nonneg (by norm_num) (he j).le)
  unfold angularRadialBound
  linarith

theorem angularRadialWeight_le {c : ℝ} {K e : Fin n → ℝ}
    (hc : 0 < c) (hK : ∀ j, 0 ≤ K j) (he : ∀ j, 0 < e j)
    {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) :
    angularRadialWeight c K e a ≤ b * angularRadialBound c K e := by
  have hs : angularMassSlope c K e (a ^ 2) ≤ angularRadialBound c K e := by
    unfold angularMassSlope angularRadialBound
    apply add_le_add_right
    apply Finset.sum_le_sum
    intro j _
    have hr : 1 ≤ Real.sqrt (1 + a ^ 2 / e j) := by
      apply Real.one_le_sqrt.2
      have h := div_nonneg (sq_nonneg a) (he j).le
      linarith
    apply div_le_div_of_nonneg_left (hK j) (mul_pos (by norm_num) (he j))
    have hp : 1 ≤ Real.sqrt (1 + a ^ 2 / e j) ^ 3 := one_le_pow₀ hr
    nlinarith [he j]
  exact (mul_le_mul_of_nonneg_left hs ha).trans
    (mul_le_mul_of_nonneg_right hab (angularRadialBound_pos hc hK he).le)

theorem angularRadialMass_hasDerivAt {c : ℝ} {K e : Fin n → ℝ}
    (he : ∀ j, 0 < e j) (a : ℝ) :
    HasDerivAt (fun x : ℝ => angularMass c K e (x ^ 2) / 2)
      (angularRadialWeight c K e a) a := by
  have dsq : HasDerivAt (fun x : ℝ => x ^ 2) (2 * a) a := by
    convert! ((hasDerivAt_id a).pow 2) using 1 <;> simp
  convert! ((angularMass_hasDerivAt (c := c) (K := K) he (sq_nonneg a)).comp (h := fun x : ℝ => x ^ 2) a dsq).div_const 2 using 1
  unfold angularRadialWeight
  ring

theorem integral_angularRadialWeight {c : ℝ} {K e : Fin n → ℝ}
    (he : ∀ j, 0 < e j) (b : ℝ) :
    (∫ a in 0..b, angularRadialWeight c K e a) = angularMass c K e (b ^ 2) / 2 := by
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun a _ => angularRadialMass_hasDerivAt he a)
    ((angularRadialWeight_continuous he).intervalIntegrable 0 b)]
  simp

theorem angular_sqrt_rescale {e a : ℝ} (he : 0 < e) :
    Real.sqrt (1 + a ^ 2 / e) = Real.sqrt (e + a ^ 2) / Real.sqrt e := by
  rw [show 1 + a ^ 2 / e = (e + a ^ 2) / e by field_simp, Real.sqrt_div (by positivity)]

theorem linear_abel_integral {t : ℝ} (ht : 0 < t) :
    IntervalIntegrable (fun a => a * Zeta5.Analysis.abelKernel t a) volume 0 t ∧
      (∫ a in 0..t, a * Zeta5.Analysis.abelKernel t a) = t := by
  have hc : Continuous (fun a : ℝ => -Real.sqrt (t ^ 2 - a ^ 2)) := by fun_prop
  have hd (a : ℝ) (ha : a ∈ Ioo (0 : ℝ) t) :
      HasDerivAt (fun x : ℝ => -Real.sqrt (t ^ 2 - x ^ 2))
        (a * Zeta5.Analysis.abelKernel t a) a := by
    have hr : 0 < t ^ 2 - a ^ 2 := by nlinarith [ha.1, ha.2]
    convert! (((hasDerivAt_const a (t ^ 2)).sub ((hasDerivAt_id a).pow 2)).sqrt hr.ne').neg using 1
    dsimp only [Pi.pow_apply, Pi.sub_apply, id_eq]
    norm_num [Zeta5.Analysis.abelKernel]
    field_simp
  obtain ⟨hi, hv⟩ := Zeta5.Analysis.integral_of_nonnegative_derivative ht.le hc.continuousOn hd
    (fun a ha => mul_nonneg ha.1.le (Zeta5.Analysis.abelKernel_nonneg t a))
  exact ⟨hi, by simpa [Real.sqrt_sq ht.le] using hv⟩

theorem angular_charge_abel_primitive {e t a : ℝ} (he : 0 < e) (ht : 0 < t)
    (ha : a ∈ Ioo (0 : ℝ) t) :
    HasDerivAt (fun x : ℝ =>
      -Real.sqrt e / (e + t ^ 2) * Real.sqrt (t ^ 2 - x ^ 2) / Real.sqrt (e + x ^ 2))
      (a / (e * Real.sqrt (1 + a ^ 2 / e) ^ 3) * Zeta5.Analysis.abelKernel t a) a := by
  have hrad : 0 < t ^ 2 - a ^ 2 := by nlinarith [ha.1, ha.2]
  have harg : 0 < e + a ^ 2 := by positivity
  have hs := Real.sqrt_pos.2 hrad
  have hr := Real.sqrt_pos.2 harg
  have heS := Real.sqrt_pos.2 he
  have htE : 0 < e + t ^ 2 := by positivity
  have dnum := (((hasDerivAt_const a (t ^ 2)).sub ((hasDerivAt_id a).pow 2)).sqrt hrad.ne').const_mul
    (-Real.sqrt e / (e + t ^ 2))
  have dden := (((hasDerivAt_id a).pow 2).const_add e).sqrt harg.ne'
  convert! dnum.div dden hr.ne' using 1
  dsimp only [Pi.pow_apply, Pi.sub_apply, id_eq]
  norm_num only [Nat.reduceSub, pow_one, mul_one, zero_sub, angular_sqrt_rescale he,
    Zeta5.Analysis.abelKernel]
  have hs2 := Real.sq_sqrt hrad.le
  have hr2 := Real.sq_sqrt harg.le
  have he2 := Real.sq_sqrt he.le
  field_simp
  rw [he2, hs2, hr2]
  ring

theorem angular_charge_abel_integral {e t : ℝ} (he : 0 < e) (ht : 0 < t) :
    IntervalIntegrable
      (fun a => a / (e * Real.sqrt (1 + a ^ 2 / e) ^ 3) * Zeta5.Analysis.abelKernel t a)
      volume 0 t ∧
    (∫ a in 0..t, a / (e * Real.sqrt (1 + a ^ 2 / e) ^ 3) * Zeta5.Analysis.abelKernel t a) =
      t / (e + t ^ 2) := by
  have hc : Continuous (fun x : ℝ =>
      -Real.sqrt e / (e + t ^ 2) * Real.sqrt (t ^ 2 - x ^ 2) / Real.sqrt (e + x ^ 2)) := by
    apply Continuous.div
    · fun_prop
    · fun_prop
    · intro x
      positivity
  obtain ⟨hi, hv⟩ := Zeta5.Analysis.integral_of_nonnegative_derivative ht.le hc.continuousOn
    (fun a ha => angular_charge_abel_primitive he ht ha) (fun a ha => by
      apply mul_nonneg
      · apply div_nonneg ha.1.le
        positivity
      · exact Zeta5.Analysis.abelKernel_nonneg t a)
  refine ⟨hi, ?_⟩
  convert! hv using 1
  norm_num only [sub_self, Real.sqrt_zero, mul_zero, zero_div, zero_pow, add_zero,
    sub_zero, Real.sqrt_sq ht.le]
  have hs := Real.sqrt_pos.2 he
  field_simp
  ring

theorem angularRadialWeight_abel_integral {c : ℝ} {K e : Fin n → ℝ}
    (he : ∀ j, 0 < e j) {t : ℝ} (ht : 0 < t) :
    IntervalIntegrable (fun a => angularRadialWeight c K e a * Zeta5.Analysis.abelKernel t a)
      volume 0 t ∧
      (∫ a in 0..t, angularRadialWeight c K e a * Zeta5.Analysis.abelKernel t a) =
        angularEquilibriumSlope c K e t := by
  obtain ⟨h0, h0v⟩ := linear_abel_integral ht
  have hterm (j : Fin n) := angular_charge_abel_integral (he j) ht
  have heq : (fun a => angularRadialWeight c K e a * Zeta5.Analysis.abelKernel t a) =
      (fun a => c / 2 * (a * Zeta5.Analysis.abelKernel t a) +
        ∑ j, K j / 2 * (a / (e j * Real.sqrt (1 + a ^ 2 / e j) ^ 3) *
          Zeta5.Analysis.abelKernel t a)) := by
    funext a
    unfold angularRadialWeight angularMassSlope
    rw [mul_add, add_mul, Finset.mul_sum, Finset.sum_mul]
    congr 1
    · ring
    · apply Finset.sum_congr rfl
      intro j _
      ring
  rw [heq]
  have hsum : IntervalIntegrable (fun a => ∑ j, K j / 2 *
      (a / (e j * Real.sqrt (1 + a ^ 2 / e j) ^ 3) * Zeta5.Analysis.abelKernel t a)) volume 0 t := by
    convert! IntervalIntegrable.sum Finset.univ (fun j _ => (hterm j).1.const_mul (K j / 2)) using 1
    ext a
    simp
  refine ⟨(h0.const_mul (c / 2)).add hsum, ?_⟩
  rw [intervalIntegral.integral_add (h0.const_mul (c / 2)) hsum,
    intervalIntegral.integral_const_mul, h0v,
    intervalIntegral.integral_finset_sum (fun j _ => (hterm j).1.const_mul (K j / 2))]
  simp_rw [intervalIntegral.integral_const_mul, fun j => (hterm j).2]
  unfold angularEquilibriumSlope
  congr 1
  · ring
  · apply Finset.sum_congr rfl
    intro j _
    have hd0 : e j + t ^ 2 ≠ 0 := ne_of_gt (add_pos_of_pos_of_nonneg (he j) (sq_nonneg t))
    field_simp <;> ring

theorem angularField_zero (c : ℝ) (K e : Fin n → ℝ) : angularField c K e 0 = 0 := by
  simp [angularField]

theorem angularField_sq_hasDerivAt {c : ℝ} {K e : Fin n → ℝ}
    (he : ∀ j, 0 < e j) (y : ℝ) :
    HasDerivAt (fun x => angularField c K e (x ^ 2))
      (4 * angularEquilibriumSlope c K e y) y := by
  have dsq : HasDerivAt (fun x : ℝ => x ^ 2) (2 * y) y := by
    convert! ((hasDerivAt_id y).pow 2) using 1 <;> simp
  have dt (j : Fin n) : HasDerivAt (fun x : ℝ => K j * Real.log (1 + x ^ 2 / e j))
      (2 * K j * y / (e j + y ^ 2)) y := by
    have hp : 0 < 1 + y ^ 2 / e j := by
      have h := div_nonneg (sq_nonneg y) (he j).le
      linarith
    convert! (((dsq.div_const (e j)).const_add 1).log hp.ne').const_mul (K j) using 1
    have he0 := (he j).ne'
    have hd0 : e j + y ^ 2 ≠ 0 := ne_of_gt (add_pos_of_pos_of_nonneg (he j) (sq_nonneg y))
    field_simp <;> ring
  have h := (dsq.const_mul c).add (HasDerivAt.fun_sum (u := Finset.univ) (fun j _ => dt j))
  convert! h using 1
  unfold angularEquilibriumSlope
  rw [mul_add, Finset.mul_sum]
  congr 1
  · ring
  · apply Finset.sum_congr rfl
    intro j _
    have he0 := (he j).ne'
    have hd0 : e j + y ^ 2 ≠ 0 := ne_of_gt (add_pos_of_pos_of_nonneg (he j) (sq_nonneg y))
    field_simp
    ring

theorem angularEquilibriumSlope_continuous {c : ℝ} {K e : Fin n → ℝ}
    (he : ∀ j, 0 < e j) : Continuous (angularEquilibriumSlope c K e) := by
  unfold angularEquilibriumSlope
  apply Continuous.add (by fun_prop)
  apply continuous_finsetSum
  intro j _
  apply Continuous.div (by fun_prop) (by fun_prop)
  intro x
  have h := he j
  positivity

theorem integral_angularEquilibriumSlope {c : ℝ} {K e : Fin n → ℝ}
    (he : ∀ j, 0 < e j) (y : ℝ) :
    (∫ t in 0..y, angularEquilibriumSlope c K e t) = angularField c K e (y ^ 2) / 4 := by
  have hd (t : ℝ) : HasDerivAt (fun x => angularField c K e (x ^ 2) / 4)
      (angularEquilibriumSlope c K e t) t := by
    convert! (angularField_sq_hasDerivAt he t).div_const 4 using 1
    ring
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ => hd t)
    ((angularEquilibriumSlope_continuous he).intervalIntegrable 0 y)]
  simp [angularField_zero]

end Zeta3.Analysis

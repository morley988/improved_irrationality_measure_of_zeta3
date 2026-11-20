import Zeta5.Analysis.PhysicalMeasureCauchyFourthIntegrals

/-!
# Exact second Cauchy integrals

Explicit antiderivatives, verified by field normalization, supply all three
rational integrals needed for the cubic Stieltjes transform. The coincident
parameter case is included separately. No differentiation under an improper
integral or external symbolic answer is assumed.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace Zeta3.Analysis
open MeasureTheory Filter Set Real Zeta5.Analysis
open scoped Topology

def secondCauchyKernel (b x : ℝ) : ℝ :=
  2 * (3 * b ^ 2 - x ^ 2) / (x ^ 2 + b ^ 2) ^ 3

theorem secondCauchyKernel_abs_bound {b : ℝ} (hb : 0 < b) (x : ℝ) :
    |secondCauchyKernel b x| ≤ 6 / (x ^ 2 + b ^ 2) ^ 2 := by
  have hd := cauchy_den_pos hb x
  have hp : |3 * b ^ 2 - x ^ 2| ≤ 3 * (x ^ 2 + b ^ 2) := by
    apply abs_le.mpr
    constructor <;> nlinarith [sq_nonneg x, sq_nonneg b]
  unfold secondCauchyKernel
  rw [abs_div, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2), abs_of_pos (pow_pos hd 3)]
  calc
    _ ≤ 2 * (3 * (x ^ 2 + b ^ 2)) / (x ^ 2 + b ^ 2) ^ 3 := by gcongr
    _ = _ := by field_simp; ring

theorem secondCauchyKernel_continuous {b : ℝ} (hb : 0 < b) :
    Continuous (secondCauchyKernel b) := by
  unfold secondCauchyKernel
  fun_prop (disch := exact fun x => pow_ne_zero 3 (ne_of_gt (cauchy_den_pos hb x)))

theorem secondCauchyKernel_integrableOn {b : ℝ} (hb : 0 < b) :
    IntegrableOn (secondCauchyKernel b) (Ioi 0) := by
  apply ((cauchy_inverse_integrableOn hb).const_mul (6 / b ^ 2)).mono'
    (secondCauchyKernel_continuous hb).aestronglyMeasurable
  filter_upwards with x
  rw [Real.norm_eq_abs]
  refine (secondCauchyKernel_abs_bound hb x).trans ?_
  have hd := cauchy_den_pos hb x
  calc
    6 / (x ^ 2 + b ^ 2) ^ 2 = (6 / (x ^ 2 + b ^ 2)) * (1 / (x ^ 2 + b ^ 2)) := by field_simp
    _ ≤ (6 / b ^ 2) * (1 / (x ^ 2 + b ^ 2)) := by
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      exact div_le_div_of_nonneg_left (by norm_num) (by positivity)
        (le_add_of_nonneg_left (sq_nonneg x))

theorem linear_secondCauchyKernel_integrableOn {b : ℝ} (hb : 0 < b) :
    IntegrableOn (fun x : ℝ => x * secondCauchyKernel b x) (Ioi 0) := by
  apply ((cauchy_linear_square_integrableOn hb).const_mul 6).mono'
    (continuous_id.mul (secondCauchyKernel_continuous hb)).aestronglyMeasurable
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
  change ‖x * secondCauchyKernel b x‖ ≤ _
  rw [Real.norm_eq_abs, abs_mul, abs_of_pos hx]
  calc
    _ ≤ x * (6 / (x ^ 2 + b ^ 2) ^ 2) :=
      mul_le_mul_of_nonneg_left (secondCauchyKernel_abs_bound hb x) hx.le
    _ = _ := by ring

theorem product_secondCauchyKernel_integrableOn {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    IntegrableOn (fun x : ℝ => x ^ 2 / (x ^ 2 + a ^ 2) * secondCauchyKernel b x) (Ioi 0) := by
  have hc : Continuous (fun x : ℝ => x ^ 2 / (x ^ 2 + a ^ 2) * secondCauchyKernel b x) := by
    apply Continuous.mul _ (secondCauchyKernel_continuous hb)
    exact (continuous_id.pow 2).div ((continuous_id.pow 2).add continuous_const)
      (fun x => ne_of_gt (cauchy_den_pos ha x))
  apply (secondCauchyKernel_integrableOn hb).norm.mono' hc.aestronglyMeasurable
  filter_upwards with x
  rw [norm_mul, Real.norm_eq_abs (x ^ 2 / (x ^ 2 + a ^ 2)), abs_of_nonneg (by positivity)]
  exact mul_le_of_le_one_left (norm_nonneg _) ((div_le_one (cauchy_den_pos ha x)).mpr
    (le_add_of_nonneg_right (sq_nonneg a)))

theorem square_secondCauchyKernel_integrableOn {b : ℝ} (hb : 0 < b) :
    IntegrableOn (fun x : ℝ => x ^ 2 * secondCauchyKernel b x) (Ioi 0) := by
  apply ((cauchy_inverse_integrableOn hb).const_mul 6).mono'
    ((continuous_id.pow 2).mul (secondCauchyKernel_continuous hb)).aestronglyMeasurable
  filter_upwards with x
  change ‖x ^ 2 * secondCauchyKernel b x‖ ≤ _
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (sq_nonneg x)]
  have hd := cauchy_den_pos hb x
  calc
    _ ≤ x ^ 2 * (6 / (x ^ 2 + b ^ 2) ^ 2) :=
      mul_le_mul_of_nonneg_left (secondCauchyKernel_abs_bound hb x) (sq_nonneg x)
    _ ≤ (x ^ 2 + b ^ 2) * (6 / (x ^ 2 + b ^ 2) ^ 2) := by
      apply mul_le_mul_of_nonneg_right (le_add_of_nonneg_right (sq_nonneg b))
      positivity
    _ = _ := by field_simp

def secondCauchyPrimitive (b x : ℝ) : ℝ :=
  (2 / b ^ 3) * arctan (x / b) + (2 / b ^ 2) * cauchyAtom b 1 x + 2 * cauchyAtom b 2 x

theorem hasDerivAt_secondCauchyPrimitive {b : ℝ} (hb : 0 < b) (x : ℝ) :
    HasDerivAt (secondCauchyPrimitive b) (secondCauchyKernel b x) x := by
  unfold secondCauchyPrimitive
  have h := (((hasDerivAt_arctan_div hb x).const_mul (2 / b ^ 3)).add
    ((hasDerivAt_cauchyAtom hb 1 x).const_mul (2 / b ^ 2))).add
    ((hasDerivAt_cauchyAtom hb 2 x).const_mul 2)
  apply h.congr_deriv
  unfold secondCauchyKernel
  norm_num
  field_simp [hb.ne', ne_of_gt (cauchy_den_pos hb x)]
  ring

theorem tendsto_secondCauchyPrimitive {b : ℝ} (hb : 0 < b) :
    Tendsto (secondCauchyPrimitive b) atTop (𝓝 (π / b ^ 3)) := by
  unfold secondCauchyPrimitive
  have h := (((tendsto_arctan_div hb).const_mul (2 / b ^ 3)).add
    ((tendsto_cauchyAtom hb 0).const_mul (2 / b ^ 2))).add
    ((tendsto_cauchyAtom hb 1).const_mul 2)
  simp only [mul_zero, add_zero] at h
  convert! h using 1 <;> ring

theorem secondCauchyKernel_integral {b : ℝ} (hb : 0 < b) :
    ∫ x : ℝ in Ioi 0, secondCauchyKernel b x = π / b ^ 3 := by
  have h := integral_Ioi_of_hasDerivAt_of_tendsto' (a := 0)
    (fun x _ => hasDerivAt_secondCauchyPrimitive hb x)
    (secondCauchyKernel_integrableOn hb) (tendsto_secondCauchyPrimitive hb)
  simpa [secondCauchyPrimitive, cauchyAtom] using h

def linearSecondCauchyPrimitive (b x : ℝ) : ℝ :=
  cauchyInvAtom b 1 x - (2 * b ^ 2) * cauchyInvAtom b 2 x

theorem hasDerivAt_linearSecondCauchyPrimitive {b : ℝ} (hb : 0 < b) (x : ℝ) :
    HasDerivAt (linearSecondCauchyPrimitive b) (x * secondCauchyKernel b x) x := by
  unfold linearSecondCauchyPrimitive
  have h := (hasDerivAt_cauchyInvAtom hb 1 x).sub
    ((hasDerivAt_cauchyInvAtom hb 2 x).const_mul (2 * b ^ 2))
  apply h.congr_deriv
  unfold secondCauchyKernel
  norm_num
  field_simp [ne_of_gt (cauchy_den_pos hb x)]
  ring

theorem tendsto_linearSecondCauchyPrimitive {b : ℝ} :
    Tendsto (linearSecondCauchyPrimitive b) atTop (𝓝 0) := by
  unfold linearSecondCauchyPrimitive
  have h := (tendsto_cauchyInvAtom b (by decide : 1 ≠ 0)).sub
    ((tendsto_cauchyInvAtom b (by decide : 2 ≠ 0)).const_mul (2 * b ^ 2))
  simpa using h

theorem linear_secondCauchyKernel_integral {b : ℝ} (hb : 0 < b) :
    ∫ x : ℝ in Ioi 0, x * secondCauchyKernel b x = 1 / b ^ 2 := by
  have h := integral_Ioi_of_hasDerivAt_of_tendsto' (a := 0)
    (fun x _ => hasDerivAt_linearSecondCauchyPrimitive hb x)
    (linear_secondCauchyKernel_integrableOn hb) tendsto_linearSecondCauchyPrimitive
  rw [h]
  unfold linearSecondCauchyPrimitive cauchyInvAtom
  norm_num
  field_simp [hb.ne']
  ring

def repeatedSecondCauchyPrimitive (b x : ℝ) : ℝ :=
  (1 / (4 * b ^ 3)) * arctan (x / b) + (1 / (4 * b ^ 2)) * cauchyAtom b 1 x +
    (5 / 6) * cauchyAtom b 2 x - (4 * b ^ 2 / 3) * cauchyAtom b 3 x

theorem hasDerivAt_repeatedSecondCauchyPrimitive {b : ℝ} (hb : 0 < b) (x : ℝ) :
    HasDerivAt (repeatedSecondCauchyPrimitive b)
      (x ^ 2 / (x ^ 2 + b ^ 2) * secondCauchyKernel b x) x := by
  unfold repeatedSecondCauchyPrimitive
  have h := ((((hasDerivAt_arctan_div hb x).const_mul (1 / (4 * b ^ 3))).add
    ((hasDerivAt_cauchyAtom hb 1 x).const_mul (1 / (4 * b ^ 2)))).add
    ((hasDerivAt_cauchyAtom hb 2 x).const_mul (5 / 6))).sub
    ((hasDerivAt_cauchyAtom hb 3 x).const_mul (4 * b ^ 2 / 3))
  apply h.congr_deriv
  unfold secondCauchyKernel
  norm_num
  field_simp [hb.ne', ne_of_gt (cauchy_den_pos hb x)]
  ring

theorem tendsto_repeatedSecondCauchyPrimitive {b : ℝ} (hb : 0 < b) :
    Tendsto (repeatedSecondCauchyPrimitive b) atTop (𝓝 (π / (b + b) ^ 3)) := by
  unfold repeatedSecondCauchyPrimitive
  have h := ((((tendsto_arctan_div hb).const_mul (1 / (4 * b ^ 3))).add
    ((tendsto_cauchyAtom hb 0).const_mul (1 / (4 * b ^ 2)))).add
    ((tendsto_cauchyAtom hb 1).const_mul (5 / 6))).sub
    ((tendsto_cauchyAtom hb 2).const_mul (4 * b ^ 2 / 3))
  simp only [mul_zero, add_zero, sub_zero] at h
  convert! h using 1 <;> ring

theorem repeated_secondCauchyKernel_integral {b : ℝ} (hb : 0 < b) :
    ∫ x : ℝ in Ioi 0, x ^ 2 / (x ^ 2 + b ^ 2) * secondCauchyKernel b x =
      π / (b + b) ^ 3 := by
  have h := integral_Ioi_of_hasDerivAt_of_tendsto' (a := 0)
    (fun x _ => hasDerivAt_repeatedSecondCauchyPrimitive hb x)
    (product_secondCauchyKernel_integrableOn hb hb) (tendsto_repeatedSecondCauchyPrimitive hb)
  simpa [repeatedSecondCauchyPrimitive, cauchyAtom] using h

def distinctSecondCauchyPrimitive (a b x : ℝ) : ℝ :=
  (2 * a * (a ^ 2 + 3 * b ^ 2) / (a ^ 2 - b ^ 2) ^ 3) * arctan (x / a) +
    (-2 * b * (3 * a ^ 2 + b ^ 2) / (a ^ 2 - b ^ 2) ^ 3) * arctan (x / b) +
    (2 * (a ^ 2 + b ^ 2) / (a ^ 2 - b ^ 2) ^ 2) * cauchyAtom b 1 x +
    (-2 * b ^ 2 / (a ^ 2 - b ^ 2)) * cauchyAtom b 2 x

theorem hasDerivAt_distinctSecondCauchyPrimitive {a b : ℝ}
    (ha : 0 < a) (hb : 0 < b) (hab : a ≠ b) (x : ℝ) :
    HasDerivAt (distinctSecondCauchyPrimitive a b)
      (x ^ 2 / (x ^ 2 + a ^ 2) * secondCauchyKernel b x) x := by
  unfold distinctSecondCauchyPrimitive
  have h := ((((hasDerivAt_arctan_div ha x).const_mul
    (2 * a * (a ^ 2 + 3 * b ^ 2) / (a ^ 2 - b ^ 2) ^ 3)).add
    ((hasDerivAt_arctan_div hb x).const_mul
      (-2 * b * (3 * a ^ 2 + b ^ 2) / (a ^ 2 - b ^ 2) ^ 3))).add
    ((hasDerivAt_cauchyAtom hb 1 x).const_mul
      (2 * (a ^ 2 + b ^ 2) / (a ^ 2 - b ^ 2) ^ 2))).add
    ((hasDerivAt_cauchyAtom hb 2 x).const_mul (-2 * b ^ 2 / (a ^ 2 - b ^ 2)))
  apply h.congr_deriv
  unfold secondCauchyKernel
  norm_num
  field_simp [ne_of_gt (cauchy_den_pos ha x), ne_of_gt (cauchy_den_pos hb x),
    cauchy_square_sub_ne_zero hb ha hab.symm]
  ring

theorem tendsto_distinctSecondCauchyPrimitive {a b : ℝ}
    (ha : 0 < a) (hb : 0 < b) (hab : a ≠ b) :
    Tendsto (distinctSecondCauchyPrimitive a b) atTop (𝓝 (π / (a + b) ^ 3)) := by
  unfold distinctSecondCauchyPrimitive
  have h := ((((tendsto_arctan_div ha).const_mul
    (2 * a * (a ^ 2 + 3 * b ^ 2) / (a ^ 2 - b ^ 2) ^ 3)).add
    ((tendsto_arctan_div hb).const_mul
      (-2 * b * (3 * a ^ 2 + b ^ 2) / (a ^ 2 - b ^ 2) ^ 3))).add
    ((tendsto_cauchyAtom hb 0).const_mul
      (2 * (a ^ 2 + b ^ 2) / (a ^ 2 - b ^ 2) ^ 2))).add
    ((tendsto_cauchyAtom hb 1).const_mul (-2 * b ^ 2 / (a ^ 2 - b ^ 2)))
  simp only [mul_zero, add_zero] at h
  have he : (2 * a * (a ^ 2 + 3 * b ^ 2) / (a ^ 2 - b ^ 2) ^ 3) * (π / 2) +
      (-2 * b * (3 * a ^ 2 + b ^ 2) / (a ^ 2 - b ^ 2) ^ 3) * (π / 2) =
      π / (a + b) ^ 3 := by
    field_simp [ne_of_gt (add_pos ha hb), cauchy_square_sub_ne_zero hb ha hab.symm]
    ring
  rwa [he] at h

theorem product_secondCauchyKernel_integral {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    ∫ x : ℝ in Ioi 0, x ^ 2 / (x ^ 2 + a ^ 2) * secondCauchyKernel b x =
      π / (a + b) ^ 3 := by
  by_cases hab : a = b
  · subst b
    exact repeated_secondCauchyKernel_integral ha
  · have h := integral_Ioi_of_hasDerivAt_of_tendsto' (a := 0)
      (fun x _ => hasDerivAt_distinctSecondCauchyPrimitive ha hb hab x)
      (product_secondCauchyKernel_integrableOn ha hb) (tendsto_distinctSecondCauchyPrimitive ha hb hab)
    simpa [distinctSecondCauchyPrimitive, cauchyAtom] using h

end Zeta3.Analysis

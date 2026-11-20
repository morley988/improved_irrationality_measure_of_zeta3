import Zeta3.Arithmetic.SmallPrimeSum
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-! The complete small-prime contribution vanishes at the physical
quadratic scale (50n)². All estimates here are internal real analysis. -/
noncomputable section
namespace Zeta3.Arithmetic
open Filter
open scoped Topology

def arithmeticScale (n : ℕ) : ℝ := (50 * (n : ℝ)) ^ 2

lemma smallPrimeCutoff_le_real_sqrt {n : ℕ} (hn : 0 < n) :
    (Zeta3.Arithmetic.smallPrimeCutoff n : ℝ) ≤ 200*Real.sqrt (n : ℝ) := by
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hs1 : 1 ≤ Real.sqrt (n : ℝ) := Real.one_le_sqrt.mpr hn1
  have hsq : (Nat.sqrt n : ℝ)^2 ≤ (n : ℝ) := by exact_mod_cast Nat.sqrt_le' n
  have hroot := Real.sq_sqrt (Nat.cast_nonneg n : (0 : ℝ) ≤ n)
  have hsn := Real.sqrt_nonneg (n : ℝ)
  have hkn : (0 : ℝ) ≤ Nat.sqrt n := Nat.cast_nonneg _
  unfold Zeta3.Arithmetic.smallPrimeCutoff
  push_cast
  nlinarith

lemma tendsto_log_nat_div_sqrt :
    Tendsto (fun n : ℕ => Real.log (n : ℝ)/Real.sqrt (n : ℝ)) atTop (𝓝 0) := by
  have h := (isLittleO_log_rpow_atTop (by norm_num : (0 : ℝ) < 1/2)).tendsto_div_nhds_zero
  have hcast : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
  convert! h.comp hcast using 1
  ext n
  simp only [Function.comp_apply, Real.sqrt_eq_rpow]

lemma tendsto_inv_sqrt_nat :
    Tendsto (fun n : ℕ => (Real.sqrt (n : ℝ))⁻¹) atTop (𝓝 0) :=
  tendsto_inv_atTop_zero.comp (Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop)

lemma smallPrimeError_nonneg (n : ℕ) : 0 ≤ Zeta3.Arithmetic.smallPrimeError n := by
  unfold Zeta3.Arithmetic.smallPrimeError
  apply mul_nonneg (by positivity)
  apply add_nonneg
  · exact mul_nonneg (by norm_num) (Real.log_nonneg
      (by nlinarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]))
  · exact Real.log_nonneg (by norm_num)

lemma smallPrimeError_over_scale_le {n : ℕ} (hn : 0 < n) :
    Zeta3.Arithmetic.smallPrimeError n/arithmeticScale n ≤
      (102/25 : ℝ)*(9*(Real.log 272+Real.log (n : ℝ))+Real.log 96)/Real.sqrt (n : ℝ) := by
  have hnpos : 0 < (n : ℝ) := by exact_mod_cast hn
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hspos : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.mpr hnpos
  have hlog : Real.log (268*(n : ℝ)+4) ≤ Real.log 272+Real.log (n : ℝ) := by
    have h := Real.log_le_log (by positivity : 0 < 268*(n : ℝ)+4)
      (show 268*(n : ℝ)+4 ≤ 272*(n : ℝ) by linarith)
    rwa [Real.log_mul (by norm_num : (272 : ℝ) ≠ 0) hnpos.ne'] at h
  have hB : 0 ≤ 9*Real.log (268*(n : ℝ)+4)+Real.log 96 := by
    exact add_nonneg (mul_nonneg (by norm_num) (Real.log_nonneg (by linarith)))
      (Real.log_nonneg (by norm_num))
  have hB' : 0 ≤ 9*(Real.log 272+Real.log (n : ℝ))+Real.log 96 := by
    linarith
  have h := mul_le_mul
    (mul_le_mul_of_nonneg_left (smallPrimeCutoff_le_real_sqrt hn)
      (show 0 ≤ 51*(n : ℝ) by positivity))
    (show 9*Real.log (268*(n : ℝ)+4)+Real.log 96 ≤
      9*(Real.log 272+Real.log (n : ℝ))+Real.log 96 by linarith) hB (by positivity)
  have hd := div_le_div_of_nonneg_right h (sq_nonneg (50*(n : ℝ)))
  change Zeta3.Arithmetic.smallPrimeError n/arithmeticScale n ≤ _ at hd
  apply hd.trans_eq
  have hs := Real.sq_sqrt hnpos.le
  field_simp
  nlinarith [hs]

theorem smallPrimeError_over_windowScale_limit :
    Tendsto (fun n : ℕ => Zeta3.Arithmetic.smallPrimeError n/arithmeticScale n)
      atTop (𝓝 0) := by
  have hlog := tendsto_log_nat_div_sqrt.const_mul (918/25 : ℝ)
  have hc := tendsto_inv_sqrt_nat.const_mul ((102/25 : ℝ)*(9*Real.log 272+Real.log 96))
  have hupper := hlog.add hc
  simp only [mul_zero, add_zero] at hupper
  have hupper' : Tendsto (fun n : ℕ =>
      (102/25 : ℝ)*(9*(Real.log 272+Real.log (n : ℝ))+Real.log 96)/Real.sqrt (n : ℝ)) atTop (𝓝 0) := by
    convert! hupper using 1
    ext n
    ring
  apply squeeze_zero' _ _ hupper'
  · filter_upwards [] with n
    exact div_nonneg (smallPrimeError_nonneg n) (sq_nonneg _)
  · exact (eventually_gt_atTop (0 : ℕ)).mono (fun _ hn => smallPrimeError_over_scale_le hn)

end Zeta3.Arithmetic

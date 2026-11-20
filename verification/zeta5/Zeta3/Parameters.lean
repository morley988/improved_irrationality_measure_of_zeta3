import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp
import Mathlib.Data.Real.Basic

/-!
# Exact parameters and the final rational comparison

These inequalities are checked by Lean's kernel. The finite Arb certificates
are needed to bound the *actual* analytic and arithmetic quantities by these
rationals. This file does not assert that those bounds hold.

The response slope remains the actual real number `a = g(T)` until the last
monotonicity step. In particular we do not replace the response threshold by
its upper enclosure in the response theorem.
-/

namespace Zeta3.Parameters
noncomputable section

def s₁ : ℝ := 2 / 25
def s₂ : ℝ := 8 / 25
def δ : ℝ := 51 / 50
def degreeRate : ℝ := 17 / 25
def u : ℝ := 1000001 / 1000000
def T : ℝ := 17 / 125
def Tcap : ℝ := 7 / 50

def arithmeticUpper : ℝ := 1926282169226183949 / 500000000000000000
def analyticLower : ℝ := 300854183181 / 62500000000
def responseIntegralUpper : ℝ := 191284115113 / 200000000000
def slopeLower : ℝ := 6545408942519 / 1000000000000
def slopeUpper : ℝ := 6545408942957 / 1000000000000
def savingLower : ℝ := 2341008439316051 / 500000000000000000
def target : ℝ := 2225439040605380000 / 447428816560392051

theorem windows_positive : 0 < s₁ ∧ 0 < s₂ ∧ s₁ < s₂ ∧ s₁ + s₂ < 1 := by
  norm_num [s₁, s₂]

theorem parameters_positive : 0 < degreeRate ∧ 0 < T ∧ T < Tcap ∧ 0 < slopeLower ∧
    slopeLower ≤ slopeUpper ∧ 0 < savingLower := by
  norm_num [degreeRate, T, Tcap, slopeLower, slopeUpper, savingLower]

theorem savingLower_exact :
    analyticLower - arithmeticUpper - responseIntegralUpper = savingLower := by
  norm_num [analyticLower, arithmeticUpper, responseIntegralUpper, savingLower]

theorem target_exact : degreeRate * slopeUpper / (savingLower + T * slopeUpper) = target := by
  norm_num [degreeRate, slopeUpper, savingLower, T, target]

theorem target_lt_4974 : target < (2487 / 500 : ℝ) := by
  norm_num [target]

/-- The ratio increases with its positive slope and decreases with its positive
response saving. This is an ordinary ordered-field proof, not a numerical
assumption. -/
theorem ratio_le_of_enclosures {a S : ℝ} (ha : 0 < a)
    (haU : a ≤ slopeUpper) (hS : savingLower ≤ S) :
    0 < S + T * a ∧ degreeRate * a / (S + T * a) ≤ target := by
  have hdegreeRate : 0 < degreeRate := parameters_positive.1
  have hT : 0 < T := parameters_positive.2.1
  have hs : 0 < savingLower := parameters_positive.2.2.2.2.2
  have hSpos : 0 < S := lt_of_lt_of_le hs hS
  have hd : 0 < S + T * a := add_pos hSpos (mul_pos hT ha)
  have hd' : 0 < savingLower + T * a := add_pos hs (mul_pos hT ha)
  have haUpos : 0 < slopeUpper := lt_of_lt_of_le ha haU
  have hdU : 0 < savingLower + T * slopeUpper := add_pos hs (mul_pos hT haUpos)
  refine ⟨hd, ?_⟩
  rw [← target_exact]
  calc
    degreeRate * a / (S + T * a) ≤ degreeRate * a / (savingLower + T * a) := by
      apply div_le_div_of_nonneg_left (mul_pos hdegreeRate ha).le hd'
      linarith
    _ ≤ degreeRate * slopeUpper / (savingLower + T * slopeUpper) := by
      apply (div_le_div_iff₀ hd' hdU).mpr
      nlinarith [mul_nonneg hdegreeRate.le (mul_nonneg hs.le (sub_nonneg.mpr haU))]

/-- A finite certificate need only enclose the actual three constants and the
actual response slope. The final rational bound then follows in the kernel. -/
theorem ratio_le_from_actual_constants {a C_an C_ar I : ℝ}
    (ha : 0 < a) (haU : a ≤ slopeUpper)
    (hAn : analyticLower ≤ C_an) (hAr : C_ar ≤ arithmeticUpper)
    (hI : I ≤ responseIntegralUpper) :
    0 < C_an - C_ar - I + T * a ∧
      degreeRate * a / (C_an - C_ar - I + T * a) ≤ target := by
  apply ratio_le_of_enclosures ha haU
  have hsave := savingLower_exact
  linarith

end
end Zeta3.Parameters

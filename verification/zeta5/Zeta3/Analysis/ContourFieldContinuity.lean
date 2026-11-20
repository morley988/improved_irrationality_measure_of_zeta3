import Zeta3.Analysis.PhysicalEquilibrium
import Zeta3.Analysis.ContourLocalNorm

/-!
# Actual external-field oscillation for the local norm comparison

The two-window external field is `3π`-Lipschitz on the nonnegative axis.
After the substitution `y = √z`, it is Hölder with exponent `1/2` and the
same constant.  A weighted maximum therefore supplies the actual local
uniform polynomial bound required by `ContourLocalNorm`.
-/

noncomputable section
open Set Polynomial

namespace Zeta3.Analysis

private def smoothExternalField (s y : ℝ) : ℝ :=
  2*Real.pi*y + Zeta5.Analysis.externalIntegralFormula 1 y -
    2*Zeta5.Analysis.externalIntegralFormula s y

private theorem smoothExternalField_eq (s y : ℝ) (hs : 0 < s) (hy : 0 ≤ y) :
    smoothExternalField s y = Zeta5.Analysis.externalField s y := by
  simp only [smoothExternalField, Zeta5.Analysis.externalField,
    Zeta5.Analysis.externalIntegral_formula (by norm_num : (0:ℝ)<1) hy,
    Zeta5.Analysis.externalIntegral_formula hs hy]

private theorem smoothExternalField_hasDerivAt (s y : ℝ) (hs : 0 < s) :
    HasDerivAt (smoothExternalField s) (4*Zeta5.Analysis.equilibriumSlope s y) y := by
  have h := (((hasDerivAt_id y).const_mul (2*Real.pi)).add
    (Zeta5.Analysis.externalIntegralFormula_hasDerivAt (by norm_num : (0:ℝ)<1) y)).sub
      ((Zeta5.Analysis.externalIntegralFormula_hasDerivAt hs y).const_mul 2)
  convert! h using 1
  dsimp [Zeta5.Analysis.equilibriumSlope]
  rw [div_one]
  ring

private theorem equilibriumSlope_nonneg (s y : ℝ) (hs : 0 < s) (hy : 0 ≤ y) :
    0 ≤ Zeta5.Analysis.equilibriumSlope s y := by
  have h1 := Real.arctan_lt_pi_div_two y
  have h2 := Real.arctan_nonneg.mpr (div_nonneg hy hs.le)
  dsimp [Zeta5.Analysis.equilibriumSlope]
  linarith

theorem externalField_lipschitz_nonneg (s x y : ℝ) (hs : 0 < s)
    (hx : 0 ≤ x) (hy : 0 ≤ y) :
    |Zeta5.Analysis.externalField s y-Zeta5.Analysis.externalField s x| ≤
      3*Real.pi* |y-x| := by
  have h := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
    (f := smoothExternalField s) (f' := fun t => 4*Zeta5.Analysis.equilibriumSlope s t)
    (fun t _ => (smoothExternalField_hasDerivAt s t hs).hasDerivWithinAt)
    (C := 3*Real.pi)
    (fun t (ht : t ∈ Ici (0:ℝ)) => by
      rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (by norm_num)
        (equilibriumSlope_nonneg s t hs ht))]
      have h := Zeta5.Analysis.equilibriumSlope_le (s := s) ht
      linarith)
    (convex_Ici (0:ℝ)) hx hy
  rw [smoothExternalField_eq s y hs hy, smoothExternalField_eq s x hs hx,
    Real.norm_eq_abs, Real.norm_eq_abs] at h
  exact h

theorem physicalField_lipschitz_nonneg (s₁ s₂ x y : ℝ) (h₁ : 0 < s₁) (h₂ : 0 < s₂)
    (hx : 0 ≤ x) (hy : 0 ≤ y) :
    |physicalField s₁ s₂ y-physicalField s₁ s₂ x| ≤ 3*Real.pi* |y-x| := by
  have h1 := externalField_lipschitz_nonneg s₁ x y h₁ hx hy
  have h2 := externalField_lipschitz_nonneg s₂ x y h₂ hx hy
  rw [physicalField_eq_average, physicalField_eq_average]
  have heq : (Zeta5.Analysis.externalField s₁ y+Zeta5.Analysis.externalField s₂ y)/2 -
      (Zeta5.Analysis.externalField s₁ x+Zeta5.Analysis.externalField s₂ x)/2 =
      ((Zeta5.Analysis.externalField s₁ y-Zeta5.Analysis.externalField s₁ x)+
        (Zeta5.Analysis.externalField s₂ y-Zeta5.Analysis.externalField s₂ x))/2 := by ring
  rw [heq, abs_div, abs_of_pos (by norm_num : (0:ℝ)<2)]
  have ht := abs_add_le (Zeta5.Analysis.externalField s₁ y-Zeta5.Analysis.externalField s₁ x)
    (Zeta5.Analysis.externalField s₂ y-Zeta5.Analysis.externalField s₂ x)
  linarith

/-- The elementary square-root Hölder inequality on the nonnegative axis. -/
theorem sqrt_abs_sub_le (x y : ℝ) (hx : 0 ≤ x) (hy : 0 ≤ y) :
    |Real.sqrt y-Real.sqrt x| ≤ Real.sqrt |y-x| := by
  have hxs := Real.sq_sqrt hx
  have hys := Real.sq_sqrt hy
  have hrs := Real.sq_sqrt (abs_nonneg (y-x))
  apply (sq_le_sq₀ (abs_nonneg _) (Real.sqrt_nonneg _)).mp
  rw [sq_abs, hrs]
  rcases le_total x y with hxy | hyx
  · rw [abs_of_nonneg (sub_nonneg.mpr hxy)]
    have hs := Real.sqrt_le_sqrt hxy
    nlinarith [mul_nonneg (sub_nonneg.mpr hs) (Real.sqrt_nonneg x)]
  · rw [abs_of_nonpos (sub_nonpos.mpr hyx)]
    have hs := Real.sqrt_le_sqrt hyx
    nlinarith [mul_nonneg (sub_nonneg.mpr hs) (Real.sqrt_nonneg y)]

theorem physicalField_sqrt_holder (s₁ s₂ x y : ℝ) (h₁ : 0 < s₁) (h₂ : 0 < s₂)
    (hx : 0 ≤ x) (hy : 0 ≤ y) :
    |physicalField s₁ s₂ (Real.sqrt y)-physicalField s₁ s₂ (Real.sqrt x)| ≤
      3*Real.pi*Real.sqrt |y-x| := by
  exact (physicalField_lipschitz_nonneg s₁ s₂ _ _ h₁ h₂
    (Real.sqrt_nonneg x) (Real.sqrt_nonneg y)).trans
      (mul_le_mul_of_nonneg_left (sqrt_abs_sub_le x y hx hy) (by positivity))

theorem physicalField_sqrt_oscillation (s₁ s₂ x y L : ℝ) (h₁ : 0 < s₁) (h₂ : 0 < s₂)
    (hx : 0 ≤ x) (hy : 0 ≤ y) (hclose : |y-x| ≤ L) :
    |physicalField s₁ s₂ (Real.sqrt y)-physicalField s₁ s₂ (Real.sqrt x)| ≤
      3*Real.pi*Real.sqrt L :=
  (physicalField_sqrt_holder s₁ s₂ x y h₁ h₂ hx hy).trans
    (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hclose) (by positivity))

/-- The elementary conversion of a weighted-value comparison into an
unweighted one, retaining the exact oscillation loss. -/
theorem polynomial_bound_of_weighted_comparison (p : ℝ[X]) (V : ℝ → ℝ)
    (N x y ω : ℝ) (hN : 0 ≤ N)
    (hmax : |p.eval y| * Real.exp (-N*V y/2) ≤ |p.eval x| * Real.exp (-N*V x/2))
    (hV : V y-V x ≤ ω) :
    |p.eval y| ≤ |p.eval x| * Real.exp (N*ω/2) := by
  calc
    |p.eval y| = (|p.eval y| * Real.exp (-N*V y/2))*Real.exp (N*V y/2) := by
      rw [mul_assoc, ← Real.exp_add]
      rw [show -N*V y/2+N*V y/2=0 by ring, Real.exp_zero, mul_one]
    _ ≤ (|p.eval x| * Real.exp (-N*V x/2))*Real.exp (N*V y/2) :=
      mul_le_mul_of_nonneg_right hmax (Real.exp_pos _).le
    _ = |p.eval x| * Real.exp (N*(V y-V x)/2) := by
      rw [mul_assoc, ← Real.exp_add]
      congr 2
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr
      (by nlinarith [mul_le_mul_of_nonneg_left hV hN])) (abs_nonneg _)

/-- A weighted maximum for the actual field gives the local uniform bound
with the explicit factor `exp(3π N √L / 2)`. -/
theorem polynomial_bound_near_physical_weighted_max (p : ℝ[X])
    (s₁ s₂ N x y L : ℝ) (h₁ : 0 < s₁) (h₂ : 0 < s₂) (hN : 0 ≤ N)
    (hx : 0 ≤ x) (hy : 0 ≤ y) (hclose : |y-x| ≤ L)
    (hmax : |p.eval y| * Real.exp (-N*physicalField s₁ s₂ (Real.sqrt y)/2) ≤
      |p.eval x| * Real.exp (-N*physicalField s₁ s₂ (Real.sqrt x)/2)) :
    |p.eval y| ≤ |p.eval x| * Real.exp (N*(3*Real.pi*Real.sqrt L)/2) := by
  apply polynomial_bound_of_weighted_comparison p (fun z => physicalField s₁ s₂ (Real.sqrt z))
    N x y (3*Real.pi*Real.sqrt L) hN hmax
  exact (le_abs_self _).trans (physicalField_sqrt_oscillation s₁ s₂ x y L h₁ h₂ hx hy hclose)

end Zeta3.Analysis

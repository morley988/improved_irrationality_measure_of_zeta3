import Zeta3.Analysis.ContourFieldContinuity

/-!
# Uniform finite weighted L² comparison for the actual physical field

The radius in this file depends on the interval, degree, and external field,
and is independent of the polynomial.  The resulting comparison gives the
explicit finite estimate whose logarithmic loss is sublinear when the local
interval shrinks sufficiently slowly.  Integrability and a genuine density
lower bound are mathematical hypotheses, not numerical certificate premises.
-/

noncomputable section
open Set Polynomial MeasureTheory

namespace Zeta3.Analysis

def physicalFieldOscillation (a b : ℝ) : ℝ := 3*Real.pi*Real.sqrt (b-a)

def physicalLocalGrowth (N a b : ℝ) : ℝ :=
  Real.exp (N*physicalFieldOscillation a b/2)

def physicalPersistenceRadius (n : ℕ) (N a b : ℝ) : ℝ :=
  (b-a)/(8*((n:ℝ)+1)^2*physicalLocalGrowth N a b)

theorem physicalLocalGrowth_pos (N a b : ℝ) : 0 < physicalLocalGrowth N a b :=
  Real.exp_pos _

theorem one_le_physicalLocalGrowth (N a b : ℝ) (hN : 0 ≤ N) :
    1 ≤ physicalLocalGrowth N a b := by
  apply Real.one_le_exp_iff.mpr
  unfold physicalFieldOscillation
  positivity

theorem physicalPersistenceRadius_pos (n : ℕ) (N a b : ℝ) (hab : a < b) :
    0 < physicalPersistenceRadius n N a b := by
  unfold physicalPersistenceRadius
  have hE := physicalLocalGrowth_pos N a b
  positivity

theorem physicalPersistenceRadius_eq (n : ℕ) (N a b Q : ℝ) (hQ : Q ≠ 0) :
    physicalPersistenceRadius n N a b =
      polynomialPersistenceRadius n (Q*physicalLocalGrowth N a b) a b Q := by
  unfold physicalPersistenceRadius polynomialPersistenceRadius
  field_simp
  <;> ring

theorem physicalPersistenceRadius_length (n : ℕ) (N a b : ℝ)
    (hN : 0 ≤ N) (hab : a < b) :
    2*physicalPersistenceRadius n N a b ≤ b-a := by
  rw [physicalPersistenceRadius_eq n N a b 1 (by norm_num), one_mul]
  exact polynomialPersistenceRadius_length n _ a b 1
    (physicalLocalGrowth_pos N a b) hab (one_le_physicalLocalGrowth N a b hN)

/-- The actual finite comparison for any weight above a fixed-power physical
density.  The constant on the right does not depend on `p`. -/
theorem physical_weighted_value_sq_le_integral
    (p : ℝ[X]) (n m : ℕ) (s₁ s₂ N a b x κ : ℝ) (w : ℝ → ℝ)
    (hd : p.natDegree ≤ n) (h₁ : 0 < s₁) (h₂ : 0 < s₂)
    (hN : 0 ≤ N) (ha : 0 ≤ a) (hab : a < b) (hx : x ∈ Icc a b)
    (hκ : 0 < κ) (hQ : 0 < |p.eval x|)
    (hmax : ∀ y ∈ Icc a b,
      |p.eval y| * Real.exp (-N*physicalField s₁ s₂ (Real.sqrt y)/2) ≤
        |p.eval x| * Real.exp (-N*physicalField s₁ s₂ (Real.sqrt x)/2))
    (hw : ∀ y ∈ Icc a b, 0 ≤ w y)
    (hwlower : ∀ y ∈ Icc a b,
      κ*y^m*Real.exp (-N*physicalField s₁ s₂ (Real.sqrt y)) ≤ w y)
    (hfi : IntervalIntegrable (fun y => w y*(p.eval y)^2) volume a b) :
    (p.eval x)^2*Real.exp (-N*physicalField s₁ s₂ (Real.sqrt x)) ≤
      (8/(physicalPersistenceRadius n N a b*κ*(physicalPersistenceRadius n N a b/2)^m))*
        Real.exp (N*physicalFieldOscillation a b)*
          (∫ y in a..b, w y*(p.eval y)^2) := by
  let Q := |p.eval x|
  let E := physicalLocalGrowth N a b
  let ρ := physicalPersistenceRadius n N a b
  let V := fun y => physicalField s₁ s₂ (Real.sqrt y)
  let ω := physicalFieldOscillation a b
  have hQ' : 0 < Q := hQ
  have hE : 0 < E := physicalLocalGrowth_pos N a b
  have hρ : 0 < ρ := physicalPersistenceRadius_pos n N a b hab
  have hM : 0 < Q*E := mul_pos hQ' hE
  have hclose (y : ℝ) (hy : y ∈ Icc a b) : |y-x| ≤ b-a :=
    abs_le.mpr ⟨by linarith [hy.1,hx.2], by linarith [hy.2,hx.1]⟩
  have hb (y : ℝ) (hy : y ∈ Icc a b) : |p.eval y| ≤ Q*E := by
    exact polynomial_bound_near_physical_weighted_max p s₁ s₂ N x y (b-a) h₁ h₂ hN
      (ha.trans hx.1) (ha.trans hy.1) (hclose y hy) (hmax y hy)
  have hlen : 2*ρ ≤ b-a := physicalPersistenceRadius_length n N a b hN hab
  have hscale : (4*(n:ℝ)^2*(Q*E)/(b-a))*ρ ≤ Q/2 := by
    change (4*(n:ℝ)^2*(Q*physicalLocalGrowth N a b)/(b-a))*
      physicalPersistenceRadius n N a b ≤ Q/2
    rw [physicalPersistenceRadius_eq n N a b Q hQ'.ne']
    exact polynomialPersistenceRadius_scale n (Q*E) a b Q hM hab hQ'.le
  let c := κ*(ρ/2)^m*Real.exp (-N*(V x+ω))
  have hc : 0 < c := by dsimp [c]; positivity
  have hc_bound (y : ℝ) (hy : y ∈ Icc a b) (haway : ρ/2 ≤ y) : c ≤ w y := by
    have hV : V y ≤ V x+ω := by
      have h := physicalField_sqrt_oscillation s₁ s₂ x y (b-a) h₁ h₂
        (ha.trans hx.1) (ha.trans hy.1) (hclose y hy)
      have := (le_abs_self (V y-V x)).trans h
      change V y-V x ≤ ω at this
      linarith
    have hp : (ρ/2)^m ≤ y^m := pow_le_pow_left₀ (by positivity) haway m
    calc
      c ≤ κ*y^m*Real.exp (-N*(V x+ω)) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hp hκ.le) (Real.exp_pos _).le
      _ ≤ κ*y^m*Real.exp (-N*V y) := mul_le_mul_of_nonneg_left
        (Real.exp_le_exp.mpr (by nlinarith [mul_le_mul_of_nonneg_left hV hN]))
        (mul_nonneg hκ.le (pow_nonneg (ha.trans hy.1) m))
      _ ≤ w y := hwlower y hy
  have hlower := polynomial_weighted_integral_lower p n (Q*E) a b x ρ c w
    hd hM ha hab hb hx hρ hlen hscale hc.le hw hc_bound hfi
  have hmul := mul_le_mul_of_nonneg_right hlower (Real.exp_pos (N*ω)).le
  have hexp : Real.exp (-N*(V x+ω))*Real.exp (N*ω) = Real.exp (-N*V x) := by
    rw [← Real.exp_add]
    congr 1
    ring
  have hleft : (ρ*c*(p.eval x)^2/8)*Real.exp (N*ω) =
      (ρ*κ*(ρ/2)^m/8)*((p.eval x)^2*Real.exp (-N*V x)) := by
    dsimp [c]
    calc
      _ = (ρ*κ*(ρ/2)^m/8)*(p.eval x)^2*
          (Real.exp (-N*(V x+ω))*Real.exp (N*ω)) := by ring
      _ = _ := by rw [hexp]; ring
  rw [hleft] at hmul
  have hden : 0 < ρ*κ*(ρ/2)^m := by positivity
  have hfinal : (p.eval x)^2*Real.exp (-N*V x)*(ρ*κ*(ρ/2)^m) ≤
      8*Real.exp (N*ω)*(∫ y in a..b, w y*(p.eval y)^2) := by nlinarith
  calc
    _ ≤ (8*Real.exp (N*ω)*(∫ y in a..b, w y*(p.eval y)^2))/(ρ*κ*(ρ/2)^m) :=
      (le_div_iff₀ hden).mpr hfinal
    _ = _ := by change _ = (8/(ρ*κ*(ρ/2)^m))*Real.exp (N*ω)*_
                ring

end Zeta3.Analysis

import Zeta3.Analysis.ContourNormIntegral

/-!
# A polynomial-loss weighted norm comparison

Choosing local interval length `N⁻²` makes the external-field oscillation
loss bounded independently of `N`.  For degrees at most `δ N`, the actual
weighted supremum is bounded by the actual physical norm times `K N²⁰`.
The positive constant `K` is explicit and independent of the polynomial and
of `N`.  This is stronger than the subexponential loss needed in the proof.
-/

noncomputable section
open Set Polynomial MeasureTheory

namespace Zeta3.Analysis

theorem physicalField_sqrt_continuous (s₁ s₂ : ℝ) (h₁ : 0 < s₁) (h₂ : 0 < s₂) :
    Continuous (fun z => physicalField s₁ s₂ (Real.sqrt z)) := by
  have he : (fun z => physicalField s₁ s₂ (Real.sqrt z)) =
      (fun z => 2*Real.pi*Real.sqrt z + Zeta5.Analysis.externalIntegralFormula 1 (Real.sqrt z) -
        Zeta5.Analysis.externalIntegralFormula s₁ (Real.sqrt z) -
        Zeta5.Analysis.externalIntegralFormula s₂ (Real.sqrt z)) := by
    funext z
    simp only [physicalField, Zeta5.Analysis.externalIntegral_formula
      (by norm_num : (0:ℝ)<1) (Real.sqrt_nonneg z),
      Zeta5.Analysis.externalIntegral_formula h₁ (Real.sqrt_nonneg z),
      Zeta5.Analysis.externalIntegral_formula h₂ (Real.sqrt_nonneg z)]
  rw [he]
  exact (((continuous_const.mul Real.continuous_sqrt).add
    ((Zeta5.Analysis.externalIntegralFormula_continuous (by norm_num : (0:ℝ)<1)).comp
      Real.continuous_sqrt)).sub
        ((Zeta5.Analysis.externalIntegralFormula_continuous h₁).comp Real.continuous_sqrt)).sub
      ((Zeta5.Analysis.externalIntegralFormula_continuous h₂).comp Real.continuous_sqrt)

theorem exists_interval_of_length_contains (B L x : ℝ) (hL : 0 < L) (hLB : L ≤ B)
    (hx : x ∈ Icc 0 B) :
    ∃ a b : ℝ, 0 ≤ a ∧ a < b ∧ b ≤ B ∧ b-a=L ∧ x ∈ Icc a b := by
  by_cases h : x ≤ B-L
  · exact ⟨x,x+L,hx.1,by linarith,by linarith,by ring,⟨le_refl _,by linarith⟩⟩
  · exact ⟨B-L,B,by linarith,by linarith,le_refl _,by ring,⟨by linarith,hx.2⟩⟩

def physicalNormComparisonConstant (δ κ : ℝ) : ℝ :=
  128*(8*(δ+1)^2*Real.exp (3*Real.pi/2))^5*Real.exp (3*Real.pi)/κ

theorem physicalNormComparisonConstant_pos (δ κ : ℝ) (hδ : 0 ≤ δ) (hκ : 0 < κ) :
    0 < physicalNormComparisonConstant δ κ := by
  unfold physicalNormComparisonConstant
  positivity

theorem physical_norm_prefactor_le (n : ℕ) (N δ κ a b : ℝ)
    (hN : 1 ≤ N) (hδ : 0 ≤ δ) (hκ : 0 < κ)
    (hn : (n:ℝ) ≤ δ*N) (hlen : b-a=1/N^2) :
    (8/(physicalPersistenceRadius n N a b*κ*(physicalPersistenceRadius n N a b/2)^4))*
        Real.exp (N*physicalFieldOscillation a b) ≤
      physicalNormComparisonConstant δ κ*N^20 := by
  have hNpos : 0 < N := by linarith
  have hn1 : (n:ℝ)+1 ≤ (δ+1)*N := by nlinarith
  have hω : N*physicalFieldOscillation a b = 3*Real.pi := by
    unfold physicalFieldOscillation
    rw [hlen, Real.sqrt_div (by norm_num : (0:ℝ)≤1), Real.sqrt_one, Real.sqrt_sq hNpos.le]
    field_simp
  have hE : physicalLocalGrowth N a b = Real.exp (3*Real.pi/2) := by
    unfold physicalLocalGrowth
    rw [hω]
  let d := 8*((n:ℝ)+1)^2*N^2*Real.exp (3*Real.pi/2)
  let D := 8*(δ+1)^2*Real.exp (3*Real.pi/2)
  have hd : 0 < d := by dsimp [d]; positivity
  have hD : 0 < D := by dsimp [D]; positivity
  have hρ : physicalPersistenceRadius n N a b = 1/d := by
    unfold physicalPersistenceRadius
    rw [hlen,hE]
    dsimp [d]
    field_simp
  have hdd : d ≤ D*N^4 := by
    have hs := (sq_le_sq₀ (by positivity : 0 ≤ (n:ℝ)+1) (by positivity : 0 ≤ (δ+1)*N)).mpr hn1
    have hm := mul_le_mul_of_nonneg_right hs
      (by positivity : 0 ≤ 8*N^2*Real.exp (3*Real.pi/2))
    dsimp [d,D]
    nlinarith only [hm]
  have hp : d^5 ≤ D^5*N^20 := by
    have hp := pow_le_pow_left₀ hd.le hdd 5
    simpa only [mul_pow, ← pow_mul, show 4*5=20 by omega] using hp
  rw [hρ,hω]
  calc
    _ = (128*Real.exp (3*Real.pi)/κ)*d^5 := by field_simp; ring
    _ ≤ (128*Real.exp (3*Real.pi)/κ)*(D^5*N^20) :=
      mul_le_mul_of_nonneg_left hp (by positivity)
    _ = _ := by unfold physicalNormComparisonConstant; dsimp [D]; ring

theorem normalizedPhysicalNorm_nonneg (N m₁ m₂ : ℕ) (hN : 0 < N) (q : ℝ[X]) :
    0 ≤ normalizedPhysicalNorm N m₁ m₂ q := by
  rw [normalizedPhysicalNorm_integral N m₁ m₂ hN]
  apply integral_nonneg_of_ae
  filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with z hz
  exact mul_nonneg (sq_nonneg _) (physicalScaledDensity_nonneg N m₁ m₂ hN hz.le)

private theorem weighted_square_identity (Q N V : ℝ) :
    (|Q| * Real.exp (-N*V/2))^2 = Q^2*Real.exp (-N*V) := by
  rw [mul_pow, sq_abs, ← Real.exp_nat_mul]
  congr 2
  ring

/-- Uniform weighted real-axis norm comparison, with explicit polynomial
loss.  The support length condition is automatic for all large `N` in any
fixed positive-mass range. -/
theorem actual_physical_uniform_norm_bound (q : ℝ[X]) (n N m₁ m₂ : ℕ) (δ B R : ℝ)
    (hd : q.natDegree ≤ n) (hN : 0 < N) (hm₁ : 0 < m₁) (hm₂ : 0 < m₂)
    (hδ : 0 ≤ δ) (hn : (n:ℝ) ≤ δ*(N:ℝ)) (hBR : B ≤ R)
    (hBN : 1/(N:ℝ)^2 ≤ B) :
    ∀ x ∈ Icc 0 B,
      q.eval x^2*Real.exp (-(N:ℝ)*physicalField ((m₁:ℝ)/N) ((m₂:ℝ)/N) (Real.sqrt x)) ≤
        physicalNormComparisonConstant δ
          (physicalDensityCompactConstant ((m₁:ℝ)/N) ((m₂:ℝ)/N) R)*
            (N:ℝ)^20*normalizedPhysicalNorm N m₁ m₂ q := by
  have hNr : (0:ℝ)<N := by exact_mod_cast hN
  have hN1 : (1:ℝ)≤N := by exact_mod_cast hN
  have hB : 0 < B := lt_of_lt_of_le (by positivity) hBN
  have hR : 0 < R := hB.trans_le hBR
  have hs₁ : 0 < (m₁:ℝ)/N := by positivity
  have hs₂ : 0 < (m₂:ℝ)/N := by positivity
  let V := fun x => physicalField ((m₁:ℝ)/N) ((m₂:ℝ)/N) (Real.sqrt x)
  let f := fun x => |q.eval x| * Real.exp (-(N:ℝ)*V x/2)
  have hf : Continuous f := q.continuous.abs.mul
    (((physicalField_sqrt_continuous _ _ hs₁ hs₂).const_mul (-(N:ℝ))).div_const 2).rexp
  obtain ⟨x₀,hx₀,hmax⟩ := isCompact_Icc.exists_isMaxOn (nonempty_Icc.mpr hB.le) hf.continuousOn
  have hnorm := normalizedPhysicalNorm_nonneg N m₁ m₂ hN q
  have hκ := physicalDensityCompactConstant_pos ((m₁:ℝ)/N) ((m₂:ℝ)/N) R hR
  have hK := physicalNormComparisonConstant_pos δ _ hδ hκ
  intro x hx
  have hfx : 0 ≤ f x := by dsimp [f]; positivity
  have hfx₀ : 0 ≤ f x₀ := by dsimp [f]; positivity
  have hsquare : q.eval x^2*Real.exp (-(N:ℝ)*V x) ≤
      q.eval x₀^2*Real.exp (-(N:ℝ)*V x₀) := by
    have hs := (sq_le_sq₀ hfx hfx₀).mpr (hmax hx)
    simpa only [f, weighted_square_identity] using hs
  by_cases hQ : |q.eval x₀|=0
  · have hqx₀ : q.eval x₀=0 := abs_eq_zero.mp hQ
    have hxzero : q.eval x^2*Real.exp (-(N:ℝ)*V x) ≤ 0 := by simpa [hqx₀] using hsquare
    exact hxzero.trans (mul_nonneg (mul_nonneg hK.le (by positivity)) hnorm)
  · have hQpos : 0 < |q.eval x₀| := lt_of_le_of_ne (abs_nonneg _) (Ne.symm hQ)
    obtain ⟨a,b,ha,hab,hbB,hlen,hxlocal⟩ :=
      exists_interval_of_length_contains B (1/(N:ℝ)^2) x₀ (by positivity) hBN hx₀
    have hmaxlocal : ∀ y ∈ Icc a b, f y ≤ f x₀ :=
      fun y hy => hmax ⟨ha.trans hy.1,hy.2.trans hbB⟩
    have hv := actual_physical_weighted_value_sq_le_norm q n N m₁ m₂ a b x₀ R
      hd hN hm₁ hm₂ ha hab (hbB.trans hBR) hxlocal hQpos hmaxlocal
    have hp := physical_norm_prefactor_le n N δ
      (physicalDensityCompactConstant ((m₁:ℝ)/N) ((m₂:ℝ)/N) R) a b hN1 hδ hκ hn hlen
    exact hsquare.trans (hv.trans (mul_le_mul_of_nonneg_right hp hnorm))

end Zeta3.Analysis

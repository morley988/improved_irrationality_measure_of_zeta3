import Zeta3.Analysis.SpectralLogProduct
import Zeta3.Analysis.AnalyticError
import Mathlib.Analysis.SpecificLimits.Basic

/-! The explicit spectral product remainder has zero quadratic rate.
Flooring the cutoff introduces only continuity at the actual endpoint. -/

noncomputable section
namespace Zeta3.Analysis
open Real Set Filter MeasureTheory
open scoped Topology BigOperators

def spectralCutoffIndex (T : ℝ) (N : ℕ) : ℕ := ⌊T*(N:ℝ)/2⌋₊
def spectralCutoffMesh (T : ℝ) (N : ℕ) : ℝ := 2*(spectralCutoffIndex T N:ℝ)/(N:ℝ)

theorem spectralCutoffMesh_mem {T : ℝ} (hT : 0≤T) (N : ℕ) :
    spectralCutoffMesh T N∈Icc 0 T := by
  by_cases hN : N=0
  · simpa [spectralCutoffMesh,hN] using hT
  have hNr : (0:ℝ)<N := by exact_mod_cast Nat.pos_of_ne_zero hN
  constructor
  · unfold spectralCutoffMesh
    positivity
  · unfold spectralCutoffMesh
    apply (div_le_iff₀ hNr).mpr
    have hfloor := Nat.floor_le (by positivity : 0≤T*(N:ℝ)/2)
    change (spectralCutoffIndex T N:ℝ)≤T*(N:ℝ)/2 at hfloor
    linarith

theorem spectralCutoffMesh_tendsto {T : ℝ} (hT : 0≤T) :
    Tendsto (spectralCutoffMesh T) atTop (𝓝 T) := by
  have h := ((tendsto_nat_floor_mul_div_atTop (a:=T/2) (by positivity)).comp
    tendsto_natCast_atTop_atTop).const_mul 2
  have he : 2*(T/2)=T := by ring
  rw [he] at h
  convert h using 1
  funext N
  unfold spectralCutoffMesh spectralCutoffIndex
  dsimp only [Function.comp_apply]
  rw [show T*(N:ℝ)/2=(T/2)*(N:ℝ) by ring]
  ring

theorem spectralCutoffMesh_profile_tendsto (g : ℝ→ℝ) {T : ℝ} (hT : 0≤T)
    (hg : ContinuousWithinAt g (Icc 0 T) T) :
    Tendsto (fun N:ℕ => g (spectralCutoffMesh T N)) atTop (𝓝 (g T)) := by
  have hwithin : Tendsto (spectralCutoffMesh T) atTop (𝓝[Icc 0 T] T) := by
    apply tendsto_inf.mpr
    exact ⟨spectralCutoffMesh_tendsto hT,
      tendsto_principal.mpr (Filter.Eventually.of_forall (spectralCutoffMesh_mem hT))⟩
  exact hg.tendsto.comp hwithin

theorem spectralCutoffIndex_stage_lt {T : ℝ} (hT : 0≤T) (hcap : T<51/50)
    {n : ℕ} (hn : 0<n) : 2*spectralCutoffIndex T (50*n)<51*n := by
  have hnR : (0:ℝ)<n := by exact_mod_cast hn
  have hfloor := Nat.floor_le (by positivity : 0≤T*((50*n:ℕ):ℝ)/2)
  change (spectralCutoffIndex T (50*n):ℝ)≤T*((50*n:ℕ):ℝ)/2 at hfloor
  have hreal : 2*(spectralCutoffIndex T (50*n):ℝ)<((51*n:ℕ):ℝ) := by
    push_cast at hfloor ⊢
    nlinarith
  exact_mod_cast hreal

theorem log_one_add_polynomial_le (K x : ℝ) (d : ℕ) (hK : 0≤K) (hx : 1≤x) :
    Real.log (1+K*x^d)≤Real.log (1+K)+(d:ℝ)*Real.log x := by
  have hpow : 1≤x^d := one_le_pow₀ hx
  have hbound : 1+K*x^d≤(1+K)*x^d := by nlinarith
  have h := Real.log_le_log (by positivity : 0<1+K*x^d) hbound
  rw [Real.log_mul (by positivity) (by positivity),Real.log_pow] at h
  exact h

theorem spectral_polynomial_log_error_limit (K : ℝ) (hK : 0≤K) :
    Tendsto (fun n:ℕ => (51*(n:ℝ))*Real.log (1+2*K*(50*(n:ℝ))^40)/windowScale n)
      atTop (𝓝 0) := by
  have hnat : Tendsto (fun n:ℕ => ((n:ℝ))⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop
  have hc := hnat.const_mul ((51/2500:ℝ)*Real.log (1+2*K))
  have hl := (Zeta5.Analysis.tendsto_log_mul_nat_div_nat 50 (by norm_num)).const_mul (2040/2500:ℝ)
  have hu := hc.add hl
  simp only [mul_zero,add_zero] at hu
  apply squeeze_zero' _ _ hu
  · filter_upwards [] with n
    apply div_nonneg
    · apply mul_nonneg (by positivity)
      apply Real.log_nonneg
      have hprod : 0≤2*K*(50*(n:ℝ))^40 := by positivity
      linarith
    · exact sq_nonneg _
  · filter_upwards [eventually_gt_atTop (0:ℕ)] with n hn
    have hnR : (0:ℝ)<n := by exact_mod_cast hn
    have hx : 1≤50*(n:ℝ) := by
      have : (1:ℝ)≤n := by exact_mod_cast hn
      linarith
    have hb := log_one_add_polynomial_le (2*K) (50*(n:ℝ)) 40 (by positivity) hx
    have hs := div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_left hb (by positivity : 0≤51*(n:ℝ))) (sq_nonneg (50*(n:ℝ)))
    calc
      _ ≤ 51*(n:ℝ)*(Real.log (1+2*K)+(40:ℝ)*Real.log (50*(n:ℝ)))/(50*(n:ℝ))^2 := hs
      _ = _ := by field_simp [ne_of_gt hnR] <;> ring

def spectralResponseError (K : ℝ) (g : ℝ→ℝ) (T : ℝ) (n : ℕ) : ℝ :=
  Real.log ((51*n).factorial:ℝ)+(51*(n:ℝ))*Real.log (1+2*K*(50*(n:ℝ))^40)+
    2*(50*(n:ℝ))*(g 0-g T)+
      (50*(n:ℝ))*(51*(n:ℝ))*(g (spectralCutoffMesh T (50*n))-g T)

theorem spectralResponseError_limit (K : ℝ) (hK : 0≤K) (g : ℝ→ℝ)
    {T : ℝ} (hT : 0≤T) (hg : ContinuousWithinAt g (Icc 0 T) T) :
    Tendsto (fun n:ℕ => spectralResponseError K g T n/windowScale n) atTop (𝓝 0) := by
  have hnat : Tendsto (fun n:ℕ => ((n:ℝ))⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop
  have hlin := hnat.const_mul ((g 0-g T)/25)
  have hscale : Tendsto (fun n:ℕ => 50*n) atTop atTop :=
    tendsto_atTop_mono (fun n => show n≤50*n by omega) tendsto_id
  have hprof := (spectralCutoffMesh_profile_tendsto g hT hg).comp hscale
  have htail := (hprof.sub (tendsto_const_nhds (x:=g T))).const_mul (51/50:ℝ)
  have h := ((factorial_over_windowScale_limit.add (spectral_polynomial_log_error_limit K hK)).add hlin).add htail
  simp only [sub_self,mul_zero,add_zero] at h
  apply h.congr'
  filter_upwards [eventually_gt_atTop (0:ℕ)] with n hn
  have hnR : (0:ℝ)<n := by exact_mod_cast hn
  unfold spectralResponseError windowScale
  dsimp only [Function.comp_apply]
  field_simp [ne_of_gt hnR] <;> ring

end Zeta3.Analysis

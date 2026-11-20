import Zeta3.Analysis.SpectralLogRate

/-! Spectral eigenvalue estimates and the actual determinant majorant imply
the required response rate, including the factor-two Cauchy radius. -/

noncomputable section
namespace Zeta3.Analysis
open Real Set Filter MeasureTheory
open scoped Topology BigOperators

theorem response_integral_sub_endpoint (g : ℝ→ℝ) (T : ℝ) (hT : 0≤T)
    (hg : AntitoneOn g (Icc 0 T)) :
    (∫ t in 0..T,g t-g T)=(∫ t in 0..T,g t)-T*g T := by
  have hgi : IntervalIntegrable g volume 0 T := by
    apply AntitoneOn.intervalIntegrable
    simpa only [uIcc_of_le hT] using hg
  rw [intervalIntegral.integral_sub hgi intervalIntegrable_const,
    intervalIntegral.integral_const,sub_zero,smul_eq_mul]

/-- This theorem contains no external numerical premise. Its spectral
hypotheses are supplied by the concrete contour and trial-space construction. -/
theorem exists_response_rate_error_of_spectral_bounds
    (g : ℝ→ℝ) (T K : ℝ) (hT : 0≤T) (hcap : T<51/50) (hK : 0≤K)
    (hg : AntitoneOn g (Icc 0 T)) (hcont : ContinuousWithinAt g (Icc 0 T) T)
    (eig : ∀ n:ℕ,Fin (51*n)→ℝ) (response : ℕ→ℂ→ℂ)
    (heig : ∀ n j,0≤eig n j) (hanti : ∀ n,Antitone (eig n))
    (hmajorant : ∀ᶠ n:ℕ in atTop,∀ h:ℂ,
      ‖response n h‖≤((51*n).factorial:ℝ)*∏ j:Fin (51*n),(1+‖h‖*eig n j))
    (hbound : ∀ᶠ n:ℕ in atTop,∀ (k:ℕ) (hk:2*k<51*n),
      2*(k:ℝ)/((50*n:ℕ):ℝ)≤T →
        eig n ⟨2*k,hk⟩≤K*((50*n:ℕ):ℝ)^40*
          Real.exp (((50*n:ℕ):ℝ)*g (2*(k:ℝ)/((50*n:ℕ):ℝ)))) :
    ∃ E:ℕ→ℝ,
      Tendsto (fun n => E n/windowScale n) atTop (𝓝 0) ∧
      ∀ᶠ n:ℕ in atTop,∀ h:ℂ,
        ‖h‖≤2*Real.exp (-((50*n:ℕ):ℝ)*g T) →
          ‖response n h‖≤Real.exp
            (((∫ t in 0..T,g t)-T*g T)*windowScale n+E n) := by
  refine ⟨spectralResponseError K g T,spectralResponseError_limit K hK g hT hcont,?_⟩
  filter_upwards [hmajorant,hbound,eventually_gt_atTop (0:ℕ)] with n hmaj hbd hn
  intro h hh
  let N : ℝ := ((50*n:ℕ):ℝ)
  let m := spectralCutoffIndex T (50*n)
  let D : ℝ := 2*K*N^40
  let eig₂ : Fin (51*n)→ℝ := fun j => 2*eig n j
  have hN : 0<N := by dsimp [N];positivity
  have hmr : 2*m<51*n := spectralCutoffIndex_stage_lt hT hcap hn
  have hmesh : 2*(m:ℝ)/N≤T := (spectralCutoffMesh_mem hT (50*n)).2
  have heig₂ : ∀ j,0≤eig₂ j := fun j => mul_nonneg (by norm_num) (heig n j)
  have hanti₂ : Antitone eig₂ := fun i j hij =>
    mul_le_mul_of_nonneg_left (hanti n hij) (by norm_num)
  have hbd₂ : ∀ (k:ℕ) (hk:k≤m),eig₂ ⟨2*k,by omega⟩≤D*Real.exp (N*g (2*(k:ℝ)/N)) := by
    intro k hk
    have hkt : 2*(k:ℝ)/N≤T := by
      apply le_trans _ hmesh
      apply div_le_div_of_nonneg_right _ hN.le
      exact_mod_cast (show 2*k≤2*m by omega)
    have he := mul_le_mul_of_nonneg_left (hbd k (by omega) hkt) (by norm_num : (0:ℝ)≤2)
    simpa only [eig₂,D,N,mul_assoc] using he
  have hrad : ‖h‖/2≤Real.exp (-g T*N) := by
    have he : -N*g T=-g T*N := by ring
    change ‖h‖≤2*Real.exp (-N*g T) at hh
    rw [he] at hh
    linarith
  have hl := spectral_log_product_le g T N D (‖h‖/2) (51*n) m hN hT
    (by dsimp [D];positivity) (by positivity) hmr hmesh hg hrad eig₂ heig₂ hanti₂ hbd₂
  have heprod : (∏ j:Fin (51*n),(1+(‖h‖/2)*eig₂ j))=
      ∏ j:Fin (51*n),(1+‖h‖*eig n j) := by
    apply Finset.prod_congr rfl
    intro j hj
    dsimp [eig₂]
    ring
  rw [heprod,response_integral_sub_endpoint g T hT hg] at hl
  have hp : 0<∏ j:Fin (51*n),(1+‖h‖*eig n j) := by
    apply Finset.prod_pos
    intro j hj
    have hj0 := heig n j
    positivity
  have hprod := (Real.log_le_iff_le_exp hp).mp hl
  have hf : 0<((51*n).factorial:ℝ) := by positivity
  calc
    ‖response n h‖ ≤ ((51*n).factorial:ℝ)*∏ j:Fin (51*n),(1+‖h‖*eig n j) := hmaj h
    _ ≤ ((51*n).factorial:ℝ)*Real.exp
        (N^2*((∫ t in 0..T,g t)-T*g T)+2*N*(g 0-g T)+
          ((51*n:ℕ):ℝ)*Real.log (1+D)+N*((51*n:ℕ):ℝ)*(g (2*(m:ℝ)/N)-g T)) :=
      mul_le_mul_of_nonneg_left hprod hf.le
    _ = Real.exp (((∫ t in 0..T,g t)-T*g T)*windowScale n+spectralResponseError K g T n) := by
      rw [← Real.exp_log hf,← Real.exp_add]
      congr 1
      dsimp [N,D,m,spectralResponseError,spectralCutoffMesh,windowScale]
      push_cast
      ring

end Zeta3.Analysis

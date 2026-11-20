import Zeta3.Arithmetic.ProfileCells
import Zeta3.Arithmetic.FloorStrip

/-! The finite floor and epsilon witnesses determine the actual arithmetic
parameters at every prime in a cell. -/
noncomputable section
namespace Zeta3.Arithmetic.ProfileCertificate
open Zeta3.Arithmetic Zeta5.Arithmetic Zeta3.Construction.Features

theorem floor_constant_stage_ratio (n p k : ℕ) (c : ℚ) (hc : (50:ℚ)*c=k) :
    ⌊(c:ℝ)/((p:ℝ)/((50*n:ℕ):ℝ))⌋₊=(k*n)/p := by
  have hcR : (50:ℝ)*(c:ℝ)=k := by exact_mod_cast hc
  have he : (c:ℝ)*((50*n:ℕ):ℝ)=((k*n:ℕ):ℝ) := by push_cast; nlinarith
  rw [div_div_eq_mul_div,he,Nat.floor_div_natCast,Nat.floor_natCast]

structure StageParameters (c : Cell) (n p : ℕ) : Prop where
  q : (50*n)/p=c.environment.q
  epsilon : 2*((50*n)%p)/p=c.environment.eps
  d₁ : (110*n)/p=c.environment.d₁
  d₂ : (134*n)/p=c.environment.d₂
  a₁ : (4*n)/p=c.environment.a₁
  a₂ : (16*n)/p=c.environment.a₂

theorem Cell.stage_parameters {c : Cell} (h : c.Valid) {n p : ℕ} (hn : 0<n) (hp : 0<p)
    (hl : (c.lo:ℝ)<(p:ℝ)/((50*n:ℕ):ℝ))
    (hr : (p:ℝ)/((50*n:ℕ):ℝ)<(c.hi:ℝ)) : StageParameters c n p := by
  rcases h with ⟨hlo,hhi,hq,hd₁,hd₂,ha₁,ha₂,heps,hreg,hnorm⟩
  have hq' := FloorBand.floor hq hlo hl hr
  have hd₁' := FloorBand.floor hd₁ hlo hl hr
  have hd₂' := FloorBand.floor hd₂ hlo hl hr
  have ha₁' := FloorBand.floor ha₁ hlo hl hr
  have ha₂' := FloorBand.floor ha₂ hlo hl hr
  rw [floor_constant_stage_ratio n p 50 1 (by norm_num)] at hq'
  rw [floor_constant_stage_ratio n p 110 (11/5) (by norm_num)] at hd₁'
  rw [floor_constant_stage_ratio n p 134 (67/25) (by norm_num)] at hd₂'
  rw [floor_constant_stage_ratio n p 4 (2/25) (by norm_num)] at ha₁'
  rw [floor_constant_stage_ratio n p 16 (8/25) (by norm_num)] at ha₂'
  refine ⟨hq',?_,hd₁',hd₂',ha₁',ha₂'⟩
  have hN : (0:ℝ)<((50*n:ℕ):ℝ) := by exact_mod_cast (by omega : 0<50*n)
  have hmod : (((50*n)%p:ℕ):ℝ)+(p:ℝ)*c.environment.q=((50*n:ℕ):ℝ) := by
    have hh := Nat.mod_add_div (50*n) p
    rw [hq'] at hh
    exact_mod_cast hh
  cases hε : c.environment.epsilon
  · simp only [hε,Bool.false_eq_true,if_false] at heps
    have hg : (2:ℝ)≤(2*(c.environment.q:ℝ)+1)*(c.lo:ℝ) := by exact_mod_cast heps
    have hstep := mul_lt_mul_of_pos_left hl (by positivity : (0:ℝ)<2*c.environment.q+1)
    have hs : (2:ℝ)<(2*(c.environment.q:ℝ)+1)*((p:ℝ)/((50*n:ℕ):ℝ)) := hg.trans_lt hstep
    rw [← mul_div_assoc] at hs
    have hs' := (lt_div_iff₀ hN).mp hs
    have hsmall : 2*((50*n)%p)<p := by
      exact_mod_cast (show 2*((((50*n)%p:ℕ):ℝ))<(p:ℝ) by nlinarith)
    rw [reflected_epsilon (50*n) p hp,if_pos hsmall]
    simp [Environment.eps,hε]
  · simp only [hε,if_true] at heps
    have hg : (2*(c.environment.q:ℝ)+1)*(c.hi:ℝ)≤2 := by exact_mod_cast heps
    have hstep := mul_lt_mul_of_pos_left hr (by positivity : (0:ℝ)<2*c.environment.q+1)
    have hs : (2*(c.environment.q:ℝ)+1)*((p:ℝ)/((50*n:ℕ):ℝ))<2 := hstep.trans_le hg
    rw [← mul_div_assoc] at hs
    have hs' := (div_lt_iff₀ hN).mp hs
    have hsmall : ¬2*((50*n)%p)<p := by
      have hh : (p:ℝ)<2*((((50*n)%p:ℕ):ℝ)) := by nlinarith
      have hh' : p<2*((50*n)%p) := by exact_mod_cast hh
      omega
    rw [reflected_epsilon (50*n) p hp,if_neg hsmall]
    simp [Environment.eps,hε]

theorem Cell.stage_restrictionDepth {c : Cell} (h : c.Valid) {n p : ℕ}
    (hn : 0<n) (hp : 0<p)
    (hl : (c.lo:ℝ)<(p:ℝ)/((50*n:ℕ):ℝ))
    (hr : (p:ℝ)/((50*n:ℕ):ℝ)<(c.hi:ℝ))
    (hstrip : (p:ℝ)+2<(c.hi:ℝ)*((50*n:ℕ):ℝ)) :
    restrictionDepth (4*n) (51*n) p=c.environment.d₁ ∧
      restrictionDepth (16*n) (51*n) p=c.environment.d₂ := by
  have hs := Cell.stage_parameters h hn hp hl hr
  have h₁ := h.2.2.2.1.1
  have h₂ := h.2.2.2.2.1.1
  constructor
  · apply restrictionDepth_eq_full_of_right_strip hp (c.hi:ℝ)
      (by simpa only [show 2*(4*n+51*n)=110*n by omega] using hs.d₁) _ hstrip
    have hh : (c.environment.d₁:ℝ)*(c.hi:ℝ)≤11/5 := by
      have hh := (Rat.cast_le (K:=ℝ)).mpr h₁
      push_cast at hh
      exact hh
    have hm := mul_le_mul_of_nonneg_right hh (show (0:ℝ)≤((50*n:ℕ):ℝ) from Nat.cast_nonneg _)
    push_cast at hm ⊢
    nlinarith
  · apply restrictionDepth_eq_full_of_right_strip hp (c.hi:ℝ)
      (by simpa only [show 2*(16*n+51*n)=134*n by omega] using hs.d₂) _ hstrip
    have hh : (c.environment.d₂:ℝ)*(c.hi:ℝ)≤67/25 := by
      have hh := (Rat.cast_le (K:=ℝ)).mpr h₂
      push_cast at hh
      exact hh
    have hm := mul_le_mul_of_nonneg_right hh (show (0:ℝ)≤((50*n:ℕ):ℝ) from Nat.cast_nonneg _)
    push_cast at hm ⊢
    nlinarith

end Zeta3.Arithmetic.ProfileCertificate

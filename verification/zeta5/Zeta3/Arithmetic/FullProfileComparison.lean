import Zeta3.Arithmetic.SecondProfileComparison
import Zeta3.Arithmetic.RegimeProfileComparison
import Zeta3.Arithmetic.FullCellParameters

/-! Every actual prime valuation is bounded by its certified full-profile cell. -/

noncomputable section
namespace Zeta3.Arithmetic
open Zeta3.Construction ProfileCertificate
variable {p : ℕ} [Fact p.Prime]

theorem scaled_min_upper {v N a b K : ℝ} (hN : 0≤N)
    (ha : v≤N*a+K) (hb : v≤N*b+K) : v≤N*min a b+K := by
  rw [mul_min_of_nonneg _ _ hN,←min_add_add_right]
  exact le_min ha hb

theorem windowNormalizer_fullMiddleExpr_uniform (n : ℕ) (hn : 0<n) (hp : 2<p)
    (hpN : p≤50*n) (hstrong : 536*n+100<p^2) (c : Cell) (hs : StageParameters c n p)
    (hD₁ : Zeta5.Arithmetic.restrictionDepth (4*n) (51*n) p=c.environment.d₁)
    (hD₂ : Zeta5.Arithmetic.restrictionDepth (16*n) (51*n) p=c.environment.d₂)
    (hβ : (1/500:ℝ)<(p:ℝ)/(50*n)) :
    (padicValRat p (windowNormalizer n):ℝ)≤
      (50*(n:ℝ))*c.environment.fullMiddleExpr.eval ((p:ℝ)/(50*n))+20000 := by
  have hfirst := windowNormalizer_firstExpr_uniform n hn hp hpN (by omega) c hs hβ
  have hfirst' : (padicValRat p (windowNormalizer n):ℝ)≤
      (50*(n:ℝ))*c.environment.firstExpr.eval ((p:ℝ)/(50*n))+20000 := by linarith only [hfirst]
  have hsecond := windowNormalizer_secondExpr_uniform n hn hp hpN hstrong c hs hD₁ hD₂ hβ
  change (padicValRat p (windowNormalizer n):ℝ)≤(50*(n:ℝ))*
    min (c.environment.firstExpr.eval ((p:ℝ)/(50*n)))
      (min (min ((c.environment.secondExpr 0 0).eval ((p:ℝ)/(50*n)))
          ((c.environment.secondExpr 0 1).eval ((p:ℝ)/(50*n))))
        (min ((c.environment.secondExpr 1 0).eval ((p:ℝ)/(50*n)))
          ((c.environment.secondExpr 1 1).eval ((p:ℝ)/(50*n)))))+20000
  have hN : (0:ℝ)≤50*n := by positivity
  exact scaled_min_upper hN hfirst'
    (scaled_min_upper hN
      (scaled_min_upper hN (hsecond 0 0 (by omega) (by omega)) (hsecond 0 1 (by omega) (by omega)))
      (scaled_min_upper hN (hsecond 1 0 (by omega) (by omega)) (hsecond 1 1 (by omega) (by omega))))

theorem windowNormalizer_fullCell_uniform (n : ℕ) (hn : 0<n) (hp : 2<p)
    (hstrong : 536*n+100<p^2) (c : Cell) (hc : c.FullValid)
    (hl : (c.lo:ℝ)<(p:ℝ)/((50*n:ℕ):ℝ)) (hr : (p:ℝ)/((50*n:ℕ):ℝ)<(c.hi:ℝ))
    (hstrip : (p:ℝ)+2<(c.hi:ℝ)*((50*n:ℕ):ℝ))
    (hβ : (1/500:ℝ)<(p:ℝ)/(50*n)) :
    (padicValRat p (windowNormalizer n):ℝ)≤
      ((50*n:ℕ):ℝ)*c.affine.real ((p:ℝ)/((50*n:ℕ):ℝ))+20000 := by
  have hs := Cell.full_stage_parameters hc hn (by omega : 0<p) hl hr
  have hD := Cell.full_stage_restrictionDepth hc hn (by omega : 0<p) hl hr hstrip
  have haff := Cell.full_expression_affine hc hl hr
  have hl' : (c.lo:ℝ)<(p:ℝ)/(50*n) := by simpa only [Nat.cast_mul,Nat.cast_ofNat] using hl
  have hr' : (p:ℝ)/(50*n)<(c.hi:ℝ) := by simpa only [Nat.cast_mul,Nat.cast_ofNat] using hr
  rw [←haff]
  simp only [Nat.cast_mul,Nat.cast_ofNat]
  have hN : (0:ℝ)<50*n := by positivity
  rcases hc with ⟨hlo,hhi,hq,hd₁,hd₂,ha₁,ha₂,heps,hreg,hnorm⟩
  cases hcase : c.regime with
  | middle =>
    have hhi1 : (c.hi:ℝ)≤1 := by
      have h := hreg
      rw [hcase] at h
      exact_mod_cast h
    have hratio : (p:ℝ)/(50*n)<1 := hr'.trans_le hhi1
    have hpN : p≤50*n := by
      have hh := (div_lt_iff₀ hN).mp hratio
      exact_mod_cast (show (p:ℝ)≤50*n by nlinarith)
    change (padicValRat p (windowNormalizer n):ℝ)≤
      (50*(n:ℝ))*c.environment.fullMiddleExpr.eval ((p:ℝ)/(50*n))+20000
    exact windowNormalizer_fullMiddleExpr_uniform n hn hp hpN hstrong c hs hD.1 hD.2 hβ
  | upper =>
    have hends : (16/25:ℝ)≤(c.lo:ℝ) ∧ (c.hi:ℝ)≤1 := by
      have h := hreg
      rw [hcase] at h
      constructor
      · have hh := (Rat.cast_le (K:=ℝ)).mpr h.1
        simpa only [Rat.cast_div,Rat.cast_ofNat] using hh
      · exact_mod_cast h.2
    have hratio : (p:ℝ)/(50*n)<1 := hr'.trans_le hends.2
    have hpN : p≤50*n := by
      have hh := (div_lt_iff₀ hN).mp hratio
      exact_mod_cast (show (p:ℝ)≤50*n by nlinarith)
    have hm := windowNormalizer_fullMiddleExpr_uniform n hn hp hpN hstrong c hs hD.1 hD.2 hβ
    have hu := windowNormalizer_upperExpr_uniform n hn hp (by omega) c hs (hends.1.trans_lt hl') hratio
    have hu' : (padicValRat p (windowNormalizer n):ℝ)≤
        (50*(n:ℝ))*c.environment.upperExpr.eval ((p:ℝ)/(50*n))+20000 := by linarith only [hu]
    change (padicValRat p (windowNormalizer n):ℝ)≤
      (50*(n:ℝ))*min (c.environment.fullMiddleExpr.eval ((p:ℝ)/(50*n)))
        (c.environment.upperExpr.eval ((p:ℝ)/(50*n)))+20000
    exact scaled_min_upper hN.le hm hu'
  | large =>
    have hlo1 : (1:ℝ)≤(c.lo:ℝ) := by
      have h := hreg
      rw [hcase] at h
      exact_mod_cast h
    have hlarge := windowNormalizer_largeExpr_uniform n hn c hs (hlo1.trans_lt hl')
    change (padicValRat p (windowNormalizer n):ℝ)≤
      (50*(n:ℝ))*c.environment.largeExpr.eval ((p:ℝ)/(50*n))+20000
    linarith only [hlarge]

end Zeta3.Arithmetic

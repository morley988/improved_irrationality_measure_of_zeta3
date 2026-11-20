import Zeta3.Arithmetic.FirstProfileComparison
import Zeta3.Arithmetic.UpperProfileComparison

/-! Actual prime valuations in the upper and large regimes. -/

noncomputable section
namespace Zeta3.Arithmetic
open Zeta3.Construction ProfileCertificate
variable {p : ℕ} [Fact p.Prime]

theorem windowNormalizer_upperExpr_uniform (n : ℕ) (hn : 0<n) (hp : 2<p)
    (hsmall : 268*n+4<p^2) (c : Cell) (hs : StageParameters c n p)
    (hl : (16/25:ℝ)<(p:ℝ)/(50*n)) (hr : (p:ℝ)/(50*n)<1) :
    (padicValRat p (windowNormalizer n):ℝ)≤
      (50*(n:ℝ))*c.environment.upperExpr.eval ((p:ℝ)/(50*n))+3 := by
  have hN0 : (0:ℝ)<50*n := by positivity
  have hl' := (lt_div_iff₀ hN0).mp hl
  have hr' := (div_lt_iff₀ hN0).mp hr
  have hmp : 32*n<p := by exact_mod_cast (show 32*(n:ℝ)<p by nlinarith)
  have hpN : p≤50*n := by exact_mod_cast (show (p:ℝ)≤50*n by nlinarith)
  have hN2 : 50*n<2*p := by omega
  have hv := windowNormalizer_upperCharge_bound n hn hp hmp hpN (by omega) (by omega)
  have hvR : (padicValRat p (windowNormalizer n):ℝ)≤(upperCharge n p:ℝ) :=
    (Int.cast_le (R:=ℝ)).mpr hv
  exact hvR.trans (upperCharge_le_expression n p hn (by omega) hpN hN2 c.environment hs.q hs.d₁ hs.d₂)

theorem windowNormalizer_largeExpr_uniform (n : ℕ) (hn : 0<n)
    (c : Cell) (hs : StageParameters c n p) (hl : (1:ℝ)<(p:ℝ)/(50*n)) :
    (padicValRat p (windowNormalizer n):ℝ)≤
      (50*(n:ℝ))*c.environment.largeExpr.eval ((p:ℝ)/(50*n))+1 := by
  have hl' := (lt_div_iff₀ (by positivity : (0:ℝ)<50*n)).mp hl
  have hNp : 50*n<p := by exact_mod_cast (show 50*(n:ℝ)<p by nlinarith)
  have hv := windowNormalizer_largeCharge_bound n hn hNp
  have hvR : (padicValRat p (windowNormalizer n):ℝ)≤(largeCharge n p:ℝ) :=
    (Int.cast_le (R:=ℝ)).mpr hv
  exact hvR.trans (largeCharge_le_expression n p hn (Fact.out : p.Prime).pos
    c.environment hs.q hs.d₁ hs.d₂)

end Zeta3.Arithmetic

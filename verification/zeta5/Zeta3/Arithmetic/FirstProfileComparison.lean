import Zeta3.Arithmetic.CellParameters
import Zeta3.Arithmetic.FeatureFirstLayer
import Zeta3.Arithmetic.NormalizerLocalBounds

/-! The actual first feature-rank price is bounded by the finite cell expression. -/

noncomputable section
namespace Zeta3.Arithmetic
open Polynomial Finset Matrix Module OddZeta.FourValue Zeta5.Construction
open Zeta5.Arithmetic Zeta3.Construction Zeta3.Construction.Features ProfileCertificate
variable {p : ℕ} [Fact p.Prime]

theorem windowNormalizer_firstFeature_bound (n : ℕ) (hn : 0<n) (hp : 2<p)
    (hpN : p≤50*n) (hsmall : 268*n+4<p^2) :
    padicValRat p (windowNormalizer n)≤
      (2+((2*((50*n)%p)/p:ℕ):ℤ))*((51*n:ℕ):ℤ)+
        (min (featureRankBound (50*n) (4*n) (51*n) p)
          (featureRankBound (50*n) (16*n) (51*n) p):ℕ) := by
  have hdet := unscaledCentralPencil_feature_rank_bound (p:=p)
    (50*n) (4*n) (16*n) (51*n) hp (by omega) (by omega) (by omega) (by omega)
    (featureStart_ge_window (p:=p) (4*n) (51*n) hp (by omega))
    (featureStart_ge_window (p:=p) (16*n) (51*n) hp (by omega))
  have h := primitiveNormalizer_padicVal_le (Zeta3.Construction.windowDeterminant n) (windowDeterminant_ne_zero n) p _ hdet
  change padicValRat p (windowNormalizer n)≤_ at h
  convert h using 1
  ring

theorem featureRankBound_le_expression (N m r q e D a : ℕ) (s ρ : ℚ)
    (hN : 0<N) (hp : 2<p) (hm : 0<m) (hmJ : m≤featureStart m r p)
    (hq : N/p=q) (he : 2*(N%p)/p=e) (hD : 2*(m+r)/p=D) (ha : m/p=a)
    (hs : (m:ℝ)/N=(s:ℝ)) (hρ : ((m+r:ℕ):ℝ)/N=(ρ:ℝ)) :
    (featureRankBound N m r p:ℝ)≤
      (N:ℝ)*(featureExpr q e D a s ρ).eval ((p:ℝ)/N)+((D:ℝ)+1)/2+(a:ℝ)+3 := by
  have h := featureRankBound_le_profile N m r hp hm hmJ
  rw [featureRankProfile_scaled N m r q e D a hN hq he hD ha,hD,ha,hs,hρ] at h
  simpa only [featureExpr_eval] using h

theorem firstExpr_eval (e : Environment) (β : ℝ) :
    e.firstExpr.eval β=(2+(e.eps:ℝ))*(51/50)+
      min ((featureExpr e.q e.eps e.d₁ e.a₁ (2/25) (11/10)).eval β)
        ((featureExpr e.q e.eps e.d₂ e.a₂ (8/25) (67/50)).eval β) := by
  simp only [Environment.firstExpr,Expr.eval,Expr.const_eval]
  push_cast
  rfl

theorem windowNormalizer_firstExpr_bound (n : ℕ) (hn : 0<n) (hp : 2<p)
    (hpN : p≤50*n) (hsmall : 268*n+4<p^2) (c : Cell) (hs : StageParameters c n p)
    (K : ℝ) (hK₁ : ((c.environment.d₁:ℝ)+1)/2+(c.environment.a₁:ℝ)+3≤K)
    (hK₂ : ((c.environment.d₂:ℝ)+1)/2+(c.environment.a₂:ℝ)+3≤K) :
    (padicValRat p (windowNormalizer n):ℝ)≤
      (50*(n:ℝ))*c.environment.firstExpr.eval ((p:ℝ)/(50*n))+K := by
  have hn0 : (n:ℝ)≠0 := by exact_mod_cast hn.ne'
  have h₁ := featureRankBound_le_expression (50*n) (4*n) (51*n)
    c.environment.q c.environment.eps c.environment.d₁ c.environment.a₁ (2/25) (11/10)
    (by omega) hp (by omega) (featureStart_ge_window (p:=p) (4*n) (51*n) hp (by omega))
    hs.q hs.epsilon (by simpa only [show 2*(4*n+51*n)=110*n by omega] using hs.d₁) hs.a₁
    (by push_cast;field_simp <;> norm_num) (by push_cast;field_simp <;> norm_num)
  have h₂ := featureRankBound_le_expression (50*n) (16*n) (51*n)
    c.environment.q c.environment.eps c.environment.d₂ c.environment.a₂ (8/25) (67/50)
    (by omega) hp (by omega) (featureStart_ge_window (p:=p) (16*n) (51*n) hp (by omega))
    hs.q hs.epsilon (by simpa only [show 2*(16*n+51*n)=134*n by omega] using hs.d₂) hs.a₂
    (by push_cast;field_simp <;> norm_num) (by push_cast;field_simp <;> norm_num)
  push_cast at h₁ h₂
  have h₁' : (featureRankBound (50*n) (4*n) (51*n) p:ℝ)≤
      (50*(n:ℝ))*(featureExpr c.environment.q c.environment.eps c.environment.d₁ c.environment.a₁
        (2/25) (11/10)).eval ((p:ℝ)/(50*n))+K := by linarith only [h₁,hK₁]
  have h₂' : (featureRankBound (50*n) (16*n) (51*n) p:ℝ)≤
      (50*(n:ℝ))*(featureExpr c.environment.q c.environment.eps c.environment.d₂ c.environment.a₂
        (8/25) (67/50)).eval ((p:ℝ)/(50*n))+K := by linarith only [h₂,hK₂]
  have hm := min_le_min h₁' h₂'
  rw [min_add_add_right,←mul_min_of_nonneg _ _ (by positivity : (0:ℝ)≤50*n)] at hm
  have hv : (padicValRat p (windowNormalizer n):ℝ)≤
      (2+((2*((50*n)%p)/p:ℕ):ℝ))*(51*(n:ℝ))+
        min (featureRankBound (50*n) (4*n) (51*n) p:ℝ)
          (featureRankBound (50*n) (16*n) (51*n) p:ℝ) := by
    have h := (Int.cast_le (R:=ℝ)).mpr (windowNormalizer_firstFeature_bound n hn hp hpN hsmall)
    simpa only [Int.cast_add,Int.cast_mul,Int.cast_ofNat,Int.cast_natCast,Int.cast_min,
      Nat.cast_mul,Nat.cast_ofNat,Nat.cast_min] using h
  rw [hs.epsilon] at hv
  rw [firstExpr_eval]
  nlinarith only [hv,hm]

theorem StageParameters.first_errors_le (c : Cell) (n : ℕ) (hn : 0<n)
    (hs : StageParameters c n p) (hβ : (1/500:ℝ)<(p:ℝ)/(50*n)) :
    ((c.environment.d₁:ℝ)+1)/2+(c.environment.a₁:ℝ)+3≤2000 ∧
      ((c.environment.d₂:ℝ)+1)/2+(c.environment.a₂:ℝ)+3≤2000 := by
  have hp : 0<p := (Fact.out : p.Prime).pos
  have hh := (lt_div_iff₀ (by positivity : (0:ℝ)<50*n)).mp hβ
  have hnp : n<10*p := by exact_mod_cast (show (n:ℝ)<10*p by nlinarith)
  have hd₁ : c.environment.d₁<1100 := by
    rw [←hs.d₁]
    exact (Nat.div_lt_iff_lt_mul hp).mpr (by nlinarith)
  have hd₂ : c.environment.d₂<1340 := by
    rw [←hs.d₂]
    exact (Nat.div_lt_iff_lt_mul hp).mpr (by nlinarith)
  have ha₁ : c.environment.a₁<40 := by
    rw [←hs.a₁]
    exact (Nat.div_lt_iff_lt_mul hp).mpr (by nlinarith)
  have ha₂ : c.environment.a₂<160 := by
    rw [←hs.a₂]
    exact (Nat.div_lt_iff_lt_mul hp).mpr (by nlinarith)
  have hd₁R : (c.environment.d₁:ℝ)<1100 := by exact_mod_cast hd₁
  have hd₂R : (c.environment.d₂:ℝ)<1340 := by exact_mod_cast hd₂
  have ha₁R : (c.environment.a₁:ℝ)<40 := by exact_mod_cast ha₁
  have ha₂R : (c.environment.a₂:ℝ)<160 := by exact_mod_cast ha₂
  constructor <;> linarith

theorem windowNormalizer_firstExpr_uniform (n : ℕ) (hn : 0<n) (hp : 2<p)
    (hpN : p≤50*n) (hsmall : 268*n+4<p^2) (c : Cell) (hs : StageParameters c n p)
    (hβ : (1/500:ℝ)<(p:ℝ)/(50*n)) :
    (padicValRat p (windowNormalizer n):ℝ)≤
      (50*(n:ℝ))*c.environment.firstExpr.eval ((p:ℝ)/(50*n))+2000 := by
  have h := StageParameters.first_errors_le c n hn hs hβ
  exact windowNormalizer_firstExpr_bound n hn hp hpN hsmall c hs 2000 h.1 h.2

end Zeta3.Arithmetic

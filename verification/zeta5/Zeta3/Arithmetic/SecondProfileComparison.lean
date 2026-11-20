import Zeta3.Arithmetic.SecondExpressionBound
import Zeta3.Arithmetic.StageFeatureBounds

/-! From the actual second-layer determinant bound to the finite expression. -/
noncomputable section
namespace Zeta3.Arithmetic
open Polynomial Finset Matrix Module OddZeta.FourValue Zeta5.Construction
open Zeta5.Arithmetic Zeta3.Construction Zeta3.Construction.Features ProfileCertificate
variable {p : ℕ} [Fact p.Prime]

theorem windowNormalizer_secondFeatureCost_bound (n : ℕ) (hn : 0<n) (hp : 2<p)
    (hpN : p≤50*n) (hstrong : 536*n+100<p^2) (u₁ u₂ : ℕ) (hu₁ : u₁≤1) (hu₂ : u₂≤1) :
    (padicValRat p (windowNormalizer n):ℝ)≤
      (1+((2*((50*n)%p)/p:ℕ):ℝ))*(51*(n:ℝ))+
      (featureRankBound (50*n) (4*n) (51*n) p:ℝ)+
      (featureRankBound (50*n) (16*n) (51*n) p:ℝ)+
      (secondFeatureCost (50*n) (4*n) (16*n) (51*n) p u₁ u₂:ℝ) := by
  have hv := windowNormalizer_stageFeaturePrice_bound n hn hp hstrong (by omega : p<102*n)
  have hprice : stageFeaturePrice n p≤stageSecondFeaturePrice n p := min_le_right _ _
  have hpriceZ : (stageFeaturePrice n p:ℤ)≤(stageSecondFeaturePrice n p:ℤ) := by exact_mod_cast hprice
  have hv' := hv.trans hpriceZ
  have hvR : (padicValRat p (windowNormalizer n):ℝ)≤(stageSecondFeaturePrice n p:ℝ) := by
    exact_mod_cast hv'
  simp only [stageSecondFeaturePrice,Nat.cast_add,Nat.cast_mul,Nat.cast_one,
    Nat.cast_ofNat] at hvR
  have hB : (secondRankBound (50*n) (4*n) (16*n) (51*n) p:ℝ)≤
      (secondFeatureCost (50*n) (4*n) (16*n) (51*n) p u₁ u₂:ℝ) := by
    exact_mod_cast secondRankBound_le_cost (50*n) (4*n) (16*n) (51*n) p u₁ u₂ hu₁ hu₂
  linarith

theorem windowNormalizer_secondExpr_bound (n : ℕ) (hn : 0<n) (hp : 2<p)
    (hpN : p≤50*n) (hstrong : 536*n+100<p^2) (c : Cell) (hs : StageParameters c n p)
    (hD₁ : restrictionDepth (4*n) (51*n) p=c.environment.d₁)
    (hD₂ : restrictionDepth (16*n) (51*n) p=c.environment.d₂)
    (u₁ u₂ : ℕ) (hu₁ : u₁≤1) (hu₂ : u₂≤1) :
    (padicValRat p (windowNormalizer n):ℝ)≤
      (50*(n:ℝ))*(c.environment.secondExpr u₁ u₂).eval ((p:ℝ)/(50*n))+
      (((c.environment.d₁:ℝ)+1)/2+(c.environment.a₁:ℝ)+3)+
      (((c.environment.d₂:ℝ)+1)/2+(c.environment.a₂:ℝ)+3)+
      11*((c.environment.d₁:ℝ)+1) := by
  exact secondExpr_bound_of_price n hn hp hpN c hs hD₁ hD₂ u₁ u₂ hu₁ hu₂ _
    (windowNormalizer_secondFeatureCost_bound n hn hp hpN hstrong u₁ u₂ hu₁ hu₂)

theorem windowNormalizer_secondExpr_uniform (n : ℕ) (hn : 0<n) (hp : 2<p)
    (hpN : p≤50*n) (hstrong : 536*n+100<p^2) (c : Cell) (hs : StageParameters c n p)
    (hD₁ : restrictionDepth (4*n) (51*n) p=c.environment.d₁)
    (hD₂ : restrictionDepth (16*n) (51*n) p=c.environment.d₂)
    (hβ : (1/500:ℝ)<(p:ℝ)/(50*n))
    (u₁ u₂ : ℕ) (hu₁ : u₁≤1) (hu₂ : u₂≤1) :
    (padicValRat p (windowNormalizer n):ℝ)≤
      (50*(n:ℝ))*(c.environment.secondExpr u₁ u₂).eval ((p:ℝ)/(50*n))+20000 := by
  exact secondExpr_uniform_of_price n hn hp hpN c hs hD₁ hD₂ hβ u₁ u₂ hu₁ hu₂ _
    (windowNormalizer_secondFeatureCost_bound n hn hp hpN hstrong u₁ u₂ hu₁ hu₂)

end Zeta3.Arithmetic

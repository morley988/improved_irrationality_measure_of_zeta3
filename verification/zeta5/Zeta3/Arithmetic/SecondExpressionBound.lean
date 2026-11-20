import Zeta3.Arithmetic.SecondShapeScaling

/-! Pure real comparison for the actual second feature price. -/
noncomputable section
namespace Zeta3.Arithmetic
open Polynomial Finset Matrix Module OddZeta.FourValue Zeta5.Construction
open Zeta5.Arithmetic Zeta3.Construction Zeta3.Construction.Features ProfileCertificate
variable {p : ℕ} [Fact p.Prime]

theorem secondExpr_bound_of_price (n : ℕ) (hn : 0<n) (hp : 2<p)
    (hpN : p≤50*n) (c : Cell) (hs : StageParameters c n p)
    (hD₁ : restrictionDepth (4*n) (51*n) p=c.environment.d₁)
    (hD₂ : restrictionDepth (16*n) (51*n) p=c.environment.d₂)
    (u₁ u₂ : ℕ) (hu₁ : u₁≤1) (hu₂ : u₂≤1) (v : ℝ)
    (hv : v≤(1+((2*((50*n)%p)/p:ℕ):ℝ))*(51*(n:ℝ))+
      (featureRankBound (50*n) (4*n) (51*n) p:ℝ)+
      (featureRankBound (50*n) (16*n) (51*n) p:ℝ)+
      (secondFeatureCost (50*n) (4*n) (16*n) (51*n) p u₁ u₂:ℝ)) :
    v≤
      (50*(n:ℝ))*(c.environment.secondExpr u₁ u₂).eval ((p:ℝ)/(50*n))+
      (((c.environment.d₁:ℝ)+1)/2+(c.environment.a₁:ℝ)+3)+
      (((c.environment.d₂:ℝ)+1)/2+(c.environment.a₂:ℝ)+3)+
      11*((c.environment.d₁:ℝ)+1) := by
  have hn0 : (n:ℝ)≠0 := by exact_mod_cast hn.ne'
  have hA₁ := featureRankBound_le_expression (50*n) (4*n) (51*n)
    c.environment.q c.environment.eps c.environment.d₁ c.environment.a₁ (2/25) (11/10)
    (by omega) hp (by omega) (featureStart_ge_window (p:=p) (4*n) (51*n) hp (by omega))
    hs.q hs.epsilon (by simpa only [show 2*(4*n+51*n)=110*n by omega] using hs.d₁) hs.a₁
    (by push_cast;field_simp <;> norm_num) (by push_cast;field_simp <;> norm_num)
  have hA₂ := featureRankBound_le_expression (50*n) (16*n) (51*n)
    c.environment.q c.environment.eps c.environment.d₂ c.environment.a₂ (8/25) (67/50)
    (by omega) hp (by omega) (featureStart_ge_window (p:=p) (16*n) (51*n) hp (by omega))
    hs.q hs.epsilon (by simpa only [show 2*(16*n+51*n)=134*n by omega] using hs.d₂) hs.a₂
    (by push_cast;field_simp <;> norm_num) (by push_cast;field_simp <;> norm_num)
  have hC := secondFeatureCost_le_profile (p:=p) (50*n) (4*n) (16*n) (51*n)
    u₁ u₂ hp (by omega) (by omega) hu₁ hu₂
  rw [stage_secondCostProfile_scaled n c hn hs hD₁ hD₂ u₁ u₂,hD₁] at hC
  rw [hs.epsilon] at hv
  rw [secondExpr_eval]
  unfold secondShapeValue at hC
  push_cast at hA₁ hA₂ hC
  nlinarith only [hA₁,hA₂,hC,hv]

theorem secondExpr_uniform_of_price (n : ℕ) (hn : 0<n) (hp : 2<p)
    (hpN : p≤50*n) (c : Cell) (hs : StageParameters c n p)
    (hD₁ : restrictionDepth (4*n) (51*n) p=c.environment.d₁)
    (hD₂ : restrictionDepth (16*n) (51*n) p=c.environment.d₂)
    (hβ : (1/500:ℝ)<(p:ℝ)/(50*n))
    (u₁ u₂ : ℕ) (hu₁ : u₁≤1) (hu₂ : u₂≤1) (v : ℝ)
    (hv : v≤(1+((2*((50*n)%p)/p:ℕ):ℝ))*(51*(n:ℝ))+
      (featureRankBound (50*n) (4*n) (51*n) p:ℝ)+
      (featureRankBound (50*n) (16*n) (51*n) p:ℝ)+
      (secondFeatureCost (50*n) (4*n) (16*n) (51*n) p u₁ u₂:ℝ)) :
    v≤
      (50*(n:ℝ))*(c.environment.secondExpr u₁ u₂).eval ((p:ℝ)/(50*n))+20000 := by
  have he := StageParameters.first_errors_le c n hn hs hβ
  have hh := (lt_div_iff₀ (by positivity : (0:ℝ)<50*n)).mp hβ
  have hnp : n<10*p := by exact_mod_cast (show (n:ℝ)<10*p by nlinarith)
  have hd₁ : c.environment.d₁<1100 := by
    rw [←hs.d₁]
    exact (Nat.div_lt_iff_lt_mul (by omega : 0<p)).mpr (by nlinarith)
  have hd₁R : (c.environment.d₁:ℝ)<1100 := by exact_mod_cast hd₁
  have h := secondExpr_bound_of_price n hn hp hpN c hs hD₁ hD₂ u₁ u₂ hu₁ hu₂ v hv
  linarith

end Zeta3.Arithmetic

import Zeta3.Arithmetic.SecondCostProfile
import Zeta3.Arithmetic.SecondScaling
import Zeta3.Arithmetic.FirstProfileComparison

/-! Exact scaling of the complete continuous second-layer cost. -/
noncomputable section
namespace Zeta3.Arithmetic
open Polynomial Finset Matrix Module OddZeta.FourValue Zeta5.Construction
open Zeta5.Arithmetic Zeta3.Construction Zeta3.Construction.Features ProfileCertificate
variable {p : ℕ} [Fact p.Prime]

theorem kernelProfile_scaled (N m r q e D : ℕ) (ρ : ℚ) (hN : 0<N)
    (hq : N/p=q) (he : 2*(N%p)/p=e) (hD : restrictionDepth m r p=D)
    (hρ : ((m+r:ℕ):ℝ)=(N:ℝ)*(ρ:ℝ)) :
    kernelProfile N m r p=(N:ℝ)*(kernelExpr q e D ρ).eval ((p:ℝ)/N) := by
  have hN0 : (N:ℝ)≠0 := by exact_mod_cast hN.ne'
  rw [kernelProfile,hD,maximalWidth_scaled N q e hN hq he,kernelExpr_eval]
  have hh : ((m+r:ℕ):ℝ)-(D:ℝ)*(p:ℝ)/2-(N:ℝ)*profileWidth q e ((p:ℝ)/N)=
      (N:ℝ)*((ρ:ℝ)-(D:ℝ)*((p:ℝ)/N)/2-profileWidth q e ((p:ℝ)/N)) := by
    rw [hρ]
    field_simp <;> ring
  rw [hh,←mul_zero (N:ℝ),←mul_max_of_nonneg _ _ (Nat.cast_nonneg N)]
  simp only [mul_zero]

def secondShapeValue (e : Environment) (u₁ u₂ : ℕ) (β : ℝ) : ℝ :=
  (∑ i:Fin 3,∑ j:Fin 3,
    (numericCap e.eps e.d₁ e.d₂ (2*e.a₁+i.val) (2*e.a₂+j.val) u₁ u₂:ℝ)*
      (e.bucketExpr i j).eval β)+
  ((1-u₁:ℕ):ℝ)*(kernelExpr e.q e.eps e.d₁ (11/10)).eval β+
  ((1-u₂:ℕ):ℝ)*(kernelExpr e.q e.eps e.d₂ (67/50)).eval β

theorem stage_secondCostProfile_scaled (n : ℕ) (c : Cell) (hn : 0<n)
    (hs : StageParameters c n p)
    (hD₁ : restrictionDepth (4*n) (51*n) p=c.environment.d₁)
    (hD₂ : restrictionDepth (16*n) (51*n) p=c.environment.d₂) (u₁ u₂ : ℕ) :
    secondCostProfile (50*n) (4*n) (16*n) (51*n) p u₁ u₂=
      ((50*n:ℕ):ℝ)*secondShapeValue c.environment u₁ u₂ ((p:ℝ)/((50*n:ℕ):ℝ)) := by
  have hN : 0<50*n := by omega
  have hk₁ := kernelProfile_scaled (50*n) (4*n) (51*n) c.environment.q c.environment.eps
    c.environment.d₁ (11/10) hN hs.q hs.epsilon hD₁
    (by push_cast; ring)
  have hk₂ := kernelProfile_scaled (50*n) (16*n) (51*n) c.environment.q c.environment.eps
    c.environment.d₂ (67/50) hN hs.q hs.epsilon hD₂
    (by push_cast; ring)
  unfold secondCostProfile secondShapeValue
  rw [hD₁,hD₂,hs.epsilon,hs.a₁,hs.a₂,hk₁,hk₂]
  simp_rw [stage_pairBucketLength_scaled n c.environment _ _ hn hs.q hs.epsilon hs.a₁ hs.a₂]
  simp only [mul_add,mul_sum]
  apply congrArg₂ (fun x y : ℝ => x+y)
  · apply congrArg₂ (fun x y : ℝ => x+y)
    · apply sum_congr rfl
      intro i hi
      apply sum_congr rfl
      intro j hj
      ring
    · ring
  · ring

theorem secondRankBound_le_cost (N m₁ m₂ r p u₁ u₂ : ℕ) (hu₁ : u₁≤1) (hu₂ : u₂≤1) :
    secondRankBound N m₁ m₂ r p≤secondFeatureCost N m₁ m₂ r p u₁ u₂ := by
  interval_cases u₁ <;> interval_cases u₂ <;> unfold secondRankBound <;> omega

end Zeta3.Arithmetic

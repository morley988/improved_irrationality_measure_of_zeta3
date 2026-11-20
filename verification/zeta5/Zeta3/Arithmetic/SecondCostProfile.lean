import Zeta3.Arithmetic.SecondNumeric
import Zeta3.Arithmetic.SecondBuckets
import Zeta3.Arithmetic.FeatureRankEnvelope

/-! A uniform envelope for the exact second-layer feature cost.  The only
rounding losses are two old endpoint classes and the nine bucket endpoints. -/
noncomputable section
namespace Zeta3.Arithmetic
open Finset Zeta5.Arithmetic Zeta3.Construction.Features
variable {p : ℕ} [Fact p.Prime]

def kernelProfile (N m r p : ℕ) : ℝ :=
  max 0 (((m+r:ℕ):ℝ)-(restrictionDepth m r p:ℝ)*(p:ℝ)/2-maximalWidth N p)

def secondCostProfile (N m₁ m₂ r p u₁ u₂ : ℕ) : ℝ :=
  (∑ i:Fin 3,∑ j:Fin 3,pairBucketLength N m₁ m₂ p i j*
    (numericCap (2*(N%p)/p) (restrictionDepth m₁ r p) (restrictionDepth m₂ r p)
      (2*(m₁/p)+i.val) (2*(m₂/p)+j.val) u₁ u₂:ℝ))+
    ((1-u₁:ℕ):ℝ)*kernelProfile N m₁ r p+
    ((1-u₂:ℕ):ℝ)*kernelProfile N m₂ r p

theorem featureTopKernel_le_profile (N m r : ℕ) (hp : 2<p) (hmr : 0<m+r) :
    (featureTopKernel N m r p:ℝ)≤kernelProfile N m r p := by
  have hJ : featureStart m r p≤m+r :=
    (featureStart_le m r p hmr).trans (Nat.sub_le _ _)
  have hJlo : (restrictionDepth m r p:ℝ)*(p:ℝ)≤2*(featureStart m r p:ℝ) := by
    exact_mod_cast featureStart_twice_lower m r p
  have hw := (maximalWidth_card_bounds N (by omega : p≠2)).2.1
  unfold featureTopKernel kernelProfile
  rw [nat_sub_cast_real]
  apply max_le_max le_rfl
  rw [featureTopCount,Nat.cast_sub hJ]
  linarith

theorem secondLocalRankCap_eq_numeric (N m₁ m₂ r c u₁ u₂ : ℕ) (hp : 0<p)
    (hc : 0<c) (hcp : 2*c<p) :
    secondLocalRankCap N m₁ m₂ r p c u₁ u₂=
      numericCap (2*(N%p)/p) (restrictionDepth m₁ r p) (restrictionDepth m₂ r p)
        (reflectedSize (m₁-1) p c) (reflectedSize (m₂-1) p c) u₁ u₂ := by
  rw [secondLocalRankCap,secondLocalFeatureCount,secondLocalFeatureCount,
    physicalLocalMultiplicity_eq_reflectedSize _ p c hc hcp,
    physicalLocalMultiplicity_eq_reflectedSize _ p c hc hcp,numericCap]
  rw [reflected_epsilon N p hp]
  by_cases h : 2*(N%p)<p <;> simp [h]

theorem numericCap_le_window (e D₁ D₂ k₁ k₂ u₁ u₂ : ℕ) (hu : u₁≤1) :
    numericCap e D₁ D₂ k₁ k₂ u₁ u₂≤D₁+1 :=
  (numericCap_le_left e D₁ D₂ k₁ k₂ u₁ u₂).trans
    ((Nat.sub_le _ _).trans (Nat.add_le_add_left hu _))

theorem sum_endpoint_indicator_le (S : Finset ℕ) (a B : ℕ) :
    (∑ c∈S,if a=c then B else 0)≤B := by
  classical
  by_cases h : a∈S <;> simp [h]

theorem old_second_sum_le_current (N m₁ m₂ r u₁ u₂ : ℕ) (hp : 0<p)
    (hm₁ : 0<m₁) (hm₂ : 0<m₂) (hu₁ : u₁≤1) :
    (∑ c∈nonmaximalReflectedClasses N p,secondLocalRankCap N m₁ m₂ r p c u₁ u₂)≤
      (∑ c∈nonmaximalReflectedClasses N p,
        numericCap (2*(N%p)/p) (restrictionDepth m₁ r p) (restrictionDepth m₂ r p)
          (reflectedSize m₁ p c) (reflectedSize m₂ p c) u₁ u₂)+
      2*(restrictionDepth m₁ r p+1) := by
  let B := restrictionDepth m₁ r p+1
  have hpoint : ∀ c∈nonmaximalReflectedClasses N p,
      secondLocalRankCap N m₁ m₂ r p c u₁ u₂≤
      numericCap (2*(N%p)/p) (restrictionDepth m₁ r p) (restrictionDepth m₂ r p)
        (reflectedSize m₁ p c) (reflectedSize m₂ p c) u₁ u₂+
      (if reflectedLabel p m₁=c then B else 0)+(if reflectedLabel p m₂=c then B else 0) := by
    intro c hc
    have hhalf := mem_Icc.mp (mem_sdiff.mp hc).1
    have hc0 : 0<c := by omega
    have hcp : 2*c<p := by omega
    rw [secondLocalRankCap_eq_numeric N m₁ m₂ r c u₁ u₂ hp hc0 hcp]
    have hcap := numericCap_le_window (2*(N%p)/p) (restrictionDepth m₁ r p)
      (restrictionDepth m₂ r p) (reflectedSize (m₁-1) p c)
      (reflectedSize (m₂-1) p c) u₁ u₂ hu₁
    by_cases h₁ : reflectedLabel p m₁=c
    · simp only [if_pos h₁]
      omega
    by_cases h₂ : reflectedLabel p m₂=c
    · simp only [if_neg h₁,if_pos h₂,add_zero]
      omega
    have he₁ := reflectedSize_succ (m₁-1) p c hc0 hcp
    have he₂ := reflectedSize_succ (m₂-1) p c hc0 hcp
    rw [Nat.sub_add_cancel (by omega : 1≤m₁)] at he₁
    rw [Nat.sub_add_cancel (by omega : 1≤m₂)] at he₂
    simp only [if_neg h₁,if_neg h₂,add_zero] at he₁ he₂ ⊢
    rw [he₁,he₂]
  have hh := Finset.sum_le_sum hpoint
  rw [Finset.sum_add_distrib,Finset.sum_add_distrib] at hh
  have he₁ := sum_endpoint_indicator_le (nonmaximalReflectedClasses N p) (reflectedLabel p m₁) B
  have he₂ := sum_endpoint_indicator_le (nonmaximalReflectedClasses N p) (reflectedLabel p m₂) B
  omega

theorem current_second_sum_le_buckets (N m₁ m₂ r u₁ u₂ : ℕ)
    (hodd : p%2=1) (hu₁ : u₁≤1) :
    ((∑ c∈nonmaximalReflectedClasses N p,
      numericCap (2*(N%p)/p) (restrictionDepth m₁ r p) (restrictionDepth m₂ r p)
        (reflectedSize m₁ p c) (reflectedSize m₂ p c) u₁ u₂:ℕ):ℝ)≤
      (∑ i:Fin 3,∑ j:Fin 3,pairBucketLength N m₁ m₂ p i j*
        (numericCap (2*(N%p)/p) (restrictionDepth m₁ r p) (restrictionDepth m₂ r p)
          (2*(m₁/p)+i.val) (2*(m₂/p)+j.val) u₁ u₂:ℝ))+
      9*((restrictionDepth m₁ r p:ℝ)+1) := by
  let f (i j : ℕ) := numericCap (2*(N%p)/p) (restrictionDepth m₁ r p)
    (restrictionDepth m₂ r p) (2*(m₁/p)+i) (2*(m₂/p)+j) u₁ u₂
  have he := sum_rootDigits_by_buckets N m₁ m₂ p f
  simp only [f,← reflectedSize_eq_digit] at he
  rw [he]
  simp only [Nat.cast_sum,Nat.cast_mul]
  have hpoint : ∀ i j:Fin 3,
      ((pairBucket N m₁ m₂ p i j).card:ℝ)*(f i.val j.val:ℝ)≤
      pairBucketLength N m₁ m₂ p i j*(f i.val j.val:ℝ)+
        ((restrictionDepth m₁ r p:ℝ)+1) := by
    intro i j
    have hc := pairBucket_card_le N m₁ m₂ p i j hodd
    have hb : (f i.val j.val:ℝ)≤(restrictionDepth m₁ r p:ℝ)+1 := by
      exact_mod_cast numericCap_le_window (2*(N%p)/p) (restrictionDepth m₁ r p)
        (restrictionDepth m₂ r p) (2*(m₁/p)+i.val) (2*(m₂/p)+j.val) u₁ u₂ hu₁
    have hmul := mul_le_mul_of_nonneg_right hc (Nat.cast_nonneg (f i.val j.val): (0:ℝ)≤_)
    nlinarith
  calc
    _ ≤ ∑ i:Fin 3,∑ j:Fin 3,(pairBucketLength N m₁ m₂ p i j*(f i.val j.val:ℝ)+
        ((restrictionDepth m₁ r p:ℝ)+1)) :=
      sum_le_sum (fun i _ => sum_le_sum (fun j _ => hpoint i j))
    _ = _ := by
      simp only [Finset.sum_add_distrib,Finset.sum_const,Finset.card_univ,
        Fintype.card_fin,nsmul_eq_mul,Nat.cast_ofNat]
      dsimp only [f]
      ring

theorem secondFeatureCost_le_profile (N m₁ m₂ r u₁ u₂ : ℕ) (hp : 2<p)
    (hm₁ : 0<m₁) (hm₂ : 0<m₂) (hu₁ : u₁≤1) (hu₂ : u₂≤1) :
    (secondFeatureCost N m₁ m₂ r p u₁ u₂:ℝ)≤
      secondCostProfile N m₁ m₂ r p u₁ u₂+11*((restrictionDepth m₁ r p:ℝ)+1) := by
  have hold : ((∑ c∈nonmaximalReflectedClasses N p,
      secondLocalRankCap N m₁ m₂ r p c u₁ u₂:ℕ):ℝ)≤
      ((∑ c∈nonmaximalReflectedClasses N p,
        numericCap (2*(N%p)/p) (restrictionDepth m₁ r p) (restrictionDepth m₂ r p)
          (reflectedSize m₁ p c) (reflectedSize m₂ p c) u₁ u₂:ℕ):ℝ)+
        2*((restrictionDepth m₁ r p:ℝ)+1) := by
    exact_mod_cast old_second_sum_le_current N m₁ m₂ r u₁ u₂ (by omega) hm₁ hm₂ hu₁
  have hnew := current_second_sum_le_buckets N m₁ m₂ r u₁ u₂
    ((Fact.out : p.Prime).mod_two_eq_one_iff_ne_two.mpr (by omega)) hu₁
  have hk₁ := mul_le_mul_of_nonneg_left (featureTopKernel_le_profile N m₁ r hp (by omega))
    (Nat.cast_nonneg (1-u₁): (0:ℝ)≤_)
  have hk₂ := mul_le_mul_of_nonneg_left (featureTopKernel_le_profile N m₂ r hp (by omega))
    (Nat.cast_nonneg (1-u₂): (0:ℝ)≤_)
  simp only [secondFeatureCost,Nat.cast_add,Nat.cast_mul,secondCostProfile]
  linarith

end Zeta3.Arithmetic

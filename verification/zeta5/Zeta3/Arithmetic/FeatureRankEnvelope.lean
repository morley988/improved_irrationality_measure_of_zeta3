import Zeta3.Arithmetic.FeatureProfile

/-! A uniform affine envelope for the exact feature rank. -/
noncomputable section
namespace Zeta3.Arithmetic
open Polynomial Finset Matrix Module OddZeta.FourValue Zeta5.Construction
open Zeta5.Arithmetic Zeta3.Construction.Features
variable {p : ℕ} [Fact p.Prime]

def maximalWidth (N p : ℕ) : ℝ :=
  ((N%p:ℕ):ℝ)-((2*(N%p)/p:ℕ):ℝ)*(p:ℝ)/2

theorem maximalWidth_card_bounds (N : ℕ) (hp2 : p≠2) :
    0≤maximalWidth N p ∧ maximalWidth N p≤((maximalReflectedClasses N p).card:ℝ) ∧
      ((maximalReflectedClasses N p).card:ℝ)≤maximalWidth N p+1/2 := by
  have hp := (Fact.out : p.Prime).pos
  have hodd := (Fact.out : p.Prime).mod_two_eq_one_iff_ne_two.mpr hp2
  have hcard := maximalReflectedClasses_card_real (N:=N) hp hodd
  have hd : ((N%p:ℕ):ℝ)+(p:ℝ)*((N/p:ℕ):ℝ)=N := by exact_mod_cast Nat.mod_add_div N p
  unfold maximalWidth
  rw [reflected_epsilon N p hp] at hcard ⊢
  by_cases hσ : 2*(N%p)<p
  · simp only [if_pos hσ,Nat.cast_zero,zero_mul,zero_div,sub_zero,add_zero] at hcard ⊢
    exact ⟨Nat.cast_nonneg _, by nlinarith, by nlinarith⟩
  · have hs : (p:ℝ)≤2*((N%p:ℕ):ℝ) := by exact_mod_cast (by omega : p≤2*(N%p))
    simp only [if_neg hσ,Nat.cast_one,one_mul] at hcard ⊢
    exact ⟨by linarith, by nlinarith, by nlinarith⟩

theorem featureStart_ge_window (m r : ℕ) (hp2 : 2<p) (hpr : p<2*r) :
    m≤featureStart m r p := by
  have hp : 0<p := by omega
  have hR : 0<m+r := by omega
  have hh := Nat.lt_mul_div_succ (2*(m+r)-2) hp
  have hl := featureStart_twice_lower m r p
  change 2*(m+r)-2 < p*(restrictionDepth m r p+1) at hh
  have hsub : 2*(m+r)-2+2=2*(m+r) := Nat.sub_add_cancel (by omega)
  nlinarith

theorem restrictionDepth_le_full (m r p : ℕ) : restrictionDepth m r p≤2*(m+r)/p :=
  Nat.div_le_div_right (Nat.sub_le _ _)

theorem full_depth_le_succ_restriction (m r : ℕ) (hp : 2<p) (hR : 0<m+r) :
    2*(m+r)/p≤restrictionDepth m r p+1 := by
  have h₁ := Nat.lt_mul_div_succ (2*(m+r)-2) (by omega : 0<p)
  have h₂ := Nat.div_mul_le_self (2*(m+r)) p
  change 2*(m+r)-2 < p*(restrictionDepth m r p+1) at h₁
  by_contra hh
  have hD : restrictionDepth m r p+2≤2*(m+r)/p := by omega
  have hmul := Nat.mul_le_mul_right p hD
  have hsub : 2*(m+r)-2+2=2*(m+r) := Nat.sub_add_cancel (by omega)
  nlinarith

theorem featureRankBound_floor_envelope (N m r : ℕ) (hp : 2<p) (hm : 0<m)
    (hmJ : m≤featureStart m r p) :
    (featureRankBound N m r p:ℝ)+(maximalOldRootCount N m p:ℝ) ≤
      ((2*(m+r)/p:ℕ):ℝ)*((maximalReflectedClasses N p).card:ℝ)+
      min (((m+r:ℕ):ℝ) - ((2*(m+r)/p:ℕ):ℝ)*(p:ℝ)/2)
        ((maximalReflectedClasses N p).card:ℝ) := by
  have hR : 0<m+r := by omega
  have he := featureRankBound_add_oldRoots N m r (by omega) hmJ
  have heR : (featureRankBound N m r p:ℝ)+(maximalOldRootCount N m p:ℝ) =
      (restrictionDepth m r p:ℝ)*((maximalReflectedClasses N p).card:ℝ)+
      min (featureTopCount m r p:ℝ) ((maximalReflectedClasses N p).card:ℝ) := by
    exact_mod_cast he
  rw [heR]
  have hDlo := restrictionDepth_le_full m r p
  have hDhi := full_depth_le_succ_restriction m r hp hR
  have hprod := Nat.div_mul_le_self (2*(m+r)) p
  have hprodR : ((2*(m+r)/p:ℕ):ℝ)*(p:ℝ)≤2*((m+r:ℕ):ℝ) := by exact_mod_cast hprod
  have hH0 : 0≤((m+r:ℕ):ℝ)-((2*(m+r)/p:ℕ):ℝ)*(p:ℝ)/2 := by linarith
  by_cases hD : restrictionDepth m r p=2*(m+r)/p
  · rw [hD]
    apply add_le_add le_rfl
    apply min_le_min_right
    have hJlo := featureStart_twice_lower m r p
    rw [hD] at hJlo
    have hJloR : ((2*(m+r)/p:ℕ):ℝ)*(p:ℝ)≤2*(featureStart m r p:ℝ) := by exact_mod_cast hJlo
    have hJhi : featureStart m r p≤m+r := (featureStart_le m r p hR).trans (Nat.sub_le _ _)
    rw [featureTopCount,Nat.cast_sub hJhi]
    linarith
  · have hD' : 2*(m+r)/p=restrictionDepth m r p+1 := by omega
    have hD'R : ((2*(m+r)/p:ℕ):ℝ)=(restrictionDepth m r p:ℝ)+1 := by exact_mod_cast hD'
    have hmin := min_le_right (featureTopCount m r p:ℝ) ((maximalReflectedClasses N p).card:ℝ)
    have hmin0 : 0≤min (((m+r:ℕ):ℝ)-((2*(m+r)/p:ℕ):ℝ)*(p:ℝ)/2)
        ((maximalReflectedClasses N p).card:ℝ) := le_min hH0 (Nat.cast_nonneg _)
    nlinarith

def featureRankProfile (N m r p : ℕ) : ℝ :=
  ((2*(m+r)/p:ℕ):ℝ)*maximalWidth N p - maximalOldRootProfile N m p +
    min (((m+r:ℕ):ℝ)-((2*(m+r)/p:ℕ):ℝ)*(p:ℝ)/2) (maximalWidth N p)

theorem featureRankBound_le_profile (N m r : ℕ) (hp : 2<p) (hm : 0<m)
    (hmJ : m≤featureStart m r p) :
    (featureRankBound N m r p:ℝ)≤featureRankProfile N m r p+
      (((2*(m+r)/p:ℕ):ℝ)+1)/2+((m/p:ℕ):ℝ)+3 := by
  have hfloor := featureRankBound_floor_envelope N m r hp hm hmJ
  have hroot := maximalOldRootCount_profile_lower N m p hm
    ((Fact.out : p.Prime).mod_two_eq_one_iff_ne_two.mpr (by omega))
  have hw := maximalWidth_card_bounds N (by omega : p≠2)
  let d : ℝ := ((2*(m+r)/p:ℕ):ℝ)
  let H : ℝ := ((m+r:ℕ):ℝ)-d*(p:ℝ)/2
  have hprod := mul_le_mul_of_nonneg_left hw.2.2 (show 0≤d from Nat.cast_nonneg _)
  have hmin : min H ((maximalReflectedClasses N p).card:ℝ) ≤ min H (maximalWidth N p)+1/2 := by
    exact (min_le_min_left H hw.2.2).trans (min_add_error_le H (maximalWidth N p) (1/2) (by norm_num))
  unfold featureRankProfile
  change (featureRankBound N m r p:ℝ)≤d*maximalWidth N p-maximalOldRootProfile N m p+
    min H (maximalWidth N p)+(d+1)/2+((m/p:ℕ):ℝ)+3
  change (featureRankBound N m r p:ℝ)+(maximalOldRootCount N m p:ℝ)≤
    d*((maximalReflectedClasses N p).card:ℝ)+min H ((maximalReflectedClasses N p).card:ℝ) at hfloor
  nlinarith

end Zeta3.Arithmetic

import Zeta3.Arithmetic.FeatureCounts
import Zeta5.Arithmetic.RankProfileComparison

/-! Uniform rounding control from actual feature ranks to continuous
piecewise affine functions. Every rounding error is independent of n on
any fixed prime band. -/
noncomputable section
namespace Zeta3.Arithmetic
open Polynomial Finset Matrix Module OddZeta.FourValue Zeta5.Construction
open Zeta5.Arithmetic Zeta3.Construction.Features

theorem reflectedNodes_succ (m p c : ℕ) (hc : 0<c) (hcp : 2*c<p) :
    reflectedNodes (m+1) p c =
      if reflectedLabel p (m+1)=c then insert (m+1) (reflectedNodes m p c)
      else reflectedNodes m p c := by
  have hp : 0<p := by omega
  ext i
  rw [mem_reflectedNodes]
  split_ifs with he
  · have he' := (reflectedLabel_eq_iff p (m+1) c hp hc hcp).mp he
    by_cases hi : i=m+1
    · subst i
      simp [he', mem_insert, mem_reflectedNodes]
    · simp only [mem_insert, mem_reflectedNodes]
      omega
  · have he' : ¬((m+1)%p=c ∨ (m+1)%p=p-c) :=
      (reflectedLabel_eq_iff p (m+1) c hp hc hcp).not.mp he
    by_cases hi : i=m+1
    · subst i
      rw [mem_reflectedNodes]
      omega
    · rw [mem_reflectedNodes]
      omega

theorem reflectedSize_succ (m p c : ℕ) (hc : 0<c) (hcp : 2*c<p) :
    reflectedSize (m+1) p c = reflectedSize m p c +
      if reflectedLabel p (m+1)=c then 1 else 0 := by
  rw [← reflectedNodes_card (m+1) p c hc hcp, reflectedNodes_succ m p c hc hcp,
    ← reflectedNodes_card m p c hc hcp]
  split_ifs with he
  · rw [card_insert_of_notMem]
    have hn : m+1 ∉ reflectedNodes m p c := by
      intro h
      have := mem_reflectedNodes.mp h
      omega
    exact hn
  · simp

theorem sum_reflectedSize_succ_le (S : Finset ℕ) (m p : ℕ)
    (hS : ∀ c∈S, 0<c ∧ 2*c<p) :
    (∑ c∈S, reflectedSize (m+1) p c) ≤ (∑ c∈S, reflectedSize m p c)+1 := by
  have he : (∑ c∈S, reflectedSize (m+1) p c) = (∑ c∈S, reflectedSize m p c)+
      ∑ c∈S, if reflectedLabel p (m+1)=c then 1 else 0 := by
    rw [← sum_add_distrib]
    apply sum_congr rfl
    intro c hc
    exact reflectedSize_succ m p c (hS c hc).1 (hS c hc).2
  rw [he]
  have hsum : (∑ c∈S, if reflectedLabel p (m+1)=c then (1:ℕ) else 0) ≤ 1 := by
    simp only [sum_ite_eq]
    split_ifs <;> omega
  omega

theorem maximalOldRootCount_current_lower (N m p : ℕ) (hm : 0<m) :
    (∑ c∈maximalReflectedClasses N p, reflectedSize m p c) ≤ maximalOldRootCount N m p+1 := by
  have h := sum_reflectedSize_succ_le (maximalReflectedClasses N p) (m-1) p
    (fun c hc => maximalReflectedClasses_half N p hc)
  rw [Nat.sub_add_cancel hm] at h
  have he : (∑ c∈maximalReflectedClasses N p, reflectedSize (m-1) p c) = maximalOldRootCount N m p := by
    unfold maximalOldRootCount
    apply sum_congr rfl
    intro c hc
    have hh := maximalReflectedClasses_half N p hc
    exact (physicalLocalMultiplicity_eq_reflectedSize _ p c hh.1 hh.2).symm
  rwa [he] at h

def rootPrefixProfile (q : ℕ) (s x P : ℝ) : ℝ :=
  2*q*x + min x s + max 0 (x+s-P)

theorem nat_sub_cast_real (a b : ℕ) : ((a-b : ℕ):ℝ) = max 0 ((a:ℝ)-b) := by
  by_cases h : b≤a
  · rw [Nat.cast_sub h, max_eq_right (by exact_mod_cast (show (0:ℤ)≤(a:ℤ)-b by omega) : (0:ℝ)≤(a:ℝ)-b)]
  · rw [Nat.sub_eq_zero_of_le (by omega), Nat.cast_zero, max_eq_left]
    exact_mod_cast (show (a:ℤ)-(b:ℤ)≤0 by omega)

theorem reflectedPrefixCount_bounds (m p a : ℕ) :
    rootPrefixProfile (m/p) ((m%p:ℕ):ℝ) a p ≤ (reflectedPrefixCount m p a : ℝ) ∧
      (reflectedPrefixCount m p a : ℝ) ≤ rootPrefixProfile (m/p) ((m%p:ℕ):ℝ) a p+1 := by
  unfold reflectedPrefixCount rootPrefixProfile
  simp only [Nat.cast_add,Nat.cast_mul,Nat.cast_ofNat,Nat.cast_min,nat_sub_cast_real,Nat.cast_one]
  constructor
  · have hh : max 0 ((a:ℝ)+((m%p:ℕ):ℝ)-p) ≤ max 0 ((a:ℝ)+((m%p:ℕ):ℝ)+1-p) := max_le_max le_rfl (by linarith)
    linarith
  · have hh : max 0 ((a:ℝ)+((m%p:ℕ):ℝ)+1-p) ≤ max 0 ((a:ℝ)+((m%p:ℕ):ℝ)-p)+1 := by
      rw [← max_add_add_right]
      exact max_le_max (by norm_num) (by linarith)
    linarith

theorem rootPrefixProfile_mono (q : ℕ) (s P : ℝ) : Monotone (fun x => rootPrefixProfile q s x P) := by
  intro x y hxy
  unfold rootPrefixProfile
  exact add_le_add (add_le_add (mul_le_mul_of_nonneg_left hxy (by positivity))
    (min_le_min_right s hxy)) (max_le_max le_rfl (by linarith))

theorem rootPrefixProfile_step (q : ℕ) (s P x e : ℝ) (he : 0≤e) :
    rootPrefixProfile q s (x+e) P ≤ rootPrefixProfile q s x P+(2*q+2)*e := by
  have hm : min (x+e) s ≤ min x s+e := by
    rw [← min_add_add_right]
    exact min_le_min le_rfl (by linarith)
  have hx : max 0 (x+e+s-P) ≤ max 0 (x+s-P)+e := by
    rw [← max_add_add_right]
    exact max_le_max (by simpa using he) (by linarith)
  unfold rootPrefixProfile
  nlinarith

def maximalOldRootProfile (N m p : ℕ) : ℝ :=
  if 2*(N%p)<p then rootPrefixProfile (m/p) ((m%p:ℕ):ℝ) ((N%p:ℕ):ℝ) p
  else rootPrefixProfile (m/p) ((m%p:ℕ):ℝ) ((p:ℝ)/2) p -
    rootPrefixProfile (m/p) ((m%p:ℕ):ℝ) ((p:ℝ)-((N%p:ℕ):ℝ)) p

theorem maximalOldRootCount_profile_lower (N m p : ℕ) (hm : 0<m) (hodd : p%2=1) :
    maximalOldRootProfile N m p - ((m/p:ℕ):ℝ)-3 ≤ (maximalOldRootCount N m p:ℝ) := by
  have hp : 0<p := by omega
  have hs := Nat.mod_lt N hp
  have hcurrent := maximalOldRootCount_current_lower N m p hm
  have hcurrentR : ((∑ c∈maximalReflectedClasses N p,reflectedSize m p c):ℝ) ≤
      (maximalOldRootCount N m p:ℝ)+1 := by exact_mod_cast hcurrent
  by_cases hσ : 2*(N%p)<p
  · rw [maximalOldRootProfile,if_pos hσ]
    rw [← Nat.cast_sum] at hcurrentR
    rw [maximalReflectedClasses_low N p hodd hσ,← reflectedPrefixCount_eq_sum m p (N%p) hp hs] at hcurrentR
    have hh := (reflectedPrefixCount_bounds m p (N%p)).1
    have hq : (0:ℝ)≤((m/p:ℕ):ℝ) := Nat.cast_nonneg _
    linarith
  · rw [maximalOldRootProfile,if_neg hσ]
    have hsplit := sum_Icc_prefix_split (fun c => reflectedSize m p c)
      (p-N%p) ((p-1)/2) (by omega) (by omega)
    rw [← maximalReflectedClasses_high N p hodd (by omega),
      ← reflectedPrefixCount_eq_sum m p ((p-1)/2) hp (by omega),
      ← reflectedPrefixCount_eq_sum m p (p-N%p-1) hp (by omega)] at hsplit
    have hsplitR : (reflectedPrefixCount m p ((p-1)/2):ℝ) =
        (reflectedPrefixCount m p (p-N%p-1):ℝ)+
          ((∑c∈maximalReflectedClasses N p, reflectedSize m p c):ℝ) := by exact_mod_cast hsplit
    have hlo := (reflectedPrefixCount_bounds m p ((p-1)/2)).1
    have hhi := (reflectedPrefixCount_bounds m p (p-N%p-1)).2
    have hx : (((p-1)/2:ℕ):ℝ)+1/2=(p:ℝ)/2 := by
      have hh : 2*((p-1)/2)+1=p := by omega
      have hhR : 2*(((p-1)/2:ℕ):ℝ)+1=p := by exact_mod_cast hh
      linarith
    have hstep := rootPrefixProfile_step (m/p) ((m%p:ℕ):ℝ) p (((p-1)/2:ℕ):ℝ) (1/2) (by norm_num)
    rw [hx] at hstep
    have hal : ((p-N%p-1:ℕ):ℝ) ≤ (p:ℝ)-((N%p:ℕ):ℝ) := by
      rw [Nat.cast_sub (by omega : 1≤p-N%p),Nat.cast_sub (by omega : N%p≤p)]
      norm_num
    have hmono := rootPrefixProfile_mono (m/p) ((m%p:ℕ):ℝ) (p:ℝ) hal
    linarith

end Zeta3.Arithmetic

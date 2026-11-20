import Zeta3.Arithmetic.FeatureFirstLayer

/-! Exact closed counts underlying the feature-rank profile. -/
noncomputable section
namespace Zeta3.Arithmetic
open Polynomial Finset Matrix Module OddZeta.FourValue Zeta5.Construction
open Zeta5.Arithmetic Zeta3.Construction.Features

theorem reflectedNodes_mono {N M p c : ℕ} (hNM : N ≤ M) :
    reflectedNodes N p c ⊆ reflectedNodes M p c := by
  intro i hi
  obtain ⟨hi0, hiN, hm⟩ := mem_reflectedNodes.mp hi
  exact mem_reflectedNodes.mpr ⟨hi0, hiN.trans hNM, hm⟩

theorem reflectedSize_mono {N M p c : ℕ} (hNM : N ≤ M) (hc : 0 < c) (hcp : 2*c<p) :
    reflectedSize N p c ≤ reflectedSize M p c := by
  rw [← reflectedNodes_card N p c hc hcp, ← reflectedNodes_card M p c hc hcp]
  exact card_le_card (reflectedNodes_mono hNM)

theorem maximalReflectedClasses_low (N p : ℕ) (hodd : p%2=1) (hσ : 2*(N%p)<p) :
    maximalReflectedClasses N p = Icc 1 (N%p) := by
  have hp : 0<p := by omega
  have he := reflected_epsilon N p hp
  ext c
  simp only [maximalReflectedClasses, mem_filter, mem_Icc, reflectedSize, he, if_pos hσ]
  split_ifs <;> omega

theorem maximalReflectedClasses_high (N p : ℕ) (hodd : p%2=1) (hσ : p≤2*(N%p)) :
    maximalReflectedClasses N p = Icc (p-N%p) ((p-1)/2) := by
  have hp : 0<p := by omega
  have hs := Nat.mod_lt N hp
  have he := reflected_epsilon N p hp
  ext c
  simp only [maximalReflectedClasses, mem_filter, mem_Icc, reflectedSize, he, if_neg (by omega : ¬2*(N%p)<p)]
  split_ifs <;> omega

def reflectedPrefixCount (m p a : ℕ) : ℕ :=
  2*(m/p)*a + min a (m%p) + (a + m%p + 1 - p)

theorem reflectedPrefixCount_eq_sum (m p a : ℕ) (hp : 0<p) (ha : a<p) :
    reflectedPrefixCount m p a = ∑ c ∈ Icc 1 a, reflectedSize m p c :=
  (sum_reflectedSize m p a hp ha).symm

theorem sum_Icc_prefix_split {M : Type*} [AddCommMonoid M]
    (f : ℕ → M) (l n : ℕ) (hl : 0<l) (hln : l≤n+1) :
    (∑ c ∈ Icc 1 n, f c) = (∑ c ∈ Icc 1 (l-1), f c) + ∑ c ∈ Icc l n, f c := by
  have hs : Icc 1 n = Icc 1 (l-1) ∪ Icc l n := by
    ext c
    simp only [mem_union,mem_Icc]
    omega
  have hd : Disjoint (Icc 1 (l-1)) (Icc l n) := by
    apply disjoint_left.mpr
    intro c hc hd
    have := mem_Icc.mp hc
    have := mem_Icc.mp hd
    omega
  rw [hs,sum_union hd]

def maximalOldRootCount (N m p : ℕ) : ℕ :=
  ∑ c ∈ maximalReflectedClasses N p, physicalLocalMultiplicity (m-1) p c

theorem maximalOldRootCount_low (N m p : ℕ) (hodd : p%2=1) (hσ : 2*(N%p)<p) :
    maximalOldRootCount N m p = reflectedPrefixCount (m-1) p (N%p) := by
  unfold maximalOldRootCount
  have he : (∑ c ∈ maximalReflectedClasses N p, physicalLocalMultiplicity (m-1) p c) =
      ∑ c ∈ maximalReflectedClasses N p, reflectedSize (m-1) p c := by
    apply sum_congr rfl
    intro c hc
    have hhalf := maximalReflectedClasses_half N p hc
    exact physicalLocalMultiplicity_eq_reflectedSize (m-1) p c hhalf.1 hhalf.2
  rw [he,maximalReflectedClasses_low N p hodd hσ, reflectedPrefixCount_eq_sum]
  · omega
  · exact Nat.mod_lt N (by omega)

theorem maximalOldRootCount_high (N m p : ℕ) (hodd : p%2=1) (hσ : p≤2*(N%p)) :
    maximalOldRootCount N m p + reflectedPrefixCount (m-1) p (p-N%p-1) =
      reflectedPrefixCount (m-1) p ((p-1)/2) := by
  have hp : 0<p := by omega
  have hs := Nat.mod_lt N hp
  have hh := sum_Icc_prefix_split (fun c => reflectedSize (m-1) p c)
    (p-N%p) ((p-1)/2) (by omega) (by omega)
  unfold maximalOldRootCount
  have he : (∑ c ∈ maximalReflectedClasses N p, physicalLocalMultiplicity (m-1) p c) =
      ∑ c ∈ maximalReflectedClasses N p, reflectedSize (m-1) p c := by
    apply sum_congr rfl
    intro c hc
    have hhalf := maximalReflectedClasses_half N p hc
    exact physicalLocalMultiplicity_eq_reflectedSize (m-1) p c hhalf.1 hhalf.2
  rw [he,maximalReflectedClasses_high N p hodd hσ,
    reflectedPrefixCount_eq_sum _ _ _ hp (by omega), reflectedPrefixCount_eq_sum _ _ _ hp (by omega)]
  exact (add_comm _ _).trans hh.symm

variable {p : ℕ} [Fact p.Prime]

theorem physicalOldRoots_le_depth {m r c : ℕ} (hp2 : p≠2)
    (hmJ : m≤featureStart m r p) (hc : 0<c) (hcp : 2*c<p) :
    physicalLocalMultiplicity (m-1) p c ≤ restrictionDepth m r p := by
  rw [physicalLocalMultiplicity_eq_reflectedSize (m-1) p c hc hcp]
  have hodd := (Fact.out : p.Prime).mod_two_eq_one_iff_ne_two.mpr hp2
  have h := reflectedSize_mono (Nat.sub_le_sub_right hmJ 1) hc hcp
  rw [featureStart, reflectedSize_halfBoundary _ p c hodd hc hcp] at h
  exact h

theorem featureLowCount_add_oldRoots (N m r : ℕ) (hp2 : p≠2)
    (hmJ : m≤featureStart m r p) :
    featureLowCount N m r p + maximalOldRootCount N m p =
      restrictionDepth m r p * (maximalReflectedClasses N p).card := by
  unfold featureLowCount maximalOldRootCount
  rw [← sum_add_distrib]
  have he : (∑ c ∈ maximalReflectedClasses N p,
      (restrictionDepth m r p - physicalLocalMultiplicity (m-1) p c +
        physicalLocalMultiplicity (m-1) p c)) =
      ∑ c ∈ maximalReflectedClasses N p, restrictionDepth m r p := by
    apply sum_congr rfl
    intro c hc
    have hh := maximalReflectedClasses_half N p hc
    exact Nat.sub_add_cancel (physicalOldRoots_le_depth hp2 hmJ hh.1 hh.2)
  rw [he,sum_const]
  simp [Nat.mul_comm]

theorem featureRankBound_add_oldRoots (N m r : ℕ) (hp2 : p≠2)
    (hmJ : m≤featureStart m r p) :
    featureRankBound N m r p + maximalOldRootCount N m p =
      restrictionDepth m r p * (maximalReflectedClasses N p).card +
        min (featureTopCount m r p) (maximalReflectedClasses N p).card := by
  unfold featureRankBound
  rw [add_right_comm, featureLowCount_add_oldRoots N m r hp2 hmJ]

end Zeta3.Arithmetic

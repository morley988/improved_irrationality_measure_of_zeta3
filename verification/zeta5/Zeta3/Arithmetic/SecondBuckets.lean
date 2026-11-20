import Zeta3.Arithmetic.FeatureProfile
import Zeta3.Construction.SecondDimensions

/-! Exact three-way old-root buckets and uniform bounds for their nine
pairwise intersections. The real lengths are piecewise affine. -/
noncomputable section
namespace Zeta3.Arithmetic
open Polynomial Finset Zeta5.Arithmetic Zeta3.Construction.Features

def rootDigit (m p c : ℕ) : ℕ :=
  (if c≤m%p then 1 else 0)+(if p-c≤m%p then 1 else 0)

theorem rootDigit_lt_three (m p c : ℕ) : rootDigit m p c<3 := by
  unfold rootDigit
  split_ifs <;> omega

theorem reflectedSize_eq_digit (m p c : ℕ) : reflectedSize m p c=2*(m/p)+rootDigit m p c := by
  unfold reflectedSize rootDigit
  omega

def rootBucket (m p : ℕ) (j : Fin 3) : Finset ℕ :=
  (Icc 1 ((p-1)/2)).filter (fun c => rootDigit m p c=j.val)

def rootBucketLower (m p : ℕ) (j : Fin 3) : ℕ :=
  if j.val=0 then m%p+1 else if j.val=1 then 1 else p-m%p

def rootBucketUpper (m p : ℕ) (j : Fin 3) : ℕ :=
  if j.val=1 then min (m%p) (p-m%p-1) else (p-1)/2

theorem rootBucket_eq_interval (m p : ℕ) (j : Fin 3) (hodd : p%2=1) :
    rootBucket m p j=Icc (rootBucketLower m p j) (rootBucketUpper m p j) := by
  have hp : 0<p := by omega
  have hs := Nat.mod_lt m hp
  fin_cases j <;> ext c <;>
    norm_num [rootBucket,rootBucketLower,rootBucketUpper,mem_filter,mem_Icc,rootDigit] <;>
    (try split_ifs) <;> omega

def nonmaximalLower (N p : ℕ) : ℕ := if 2*(N%p)<p then N%p+1 else 1
def nonmaximalUpper (N p : ℕ) : ℕ := if 2*(N%p)<p then (p-1)/2 else p-N%p-1

theorem nonmaximal_eq_interval (N p : ℕ) (hodd : p%2=1) :
    nonmaximalReflectedClasses N p=Icc (nonmaximalLower N p) (nonmaximalUpper N p) := by
  have hp : 0<p := by omega
  have hs := Nat.mod_lt N hp
  unfold nonmaximalReflectedClasses nonmaximalLower nonmaximalUpper
  by_cases hσ : 2*(N%p)<p
  · rw [if_pos hσ,if_pos hσ,maximalReflectedClasses_low N p hodd hσ]
    ext c
    simp only [mem_sdiff,mem_Icc]
    omega
  · rw [if_neg hσ,if_neg hσ,maximalReflectedClasses_high N p hodd (by omega)]
    ext c
    simp only [mem_sdiff,mem_Icc]
    omega

def pairBucket (N m₁ m₂ p : ℕ) (i j : Fin 3) : Finset ℕ :=
  (nonmaximalReflectedClasses N p).filter (fun c => rootDigit m₁ p c=i.val ∧ rootDigit m₂ p c=j.val)

theorem pairBucket_eq_interval (N m₁ m₂ p : ℕ) (i j : Fin 3) (hodd : p%2=1) :
    pairBucket N m₁ m₂ p i j=
      Icc (max (nonmaximalLower N p) (max (rootBucketLower m₁ p i) (rootBucketLower m₂ p j)))
        (min (nonmaximalUpper N p) (min (rootBucketUpper m₁ p i) (rootBucketUpper m₂ p j))) := by
  have he : pairBucket N m₁ m₂ p i j=
      nonmaximalReflectedClasses N p ∩ (rootBucket m₁ p i ∩ rootBucket m₂ p j) := by
    ext c
    simp only [pairBucket,rootBucket,mem_filter,mem_inter,nonmaximalReflectedClasses,mem_sdiff]
    tauto
  rw [he,nonmaximal_eq_interval N p hodd,rootBucket_eq_interval m₁ p i hodd,
    rootBucket_eq_interval m₂ p j hodd]
  ext c
  simp only [mem_inter,mem_Icc,le_min_iff,max_le_iff]
  tauto

def rootLowerReal (m p : ℕ) (j : Fin 3) : ℝ :=
  if j.val=0 then ((m%p:ℕ):ℝ) else if j.val=1 then 0 else (p:ℝ)-((m%p:ℕ):ℝ)
def rootUpperReal (m p : ℕ) (j : Fin 3) : ℝ :=
  if j.val=1 then min ((m%p:ℕ):ℝ) ((p:ℝ)-((m%p:ℕ):ℝ)) else (p:ℝ)/2

theorem rootBucket_lower_real (m p : ℕ) (j : Fin 3) (hp : 0<p) :
    rootLowerReal m p j≤(rootBucketLower m p j:ℝ) := by
  have hs := Nat.mod_lt m hp
  fin_cases j
  · simp [rootLowerReal,rootBucketLower]
  · simp [rootLowerReal,rootBucketLower]
  · simp only [rootLowerReal,rootBucketLower]
    norm_num
    rw [Nat.cast_sub hs.le]
    linarith

theorem rootBucket_upper_real (m p : ℕ) (j : Fin 3) (hp : 0<p) :
    (rootBucketUpper m p j:ℝ)≤rootUpperReal m p j := by
  have hs := Nat.mod_lt m hp
  have hhalf : 2*((p-1)/2)≤p := by omega
  have hhalfR : 2*(((p-1)/2:ℕ):ℝ)≤p := by exact_mod_cast hhalf
  fin_cases j
  · norm_num [rootUpperReal,rootBucketUpper]
    linarith
  · change ((min (m%p) (p-m%p-1):ℕ):ℝ) ≤ min ((m%p:ℕ):ℝ) ((p:ℝ)-((m%p:ℕ):ℝ))
    rw [Nat.cast_min]
    apply min_le_min le_rfl
    rw [Nat.cast_sub (by omega : 1≤p-m%p),Nat.cast_sub hs.le]
    norm_num
  · norm_num [rootUpperReal,rootBucketUpper]
    linarith

def nonmaximalLowerReal (N p : ℕ) : ℝ := if 2*(N%p)<p then ((N%p:ℕ):ℝ) else 0
def nonmaximalUpperReal (N p : ℕ) : ℝ :=
  if 2*(N%p)<p then (p:ℝ)/2 else (p:ℝ)-((N%p:ℕ):ℝ)

theorem nonmaximal_lower_real (N p : ℕ) : nonmaximalLowerReal N p≤(nonmaximalLower N p:ℝ) := by
  unfold nonmaximalLowerReal nonmaximalLower
  split_ifs <;> push_cast <;> linarith

theorem nonmaximal_upper_real (N p : ℕ) (hp : 0<p) :
    (nonmaximalUpper N p:ℝ)≤nonmaximalUpperReal N p := by
  have hs := Nat.mod_lt N hp
  unfold nonmaximalUpperReal nonmaximalUpper
  split_ifs
  · have hh : 2*((p-1)/2)≤p := by omega
    have hhR : 2*(((p-1)/2:ℕ):ℝ)≤p := by exact_mod_cast hh
    linarith
  · rw [Nat.cast_sub (by omega : 1≤p-N%p),Nat.cast_sub hs.le]
    norm_num

def pairBucketLength (N m₁ m₂ p : ℕ) (i j : Fin 3) : ℝ :=
  max 0 (min (nonmaximalUpperReal N p) (min (rootUpperReal m₁ p i) (rootUpperReal m₂ p j))-
    max (nonmaximalLowerReal N p) (max (rootLowerReal m₁ p i) (rootLowerReal m₂ p j)))

theorem nat_card_interval_le_length (a b : ℕ) (L U : ℝ)
    (ha : L≤(a:ℝ)) (hb : (b:ℝ)≤U) :
    ((Icc a b).card:ℝ)≤max 0 (U-L)+1 := by
  rw [Nat.card_Icc,nat_sub_cast_real]
  push_cast
  have h := max_le_max (show (0:ℝ)≤0 by rfl) (show (b:ℝ)+1-a≤U-L+1 by linarith)
  have h' : max 0 (U-L+1)≤max 0 (U-L)+1 := by
    rw [← max_add_add_right]
    exact max_le_max (by norm_num) le_rfl
  exact h.trans h'

theorem pairBucket_card_le (N m₁ m₂ p : ℕ) (i j : Fin 3) (hodd : p%2=1) :
    ((pairBucket N m₁ m₂ p i j).card:ℝ)≤pairBucketLength N m₁ m₂ p i j+1 := by
  have hp : 0<p := by omega
  rw [pairBucket_eq_interval N m₁ m₂ p i j hodd]
  apply nat_card_interval_le_length
  · rw [Nat.cast_max,Nat.cast_max]
    exact max_le_max (nonmaximal_lower_real N p)
      (max_le_max (rootBucket_lower_real m₁ p i hp) (rootBucket_lower_real m₂ p j hp))
  · rw [Nat.cast_min,Nat.cast_min]
    exact min_le_min (nonmaximal_upper_real N p hp)
      (min_le_min (rootBucket_upper_real m₁ p i hp) (rootBucket_upper_real m₂ p j hp))

theorem sum_rootDigits_by_buckets (N m₁ m₂ p : ℕ) (f : ℕ → ℕ → ℕ) :
    (∑ c∈nonmaximalReflectedClasses N p, f (rootDigit m₁ p c) (rootDigit m₂ p c))=
      ∑ i : Fin 3, ∑ j : Fin 3, (pairBucket N m₁ m₂ p i j).card*f i.val j.val := by
  let idx (c : ℕ) : Fin 3 × Fin 3 :=
    (⟨rootDigit m₁ p c,rootDigit_lt_three m₁ p c⟩,⟨rootDigit m₂ p c,rootDigit_lt_three m₂ p c⟩)
  have hm : ∀ c∈nonmaximalReflectedClasses N p,idx c∈(univ:Finset (Fin 3×Fin 3)) := by simp
  have hh := sum_fiberwise_of_maps_to hm (fun c => f (rootDigit m₁ p c) (rootDigit m₂ p c))
  rw [← hh,Fintype.sum_prod_type]
  apply sum_congr rfl
  intro i hi
  apply sum_congr rfl
  intro j hj
  have hs : (nonmaximalReflectedClasses N p).filter (fun c => idx c=(i,j))=pairBucket N m₁ m₂ p i j := by
    ext c
    simp [pairBucket,idx,Prod.mk.injEq,Fin.ext_iff]
  rw [hs]
  have he : (∑ c∈pairBucket N m₁ m₂ p i j, f (rootDigit m₁ p c) (rootDigit m₂ p c))=
      ∑ c∈pairBucket N m₁ m₂ p i j,f i.val j.val := by
    apply sum_congr rfl
    intro c hc
    obtain ⟨_,hc₁,hc₂⟩ := mem_filter.mp hc
    rw [hc₁,hc₂]
  rw [he,sum_const]
  simp

end Zeta3.Arithmetic

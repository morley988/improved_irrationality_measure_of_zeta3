import Zeta3.Construction.SecondLinear
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.Algebra.Group.Nat.Even

/-! The exact parity cap for the physical second-layer matrix. -/

noncomputable section
namespace Zeta3.Construction.Features
open Matrix Module Finset

def evenFinEquiv (n : ℕ) : {i : Fin n // i.val % 2 = 0} ≃ Fin ((n+1)/2) where
  toFun i := ⟨i.val.val/2,by have := i.val.isLt;have := i.property;omega⟩
  invFun j := ⟨⟨2*j.val,by have := j.isLt;omega⟩,by change (2*j.val)%2=0;omega⟩
  left_inv i := by apply Subtype.ext;apply Fin.ext;dsimp;have := i.property;omega
  right_inv j := by apply Fin.ext;dsimp;omega

def oddFinEquiv (n : ℕ) : {i : Fin n // i.val % 2 = 1} ≃ Fin (n/2) where
  toFun i := ⟨i.val.val/2,by have := i.val.isLt;have := i.property;omega⟩
  invFun j := ⟨⟨2*j.val+1,by have := j.isLt;omega⟩,by change (2*j.val+1)%2=1;omega⟩
  left_inv i := by apply Subtype.ext;apply Fin.ext;dsimp;have := i.property;omega
  right_inv j := by apply Fin.ext;dsimp;omega

theorem card_even_fin (n : ℕ) :
    (univ.filter (fun i : Fin n => i.val%2=0)).card=(n+1)/2 := by
  have h := Fintype.card_congr (evenFinEquiv n)
  simpa only [Fintype.card_subtype,Fintype.card_fin] using h

theorem card_odd_fin (n : ℕ) :
    (univ.filter (fun i : Fin n => i.val%2=1)).card=n/2 := by
  have h := Fintype.card_congr (oddFinEquiv n)
  simpa only [Fintype.card_subtype,Fintype.card_fin] using h

theorem matrix_rank_le_supported_rows {K ι κ : Type*} [Field K]
    [Fintype ι] [Fintype κ] (M : Matrix ι κ K) (s : Finset ι)
    (h : ∀i,i∉s→∀j,M i j=0) : M.rank≤s.card := by
  apply Matrix.rank_le_card_of_support_subset
  rw [Function.support_subset_iff']
  intro i hi
  funext j
  exact h i hi j

theorem matrix_rank_le_supported_columns {K ι κ : Type*} [Field K]
    [Fintype ι] [Fintype κ] (M : Matrix ι κ K) (s : Finset κ)
    (h : ∀j,j∉s→∀i,M i j=0) : M.rank≤s.card := by
  rw [←Matrix.rank_transpose M]
  exact matrix_rank_le_supported_rows M.transpose s h

theorem matrix_rank_add_le {K ι κ : Type*} [Field K]
    [Fintype ι] [Fintype κ] (M N : Matrix ι κ K) :
    (M+N).rank≤M.rank+N.rank := by
  rw [Matrix.rank,Matrix.mulVecLin_add]
  exact linear_rank_add_le M.mulVecLin N.mulVecLin

theorem matrix_rank_le_parity_cap {K : Type*} [Field K] {n₁ n₂ : ℕ}
    (M : Matrix (Fin n₁) (Fin n₂) K)
    (hzero : ∀i j,Even (i.val+j.val)→M i j=0) :
    M.rank≤min ((n₁+1)/2) (n₂/2)+min (n₁/2) ((n₂+1)/2) := by
  classical
  let A : Matrix (Fin n₁) (Fin n₂) K := fun i j => if i.val%2=0 then M i j else 0
  let B : Matrix (Fin n₁) (Fin n₂) K := fun i j => if i.val%2=1 then M i j else 0
  have hM : M=A+B := by
    funext i j
    change M i j=(if i.val%2=0 then M i j else 0)+(if i.val%2=1 then M i j else 0)
    by_cases hi : i.val%2=0
    · simp [hi,show i.val%2≠1 by omega]
    · simp [hi,show i.val%2=1 by omega]
  have hAr : A.rank≤(n₁+1)/2 := by
    rw [←card_even_fin n₁]
    apply matrix_rank_le_supported_rows
    intro i hi j
    have hin : i.val%2≠0 := by simpa only [mem_filter,mem_univ,true_and] using hi
    simp [A,hin]
  have hAc : A.rank≤n₂/2 := by
    rw [←card_odd_fin n₂]
    apply matrix_rank_le_supported_columns
    intro j hj i
    have hjn : j.val%2≠1 := by simpa only [mem_filter,mem_univ,true_and] using hj
    by_cases hi : i.val%2=0
    · have he : Even (i.val+j.val) := Nat.even_iff.mpr (by omega)
      simp [A,hi,hzero i j he]
    · simp [A,hi]
  have hBr : B.rank≤n₁/2 := by
    rw [←card_odd_fin n₁]
    apply matrix_rank_le_supported_rows
    intro i hi j
    have hin : i.val%2≠1 := by simpa only [mem_filter,mem_univ,true_and] using hi
    simp [B,hin]
  have hBc : B.rank≤(n₂+1)/2 := by
    rw [←card_even_fin n₂]
    apply matrix_rank_le_supported_columns
    intro j hj i
    have hjn : j.val%2≠0 := by simpa only [mem_filter,mem_univ,true_and] using hj
    by_cases hi : i.val%2=1
    · have he : Even (i.val+j.val) := Nat.even_iff.mpr (by omega)
      simp [B,hi,hzero i j he]
    · simp [B,hi]
  rw [hM]
  exact (matrix_rank_add_le A B).trans (Nat.add_le_add (le_min hAr hAc) (le_min hBr hBc))

end Zeta3.Construction.Features

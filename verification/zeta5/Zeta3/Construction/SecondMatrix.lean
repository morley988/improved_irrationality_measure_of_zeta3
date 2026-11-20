import Zeta3.Construction.SecondLinear
import Zeta3.Construction.SecondParityRank

/-! The rank of a bilinear pullback is bounded by the exact finite
coefficient matrix. -/
noncomputable section
namespace Zeta3.Construction.Features
open Module Matrix Finset
variable {K V W U : Type*} [Field K] [AddCommGroup V] [Module K V]
  [AddCommGroup W] [Module K W] [AddCommGroup U] [Module K U]
  [FiniteDimensional K V] [FiniteDimensional K W] [FiniteDimensional K U]

theorem linear_rank_le_of_ker_le (f : V →ₗ[K] W) (g : V →ₗ[K] U)
    (hker : g.ker≤f.ker) : finrank K f.range≤finrank K g.range := by
  have hk := Submodule.finrank_mono hker
  have hf := f.finrank_range_add_finrank_ker
  have hg := g.finrank_range_add_finrank_ker
  omega

theorem bilinear_rank_le_matrix {n₁ n₂ : ℕ}
    (B : V →ₗ[K] Module.Dual K W) (A : V →ₗ[K] (Fin n₁→K))
    (C : W →ₗ[K] (Fin n₂→K)) (M : Matrix (Fin n₁) (Fin n₂) K)
    (hB : ∀ x y,B x y=∑ i:Fin n₁,∑ j:Fin n₂,A x i*M i j*C y j) :
    finrank K B.range≤M.rank := by
  let f := M.transpose.mulVecLin.comp A
  have hker : f.ker≤B.ker := by
    intro x hx
    apply LinearMap.ext
    intro y
    change B x y=0
    rw [hB,Finset.sum_comm]
    apply Finset.sum_eq_zero
    intro j hj
    have hz : (∑ i:Fin n₁,M i j*A x i)=0 := congrFun hx j
    calc
      (∑ i:Fin n₁,A x i*M i j*C y j)=
        (∑ i:Fin n₁,M i j*A x i)*C y j := by
          rw [Finset.sum_mul]
          apply Finset.sum_congr rfl
          intro i hi
          ring
      _ = 0 := by rw [hz,zero_mul]
  have h := linear_rank_le_of_ker_le B f hker
  have hg := linear_rank_comp_le_left A M.transpose.mulVecLin
  change finrank K f.range≤M.transpose.rank at hg
  rw [Matrix.rank_transpose] at hg
  exact h.trans hg

end Zeta3.Construction.Features

import Zeta3.Construction.FeatureTopRank
import Mathlib.LinearAlgebra.Matrix.Block
import Mathlib.LinearAlgebra.Dimension.Constructions

/-! Linear algebra for complete local features. The hypotheses describe
actual maps and actual low-column interpolation, not asserted dimensions. -/

noncomputable section
namespace Zeta3.Construction.Features
open Matrix Module

section Maps
variable {K V W U Z : Type*} [Field K]
  [AddCommGroup V] [Module K V] [FiniteDimensional K V]
  [AddCommGroup W] [Module K W] [FiniteDimensional K W]
  [AddCommGroup U] [Module K U] [FiniteDimensional K U]
  [AddCommGroup Z] [Module K Z] [FiniteDimensional K Z]

theorem finrank_range_eq_of_ker_eq (f : V→ₗ[K]W) (g : V→ₗ[K]U) (h : f.ker=g.ker) :
    finrank K f.range = finrank K g.range := by
  have hf := f.finrank_range_add_finrank_ker
  have hg := g.finrank_range_add_finrank_ker
  rw [h] at hf
  omega

theorem pair_range_finrank (a : V→ₗ[K]W) (b : V→ₗ[K]U)
    (hlow : ∀ w, ∃ x, a x=w ∧ b x=0) :
    finrank K (a.prod b).range = finrank K W + finrank K b.range := by
  let f : (a.prod b).range →ₗ[K] (W × b.range) :=
    { toFun := fun x => (x.val.1, ⟨x.val.2, by
        obtain ⟨v,hv⟩ := x.property
        exact ⟨v, congrArg Prod.snd hv⟩⟩)
      map_add' := by intro x y; rfl
      map_smul' := by intro c x; rfl }
  have hfi : Function.Injective f := by
    intro x y h
    apply Subtype.ext
    apply Prod.ext
    · exact congrArg (fun z : W×b.range => z.1) h
    · exact congrArg (fun z : W×b.range => (z.2:U)) h
  have hfs : Function.Surjective f := by
    rintro ⟨w,z⟩
    obtain ⟨x,hx⟩ := z.property
    obtain ⟨y,hay,hby⟩ := hlow (w-a x)
    have he : (a.prod b) (x+y) = (w,(z:U)) := by
      apply Prod.ext
      · change a (x+y)=w
        rw [map_add,hay]
        abel
      · change b (x+y)=(z:U)
        rw [map_add,hx,hby,add_zero]
    refine ⟨⟨(w,(z:U)),⟨x+y,he⟩⟩,?_⟩
    rfl
  rw [(LinearEquiv.ofBijective f ⟨hfi,hfs⟩).finrank_eq, Module.finrank_prod]

end Maps

section Matrices
variable {K α β γ : Type*} [Field K]
  [Fintype α] [Fintype β] [Fintype γ]
  [DecidableEq α] [DecidableEq β] [DecidableEq γ]

def columnInsertion (f : β→γ) : Matrix γ β K := fun j b => if j=f b then 1 else 0

theorem mul_columnInsertion (A : Matrix α γ K) (f : β→γ) :
    A * columnInsertion f = A.submatrix id f := by
  ext a b
  simp [columnInsertion, Matrix.mul_apply]

theorem columnInsertion_mul_submatrix (A : Matrix α γ K) (f : β→γ)
    (hf : Function.Injective f) (hz : ∀ j, j∉Set.range f → ∀ a, A a j=0) :
    A.submatrix id f * (columnInsertion f).transpose = A := by
  ext a j
  by_cases hj : j∈Set.range f
  · obtain ⟨b,rfl⟩ := hj
    simp only [Matrix.mul_apply, Matrix.submatrix_apply, id_eq, Matrix.transpose_apply,
      columnInsertion]
    rw [Finset.sum_eq_single b]
    · simp
    · intro b' hb' hne
      rw [if_neg (fun h => hne (hf h.symm)), mul_zero]
    · simp
  · rw [hz j hj a]
    apply Finset.sum_eq_zero
    intro b hb
    simp only [Matrix.submatrix_apply, id_eq, Matrix.transpose_apply, columnInsertion]
    rw [if_neg (fun h => hj ⟨b,h.symm⟩), mul_zero]

theorem rank_submatrix_of_zero_outside (A : Matrix α γ K) (f : β→γ)
    (hf : Function.Injective f) (hz : ∀ j, j∉Set.range f → ∀ a, A a j=0) :
    (A.submatrix id f).rank=A.rank := by
  apply le_antisymm
  · exact Matrix.rank_submatrix_le A id f
  · calc
      A.rank = (A.submatrix id f * (columnInsertion f).transpose).rank :=
        congrArg Matrix.rank (columnInsertion_mul_submatrix A f hf hz).symm
      _ ≤ (A.submatrix id f).rank := Matrix.rank_mul_le_left _ _

theorem low_interpolation_from_minor (A : Matrix α γ K) (B : Matrix β γ K)
    (f : α→γ) (hdet : (A.submatrix id f).det≠0)
    (hzero : B.submatrix id f=0) :
    ∀ w, ∃ x, A.mulVecLin x=w ∧ B.mulVecLin x=0 := by
  intro w
  have hsurj : Function.Surjective ((A.submatrix id f).mulVecLin) :=
    Matrix.mulVec_surjective_iff_isUnit.mpr
      ((Matrix.isUnit_iff_isUnit_det _).mpr (isUnit_iff_ne_zero.mpr hdet))
  obtain ⟨y,hy⟩ := hsurj w
  refine ⟨(columnInsertion f) *ᵥ y,?_,?_⟩
  · change A *ᵥ ((columnInsertion f)*ᵥy)=w
    rw [Matrix.mulVec_mulVec, mul_columnInsertion]
    exact hy
  · change B *ᵥ ((columnInsertion f)*ᵥy)=0
    rw [Matrix.mulVec_mulVec, mul_columnInsertion,hzero,Matrix.zero_mulVec]

end Matrices
end Zeta3.Construction.Features

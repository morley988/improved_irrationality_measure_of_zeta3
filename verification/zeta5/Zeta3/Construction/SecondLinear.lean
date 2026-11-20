import Zeta3.Construction.SecondDimensions
import Mathlib.LinearAlgebra.Dual.Lemmas

/-! Finite-dimensional rank inequalities for restricting the two sides of
an actual bilinear form. -/
noncomputable section
namespace Zeta3.Construction.Features
open Module
variable {K V W U : Type*} [Field K] [AddCommGroup V] [Module K V]
  [AddCommGroup W] [Module K W] [AddCommGroup U] [Module K U]
  [FiniteDimensional K V] [FiniteDimensional K W] [FiniteDimensional K U]

theorem linear_rank_domRestrict_bound (f : V →ₗ[K] W) (S : Submodule K V) :
    finrank K f.range ≤ finrank K (f.domRestrict S).range+finrank K (V ⧸ S) := by
  let i : (f.domRestrict S).ker →ₗ[K] f.ker :=
    { toFun x := ⟨x.val.val,x.property⟩
      map_add' _ _ := rfl
      map_smul' _ _ := rfl }
  have hi : Function.Injective i := by
    intro x y h
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg (fun z : f.ker => z.val) h
  have hk := LinearMap.finrank_le_finrank_of_injective hi
  have h₁ := f.finrank_range_add_finrank_ker
  have h₂ := (f.domRestrict S).finrank_range_add_finrank_ker
  have h₃ := S.finrank_quotient_add_finrank
  omega

theorem linear_rank_comp_loss (f : V →ₗ[K] W) (g : W →ₗ[K] U) :
    finrank K f.range ≤ finrank K (g.comp f).range+finrank K g.ker := by
  have h := (g.domRestrict f.range).finrank_range_add_finrank_ker
  have hr : (g.domRestrict f.range).range=(g.comp f).range := by
    rw [LinearMap.range_domRestrict,LinearMap.range_comp]
  rw [hr] at h
  let i : (g.domRestrict f.range).ker →ₗ[K] g.ker :=
    { toFun x := ⟨x.val.val,x.property⟩
      map_add' _ _ := rfl
      map_smul' _ _ := rfl }
  have hi : Function.Injective i := by
    intro x y h
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg (fun z : g.ker => z.val) h
  have hk := LinearMap.finrank_le_finrank_of_injective hi
  omega

theorem linear_rank_comp_le_left (f : V →ₗ[K] W) (g : W →ₗ[K] U) :
    finrank K (g.comp f).range≤finrank K g.range := by
  apply Submodule.finrank_mono
  rw [LinearMap.range_comp]
  exact LinearMap.map_le_range

theorem linear_rank_comp_le_right (f : V →ₗ[K] W) (g : W →ₗ[K] U) :
    finrank K (g.comp f).range≤finrank K f.range := by
  rw [LinearMap.range_comp]
  exact Submodule.finrank_map_le _ _

theorem linear_rank_add_le (f g : V →ₗ[K] W) :
    finrank K (f+g).range≤finrank K f.range+finrank K g.range := by
  apply le_trans (Submodule.finrank_mono (show (f+g).range≤f.range⊔g.range from by
    rintro y ⟨x,rfl⟩
    exact Submodule.mem_sup.mpr ⟨f x,⟨x,rfl⟩,g x,⟨x,rfl⟩,rfl⟩))
  have h := Submodule.finrank_sup_add_finrank_inf_eq f.range g.range
  omega

theorem linear_rank_sum_le {ι : Type*} (s : Finset ι) (f : ι→V →ₗ[K] W) :
    finrank K (∑ i∈s,f i).range≤∑ i∈s,finrank K (f i).range := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    rw [Finset.sum_empty,Finset.sum_empty]
    change finrank K (LinearMap.range (0 : V →ₗ[K] W))≤0
    rw [LinearMap.range_zero,finrank_bot]
  | @insert i s hi ih =>
    rw [Finset.sum_insert hi,Finset.sum_insert hi]
    exact (linear_rank_add_le _ _).trans (Nat.add_le_add_left ih _)

theorem bilinear_rank_restrict_loss (B : V →ₗ[K] Module.Dual K W)
    (S : Submodule K V) (T : Submodule K W) :
    finrank K B.range ≤
      finrank K (T.dualRestrict.comp (B.domRestrict S)).range+
        finrank K (V ⧸ S)+finrank K (W ⧸ T) := by
  have h₁ := linear_rank_domRestrict_bound B S
  have h₂ := linear_rank_comp_loss (B.domRestrict S) T.dualRestrict
  have h₃ := Subspace.finrank_add_finrank_dualAnnihilator_eq T
  have h₄ := T.finrank_quotient_add_finrank
  rw [Submodule.dualRestrict_ker_eq_dualAnnihilator] at h₂
  omega

end Zeta3.Construction.Features

import Zeta3.Construction.FeatureComplete

/-! The remaining top directions of the actual first restriction kernel. -/

noncomputable section
namespace Zeta3.Construction.Features
open Polynomial Finset Matrix Module Zeta5.Arithmetic OddZeta.FourValue

theorem columnInsertion_transpose_mul {K α β : Type*} [Field K]
    [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β]
    (f : α→β) (hf : Function.Injective f) :
    (columnInsertion (K:=K) f).transpose * columnInsertion (K:=K) f=(1 : Matrix α α K) := by
  ext a b
  simp [columnInsertion,Matrix.mul_apply,Matrix.one_apply,hf.eq_iff,eq_comm]

variable {p : ℕ} [Fact p.Prime]

def topWindowProjection (m r p : ℕ) [Fact p.Prime] (hmJ : m≤featureStart m r p) :
    Matrix (Fin (featureTopCount m r p)) (Fin r) (PadicResidueField p) :=
  (columnInsertion (topWindowColumn m r p hmJ)).transpose

theorem topRestrictionMatrix_factor (s : Finset ℕ) (m r : ℕ) (hp2 : p≠2)
    (hsmall : 2*(m+r)-2<p^2) (hmJ : m≤featureStart m r p) :
    topRestrictionMatrix s m r hp2 hsmall =
      topFeatureMatrix s m r hp2 hsmall * topWindowProjection m r p hmJ := by
  have he := columnInsertion_mul_submatrix (topRestrictionMatrix s m r hp2 hsmall)
    (topWindowColumn m r p hmJ) (topWindowColumn_injective m r p hmJ)
    (topRestrictionMatrix_zero_outside s m r hp2 hsmall hmJ)
  rw [topRestrictionMatrix_submatrix] at he
  exact he.symm

theorem topWindowProjection_low_zero (s : Finset ℕ) (m r p : ℕ)
    [Fact p.Prime] (hmr : 0<m+r) (hmJ : m≤featureStart m r p) :
    (topWindowProjection m r p hmJ).submatrix id (lowWindowColumn s m r p hmr)=0 := by
  ext h a
  dsimp only [Matrix.submatrix_apply,id_eq,topWindowProjection,Matrix.transpose_apply,columnInsertion]
  split_ifs with he
  · have he' := congrArg Fin.val he
    have hlo := featureNodeNumber_bounds a
    dsimp only [lowWindowColumn,topWindowColumn] at he'
    omega
  · rfl

theorem low_feature_interpolation_with_top_zero (s : Finset ℕ) (m r : ℕ) (hp2 : p≠2)
    (hsmall : 2*(m+r)-2<p^2) (hmr : 0<m+r) (hmJ : m≤featureStart m r p)
    (hs : ∀ c∈s,0<c ∧ 2*c<p) :
    ∀ w, ∃ x, (sampleRestrictionMatrix s m r hp2 hsmall).mulVecLin x=w ∧
      (topRestrictionMatrix s m r hp2 hsmall).mulVecLin x=0 ∧
      (topWindowProjection m r p hmJ).mulVecLin x=0 := by
  let B : Matrix (s ⊕ Fin (featureTopCount m r p)) (Fin r) (PadicResidueField p) :=
    Sum.elim (topRestrictionMatrix s m r hp2 hsmall) (topWindowProjection m r p hmJ)
  have hB : B.submatrix id (lowWindowColumn s m r p hmr)=0 := by
    ext row a
    cases row with
    | inl c => exact congrFun (congrFun (topRestrictionMatrix_low_zero s m r hp2 hsmall hmr) c) a
    | inr h => exact congrFun (congrFun (topWindowProjection_low_zero s m r p hmr hmJ) h) a
  intro w
  obtain ⟨x,hx,hB0⟩ := low_interpolation_from_minor
    (sampleRestrictionMatrix s m r hp2 hsmall) B (lowWindowColumn s m r p hmr)
    (sampleRestrictionMatrix_minor_det_ne_zero s m r hp2 hsmall hmr hs) hB w
  refine ⟨x,hx,?_,?_⟩
  · funext c
    exact congrFun hB0 (Sum.inl c)
  · funext h
    exact congrFun hB0 (Sum.inr h)

theorem restriction_kernel_top_iff (N m r : ℕ) (hp2 : p≠2)
    (hsmall : 2*(m+r)-2<p^2) (hm : 0<m) (hmJ : m≤featureStart m r p)
    (y : Fin (featureTopCount m r p)→PadicResidueField p) :
    (∃ x, (reducedRestrictionMatrix N m r hp2 hsmall).mulVecLin x=0 ∧
      (topWindowProjection m r p hmJ).mulVecLin x=y) ↔
      (topFeatureMatrix (maximalReflectedClasses N p) m r hp2 hsmall).mulVecLin y=0 := by
  let s := maximalReflectedClasses N p
  let A := sampleRestrictionMatrix s m r hp2 hsmall
  let B := topRestrictionMatrix s m r hp2 hsmall
  let T := topFeatureMatrix s m r hp2 hsmall
  let Q := topWindowProjection m r p hmJ
  have hBT : B=T*Q := topRestrictionMatrix_factor s m r hp2 hsmall hmJ
  have hker (x : Fin r→PadicResidueField p) :
      (reducedRestrictionMatrix N m r hp2 hsmall).mulVecLin x=0 ↔
        A.mulVecLin x=0 ∧ B.mulVecLin x=0 := by
    change x∈(reducedRestrictionMatrix N m r hp2 hsmall).mulVecLin.ker ↔ _
    rw [restriction_kernel_eq_pair]
    change (A.mulVecLin x,B.mulVecLin x)=0 ↔ _
    exact Prod.mk_eq_zero
  constructor
  · rintro ⟨x,hx,hQx⟩
    have hBx := (hker x).mp hx |>.2
    change B *ᵥ x=0 at hBx
    rw [hBT,← Matrix.mulVec_mulVec] at hBx
    change T *ᵥ (Q.mulVecLin x)=0 at hBx
    rw [hQx] at hBx
    exact hBx
  · intro hTy
    let I := columnInsertion (K:=PadicResidueField p) (topWindowColumn m r p hmJ)
    let x₀ := I *ᵥ y
    have hQx₀ : Q.mulVecLin x₀=y := by
      change I.transpose *ᵥ (I *ᵥ y)=y
      rw [Matrix.mulVec_mulVec,columnInsertion_transpose_mul _ (topWindowColumn_injective m r p hmJ),
        Matrix.one_mulVec]
    have hBx₀ : B.mulVecLin x₀=0 := by
      change B *ᵥ x₀=0
      rw [hBT,← Matrix.mulVec_mulVec]
      change T *ᵥ (Q.mulVecLin x₀)=0
      rw [hQx₀]
      exact hTy
    have hs : ∀ c∈s,0<c ∧ 2*c<p := fun _ hc => maximalReflectedClasses_half N p hc
    obtain ⟨z,hAz,hBz,hQz⟩ := low_feature_interpolation_with_top_zero s m r hp2 hsmall
      (by omega) hmJ hs (-A.mulVecLin x₀)
    refine ⟨x₀+z,(hker _).mpr ⟨?_,?_⟩,?_⟩
    · rw [map_add,hAz,add_neg_cancel]
    · rw [map_add,hBx₀,hBz,add_zero]
    · rw [map_add,hQx₀,hQz,add_zero]

def firstKernelTopMap (N m r : ℕ) (hp2 : p≠2) (hsmall : 2*(m+r)-2<p^2)
    (hmJ : m≤featureStart m r p) :
    (reducedRestrictionMatrix N m r hp2 hsmall).mulVecLin.ker →ₗ[PadicResidueField p]
      (Fin (featureTopCount m r p)→PadicResidueField p) :=
  (topWindowProjection m r p hmJ).mulVecLin.domRestrict
    (reducedRestrictionMatrix N m r hp2 hsmall).mulVecLin.ker

theorem firstKernelTopMap_range (N m r : ℕ) (hp2 : p≠2)
    (hsmall : 2*(m+r)-2<p^2) (hm : 0<m) (hmJ : m≤featureStart m r p) :
    (firstKernelTopMap N m r hp2 hsmall hmJ).range =
      (topFeatureMatrix (maximalReflectedClasses N p) m r hp2 hsmall).mulVecLin.ker := by
  ext y
  constructor
  · rintro ⟨x,hx⟩
    exact (restriction_kernel_top_iff N m r hp2 hsmall hm hmJ y).mp ⟨x.val,x.property,hx⟩
  · intro hy
    obtain ⟨x,hx,hQx⟩ := (restriction_kernel_top_iff N m r hp2 hsmall hm hmJ y).mpr hy
    exact ⟨⟨x,hx⟩,hQx⟩

/-- The number `K=(H-w)_+` is the actual dimension of top coefficient
directions in the first restriction kernel. -/
theorem firstKernelTopMap_finrank (N m r : ℕ) (hp2 : p≠2)
    (hsmall : 2*(m+r)-2<p^2) (hm : 0<m) (hmJ : m≤featureStart m r p) :
    finrank (PadicResidueField p) (firstKernelTopMap N m r hp2 hsmall hmJ).range =
      featureTopKernel N m r p := by
  rw [firstKernelTopMap_range N m r hp2 hsmall hm hmJ]
  have h := (topFeatureMatrix (maximalReflectedClasses N p) m r hp2 hsmall).mulVecLin.finrank_range_add_finrank_ker
  rw [Module.finrank_pi,Fintype.card_fin] at h
  change (topFeatureMatrix (maximalReflectedClasses N p) m r hp2 hsmall).rank+_=featureTopCount m r p at h
  rw [topFeatureMatrix_rank _ m r hp2 hsmall hm hmJ
    (fun _ hc => maximalReflectedClasses_half N p hc)] at h
  unfold featureTopKernel
  omega

end Zeta3.Construction.Features

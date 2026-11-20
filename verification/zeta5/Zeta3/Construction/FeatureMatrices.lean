import Zeta3.Construction.FeatureNodes

/-! Actual low evaluations and top coefficients of the finite restriction. -/

noncomputable section
namespace Zeta3.Construction.Features
open Polynomial Finset Matrix Zeta5.Construction Zeta5.Arithmetic OddZeta.FourValue
variable {p : ℕ} [Fact p.Prime]

theorem window_index_small (m r : ℕ) (hsmall : 2*(m+r)-2<p^2) (i:Fin r) :
    2*(m+i.val)<p^2 := by have := i.isLt; omega

def topRestrictionMatrix (s : Finset ℕ) (m r : ℕ) (hp2 : p≠2)
    (hsmall : 2*(m+r)-2<p^2) : Matrix s (Fin r) (PadicResidueField p) :=
  fun c i => (reducedCentralLocal hp2 (m+i.val) (window_index_small m r hsmall i) (c:ℕ)).coeff
    (restrictionDepth m r p)

def topWindowColumn (m r p : ℕ) (hmJ : m≤featureStart m r p)
    (h : Fin (featureTopCount m r p)) : Fin r :=
  ⟨featureStart m r p-m+h.val, by
    have hh := h.isLt
    unfold featureTopCount at hh
    omega⟩

theorem topWindowColumn_injective (m r p : ℕ) (hmJ : m≤featureStart m r p) :
    Function.Injective (topWindowColumn m r p hmJ) := by
  intro i j h
  apply Fin.ext
  have := congrArg Fin.val h
  simpa only [topWindowColumn,Fin.val_mk,Nat.add_left_cancel_iff] using this

theorem topRestrictionMatrix_submatrix (s : Finset ℕ) (m r : ℕ) (hp2 : p≠2)
    (hsmall : 2*(m+r)-2<p^2) (hmJ : m≤featureStart m r p) :
    (topRestrictionMatrix s m r hp2 hsmall).submatrix id (topWindowColumn m r p hmJ) =
      topFeatureMatrix s m r hp2 hsmall := by
  ext c h
  dsimp only [Matrix.submatrix_apply, id_eq, topRestrictionMatrix, topWindowColumn,topFeatureMatrix]
  have he : m+(featureStart m r p-m+h.val)=featureStart m r p+h.val := by omega
  simp only [he]

theorem topRestrictionMatrix_zero_outside (s : Finset ℕ) (m r : ℕ) (hp2 : p≠2)
    (hsmall : 2*(m+r)-2<p^2) (hmJ : m≤featureStart m r p) :
    ∀ i, i∉Set.range (topWindowColumn m r p hmJ) → ∀ c,
      topRestrictionMatrix s m r hp2 hsmall c i=0 := by
  intro i hi c
  have hlo : m+i.val<featureStart m r p := by
    by_contra! hhi
    have hh : m+i.val-featureStart m r p<featureTopCount m r p := by
      have := i.isLt
      unfold featureTopCount
      omega
    apply hi
    refine ⟨⟨m+i.val-featureStart m r p,hh⟩,?_⟩
    apply Fin.ext
    dsimp [topWindowColumn]
    omega
  exact reducedCentralLocal_coeff_zero hp2 (m+i.val) (restrictionDepth m r p)
    (window_index_small m r hsmall i)
    (feature_low_depth m r p (m+i.val) (Fact.out:p.Prime).pos hlo) c

theorem topRestrictionMatrix_rank (s : Finset ℕ) (m r : ℕ) (hp2 : p≠2)
    (hsmall : 2*(m+r)-2<p^2) (hm : 0<m) (hmJ : m≤featureStart m r p)
    (hs : ∀ c∈s,0<c ∧ 2*c<p) :
    (topRestrictionMatrix s m r hp2 hsmall).rank=min (featureTopCount m r p) s.card := by
  have hr := rank_submatrix_of_zero_outside (topRestrictionMatrix s m r hp2 hsmall)
    (topWindowColumn m r p hmJ) (topWindowColumn_injective m r p hmJ)
    (topRestrictionMatrix_zero_outside s m r hp2 hsmall hmJ)
  rw [topRestrictionMatrix_submatrix] at hr
  rw [← hr]
  exact topFeatureMatrix_rank s m r hp2 hsmall hm hmJ hs

def sampleRestrictionMatrix (s : Finset ℕ) (m r : ℕ) (hp2 : p≠2)
    (hsmall : 2*(m+r)-2<p^2) :
    Matrix (FreeFeatureIndex s (featureStart m r p) m p) (Fin r) (PadicResidueField p) :=
  fun a i => (reducedCentralLocal hp2 (m+i.val) (window_index_small m r hsmall i) (a.1:ℕ)).eval
    (physicalLocalLevel p (a.1:ℕ) a.2.val : PadicResidueField p)

def lowWindowColumn (s : Finset ℕ) (m r p : ℕ) (hmr : 0<m+r)
    (a : FreeFeatureIndex s (featureStart m r p) m p) : Fin r :=
  ⟨featureNodeNumber a-m, by
    have hb := featureNodeNumber_bounds a
    have hJ := featureStart_le m r p hmr
    omega⟩

theorem lowWindowColumn_index (s : Finset ℕ) (m r p : ℕ) (hmr : 0<m+r)
    (a : FreeFeatureIndex s (featureStart m r p) m p) :
    m+(lowWindowColumn s m r p hmr a).val=featureNodeNumber a := by
  have hb := featureNodeNumber_bounds a
  dsimp [lowWindowColumn]
  omega

theorem sampleRestrictionMatrix_minor_det_ne_zero (s : Finset ℕ) (m r : ℕ) (hp2 : p≠2)
    (hsmall : 2*(m+r)-2<p^2) (hmr : 0<m+r) (hs : ∀ c∈s,0<c ∧ 2*c<p) :
    ((sampleRestrictionMatrix s m r hp2 hsmall).submatrix id (lowWindowColumn s m r p hmr)).det≠0 := by
  classical
  let α := FreeFeatureIndex s (featureStart m r p) m p
  letI : LinearOrder α := LinearOrder.lift' featureNodeNumber
    (featureNodeNumber_injective s (featureStart m r p) m p hs)
  let A := (sampleRestrictionMatrix s m r hp2 hsmall).submatrix id (lowWindowColumn s m r p hmr)
  have hA (a b : α) : A a b =
      (reducedCentralLocal hp2 (featureNodeNumber b)
        (by have h:=window_index_small m r hsmall (lowWindowColumn s m r p hmr b)
            rwa [lowWindowColumn_index] at h)
        (a.1:ℕ)).eval (physicalLocalLevel p (a.1:ℕ) a.2.val : PadicResidueField p) := by
    dsimp only [A,Matrix.submatrix_apply,id_eq,sampleRestrictionMatrix]
    simp only [lowWindowColumn_index]
  have ht : A.IsLowerTriangular := by
    intro a b hab
    rw [hA]
    apply reducedCentralLocal_eval_level_zero
    · exact (Finset.mem_filter.mp a.2.property).1
    · exact hab
  rw [Matrix.det_of_isLowerTriangular A ht]
  apply Finset.prod_ne_zero_iff.mpr
  intro a ha
  rw [hA]
  exact reducedCentralLocal_eval_level_self_ne_zero hp2 (featureStart m r p) (a.1:ℕ) a.2.val
    (Finset.mem_filter.mp a.2.property).1 _

theorem topRestrictionMatrix_low_zero (s : Finset ℕ) (m r : ℕ) (hp2 : p≠2)
    (hsmall : 2*(m+r)-2<p^2) (hmr : 0<m+r) :
    (topRestrictionMatrix s m r hp2 hsmall).submatrix id (lowWindowColumn s m r p hmr)=0 := by
  ext c a
  dsimp only [Matrix.submatrix_apply,id_eq,topRestrictionMatrix]
  simp only [lowWindowColumn_index]
  exact reducedCentralLocal_coeff_zero hp2 (featureNodeNumber a) (restrictionDepth m r p) _
    (feature_low_depth m r p _ (Fact.out:p.Prime).pos (featureNodeNumber_bounds a).2) c

theorem low_feature_interpolation (s : Finset ℕ) (m r : ℕ) (hp2 : p≠2)
    (hsmall : 2*(m+r)-2<p^2) (hmr : 0<m+r) (hs : ∀ c∈s,0<c ∧ 2*c<p) :
    ∀ w, ∃ x, (sampleRestrictionMatrix s m r hp2 hsmall).mulVecLin x=w ∧
      (topRestrictionMatrix s m r hp2 hsmall).mulVecLin x=0 :=
  low_interpolation_from_minor _ _ (lowWindowColumn s m r p hmr)
    (sampleRestrictionMatrix_minor_det_ne_zero s m r hp2 hsmall hmr hs)
    (topRestrictionMatrix_low_zero s m r hp2 hsmall hmr)

end Zeta3.Construction.Features

import Zeta3.Construction.FeatureMatrices

/-! Exact full rank of the actual maximal restriction matrix. The low
features are obtained by triangular interpolation at the actual integer
nodes; the top features are the proved central recurrence Vandermonde. -/

noncomputable section
namespace Zeta3.Construction.Features
open Polynomial Finset Matrix Module Zeta5.Construction Zeta5.Arithmetic OddZeta.FourValue
variable {p : ℕ} [Fact p.Prime]

theorem maximalReflectedClasses_half (N p : ℕ) {c : ℕ}
    (hc : c∈maximalReflectedClasses N p) : 0<c ∧ 2*c<p := by
  obtain ⟨hc,_⟩ := Finset.mem_filter.mp hc
  obtain ⟨hlo,hhi⟩ := Finset.mem_Icc.mp hc
  omega

theorem complete_local_count (m r c : ℕ) (hp2 : p≠2) (hc : 0<c) (hcp : 2*c<p) :
    (localFeatureNodes (featureStart m r p) p c).card = restrictionDepth m r p := by
  change physicalLocalMultiplicity (featureStart m r p-1) p c = _
  rw [physicalLocalMultiplicity_eq_reflectedSize _ p c hc hcp]
  exact reflectedSize_halfBoundary (restrictionDepth m r p) p c
    ((Fact.out:p.Prime).mod_two_eq_one_iff_ne_two.mpr hp2) hc hcp

theorem freeFeatureIndex_card (s : Finset ℕ) (m r : ℕ) (hp2 : p≠2)
    (hmJ : m≤featureStart m r p) (hs : ∀ c∈s,0<c ∧ 2*c<p) :
    Fintype.card (FreeFeatureIndex s (featureStart m r p) m p) =
      ∑ c∈s, (restrictionDepth m r p-physicalLocalMultiplicity (m-1) p c) := by
  rw [Fintype.card_sigma]
  simp only [Fintype.card_coe]
  rw [Finset.sum_coe_sort s (fun c : ℕ => (freeLocalFeatureNodes (featureStart m r p) m p (c:ℤ)).card)]
  apply Finset.sum_congr rfl
  intro c hc
  rw [freeLocalFeatureNodes_card _ _ _ hmJ]
  have hk := complete_local_count m r c hp2 (hs c hc).1 (hs c hc).2
  change physicalLocalMultiplicity (featureStart m r p-1) p c=restrictionDepth m r p at hk
  rw [hk]

def residueWindowLocal (m r : ℕ) (hp2 : p≠2) (hsmall : 2*(m+r)-2<p^2)
    (x : Fin r→PadicResidueField p) (c : ℤ) : (PadicResidueField p)[X] :=
  ∑ i:Fin r, C (x i)*reducedCentralLocal hp2 (m+i.val) (window_index_small m r hsmall i) c

theorem residueWindowLocal_natDegree_le (m r : ℕ) (hp2 : p≠2)
    (hsmall : 2*(m+r)-2<p^2) (x : Fin r→PadicResidueField p) (c : ℤ) :
    (residueWindowLocal m r hp2 hsmall x c).natDegree≤restrictionDepth m r p := by
  apply natDegree_sum_le_of_forall_le
  intro i hi
  apply (natDegree_C_mul_le _ _).trans
  apply (reducedCentralLocal_natDegree_le hp2 (m+i.val) (window_index_small m r hsmall i) c).trans
  apply Nat.div_le_div_right
  have := i.isLt
  omega

theorem residueWindowLocal_coeff (N m r : ℕ) (hp2 : p≠2)
    (hsmall : 2*(m+r)-2<p^2) (x : Fin r→PadicResidueField p)
    (a : WindowRestrictionIndex N m r p) :
    (residueWindowLocal m r hp2 hsmall x a.1.val).coeff a.2.val =
      (reducedRestrictionMatrix N m r hp2 hsmall).mulVecLin x a := by
  simp only [residueWindowLocal,finsetSum_coeff,coeff_C_mul,Matrix.mulVecLin_apply,
    Matrix.mulVec, dotProduct,reducedRestrictionMatrix_eq_local]
  apply Finset.sum_congr rfl
  intro i hi
  ring

theorem residueWindowLocal_sample (s : Finset ℕ) (m r : ℕ) (hp2 : p≠2)
    (hsmall : 2*(m+r)-2<p^2) (x : Fin r→PadicResidueField p)
    (a : FreeFeatureIndex s (featureStart m r p) m p) :
    (residueWindowLocal m r hp2 hsmall x (a.1:ℕ)).eval
        (physicalLocalLevel p (a.1:ℕ) a.2.val : PadicResidueField p) =
      (sampleRestrictionMatrix s m r hp2 hsmall).mulVecLin x a := by
  simp only [residueWindowLocal,eval_finsetSum,eval_mul,eval_C,Matrix.mulVecLin_apply,
    Matrix.mulVec,dotProduct,sampleRestrictionMatrix]
  apply Finset.sum_congr rfl
  intro i hi
  ring

theorem residueWindowLocal_top (s : Finset ℕ) (m r : ℕ) (hp2 : p≠2)
    (hsmall : 2*(m+r)-2<p^2) (x : Fin r→PadicResidueField p) (c:s) :
    (residueWindowLocal m r hp2 hsmall x (c:ℕ)).coeff (restrictionDepth m r p) =
      (topRestrictionMatrix s m r hp2 hsmall).mulVecLin x c := by
  simp only [residueWindowLocal,finsetSum_coeff,coeff_C_mul,Matrix.mulVecLin_apply,
    Matrix.mulVec,dotProduct,topRestrictionMatrix]
  apply Finset.sum_congr rfl
  intro i hi
  ring

theorem residueWindowLocal_old_root (m r : ℕ) (hp2 : p≠2)
    (hsmall : 2*(m+r)-2<p^2) (x : Fin r→PadicResidueField p) (c : ℤ)
    (i : Fin (featureStart m r p-1)×Bool)
    (hi : i∈localFeatureNodes (featureStart m r p) p c) (hnum : i.1.val+1<m) :
    (residueWindowLocal m r hp2 hsmall x c).eval
      (physicalLocalLevel p c i : PadicResidueField p)=0 := by
  rw [residueWindowLocal,eval_finsetSum]
  apply Finset.sum_eq_zero
  intro j hj
  rw [eval_mul,eval_C,reducedCentralLocal_eval_level_zero hp2 (m+j.val)
    (featureStart m r p) (window_index_small m r hsmall j) c i hi (by omega),mul_zero]

theorem restriction_kernel_iff_local_zero (N m r : ℕ) (hp2 : p≠2)
    (hsmall : 2*(m+r)-2<p^2) (x : Fin r→PadicResidueField p) :
    (reducedRestrictionMatrix N m r hp2 hsmall).mulVecLin x=0 ↔
      ∀ c : maximalReflectedClasses N p, residueWindowLocal m r hp2 hsmall x c.val=0 := by
  constructor
  · intro hx c
    ext k
    by_cases hk : k≤restrictionDepth m r p
    · have he := congrFun hx (c,⟨k,by omega⟩)
      rw [← residueWindowLocal_coeff] at he
      exact he
    · exact coeff_eq_zero_of_natDegree_lt
        (lt_of_le_of_lt (residueWindowLocal_natDegree_le m r hp2 hsmall x c.val) (by omega))
  · intro hx
    funext a
    rw [← residueWindowLocal_coeff,hx a.1]
    rfl

theorem restriction_kernel_eq_pair (N m r : ℕ) (hp2 : p≠2)
    (hsmall : 2*(m+r)-2<p^2) :
    (reducedRestrictionMatrix N m r hp2 hsmall).mulVecLin.ker =
      ((sampleRestrictionMatrix (maximalReflectedClasses N p) m r hp2 hsmall).mulVecLin.prod
        (topRestrictionMatrix (maximalReflectedClasses N p) m r hp2 hsmall).mulVecLin).ker := by
  ext x
  simp only [LinearMap.mem_ker,LinearMap.prod_apply]
  change ((reducedRestrictionMatrix N m r hp2 hsmall).mulVecLin x=0) ↔
    ((sampleRestrictionMatrix (maximalReflectedClasses N p) m r hp2 hsmall).mulVecLin x,
      (topRestrictionMatrix (maximalReflectedClasses N p) m r hp2 hsmall).mulVecLin x)=0
  rw [Prod.mk_eq_zero]
  rw [restriction_kernel_iff_local_zero]
  constructor
  · intro hx
    constructor
    · funext a
      rw [← residueWindowLocal_sample,hx a.1]
      simp
    · funext c
      rw [← residueWindowLocal_top,hx c]
      simp
  · rintro ⟨hsample,htop⟩ c
    let P := residueWindowLocal m r hp2 hsmall x c.val
    have hdeg : P.natDegree≤restrictionDepth m r p := residueWindowLocal_natDegree_le m r hp2 hsmall x c.val
    have htop0 : P.coeff (restrictionDepth m r p)=0 := by
      rw [residueWindowLocal_top]
      exact congrFun htop c
    have hdeglt : P.degree < (restrictionDepth m r p : ℕ) := by
      rw [degree_lt_iff_coeff_zero]
      intro k hk
      by_cases hkD : k=restrictionDepth m r p
      · simpa only [hkD] using htop0
      · exact coeff_eq_zero_of_natDegree_lt (by omega)
    have hc := maximalReflectedClasses_half N p c.property
    have hcount := complete_local_count m r c.val hp2 hc.1 hc.2
    have hsmallJ : 2*(featureStart m r p-1)<p^2 := by
      have hJ := featureStart_twice_upper m r p
      have hmul := Nat.div_mul_le_self (2*(m+r)-2) p
      unfold restrictionDepth at hJ
      omega
    apply Polynomial.eq_zero_of_degree_lt_of_eval_index_eq_zero
      (localFeatureNodes (featureStart m r p) p c.val)
      (v:=fun i => (physicalLocalLevel p c.val i : PadicResidueField p))
    · intro i hi j hj hij
      have he := featureNodeLevel_injective (featureStart m r p) c.val hsmallJ
        (a₁:=⟨i,hi⟩) (a₂:=⟨j,hj⟩) hij
      exact congrArg Subtype.val he
    · simpa only [hcount] using hdeglt
    · intro i hi
      by_cases hlow : i.1.val+1<m
      · exact residueWindowLocal_old_root m r hp2 hsmall x c.val i hi hlow
      · let a : FreeFeatureIndex (maximalReflectedClasses N p) (featureStart m r p) m p :=
          ⟨c,⟨i,Finset.mem_filter.mpr ⟨hi,by omega⟩⟩⟩
        have he := congrFun hsample a
        rw [← residueWindowLocal_sample] at he
        exact he

/-- The manuscript's exact complete-feature rank, for the actual reduced
`centralRestrictionMatrix` inherited from the first arithmetic layer. -/
theorem reducedRestrictionMatrix_rank (N m r : ℕ) (hp2 : p≠2)
    (hsmall : 2*(m+r)-2<p^2) (hm : 0<m) (hmJ : m≤featureStart m r p) :
    (reducedRestrictionMatrix N m r hp2 hsmall).rank=featureRankBound N m r p := by
  let s := maximalReflectedClasses N p
  have hs : ∀ c∈s,0<c ∧ 2*c<p := fun _ hc => maximalReflectedClasses_half N p hc
  have he := finrank_range_eq_of_ker_eq
    (reducedRestrictionMatrix N m r hp2 hsmall).mulVecLin
    ((sampleRestrictionMatrix s m r hp2 hsmall).mulVecLin.prod
      (topRestrictionMatrix s m r hp2 hsmall).mulVecLin)
    (restriction_kernel_eq_pair N m r hp2 hsmall)
  rw [pair_range_finrank _ _ (low_feature_interpolation s m r hp2 hsmall (by omega) hs),
    Module.finrank_pi,freeFeatureIndex_card s m r hp2 hmJ hs] at he
  change (reducedRestrictionMatrix N m r hp2 hsmall).rank =
    (∑ c∈s, (restrictionDepth m r p-physicalLocalMultiplicity (m-1) p c))+
      (topRestrictionMatrix s m r hp2 hsmall).rank at he
  rw [topRestrictionMatrix_rank s m r hp2 hsmall hm hmJ hs] at he
  exact he

end Zeta3.Construction.Features

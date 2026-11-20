import Zeta3.Construction.SecondBasis

/-! Keeping or deleting the top directions is a genuine subspace of the
actual first restriction kernel, with the exact codimension K. -/
noncomputable section
namespace Zeta3.Construction.Features
open Polynomial Finset Matrix Module Zeta5.Arithmetic OddZeta.FourValue
variable {p : ℕ} [Fact p.Prime]

abbrev FirstRestrictionKernel (N m r : ℕ) (hp2 : p≠2) (hsmall : 2*(m+r)-2<p^2) :=
  (reducedRestrictionMatrix N m r hp2 hsmall).mulVecLin.ker

def secondKernelFeatureSpace (N m r u : ℕ) (hp2 : p≠2) (hsmall : 2*(m+r)-2<p^2)
    (hmJ : m≤featureStart m r p) : Submodule (PadicResidueField p) (FirstRestrictionKernel N m r hp2 hsmall) :=
  if u=0 then (firstKernelTopMap N m r hp2 hsmall hmJ).ker else ⊤

theorem firstRestrictionKernel_finrank (N m r : ℕ) (hp2 : p≠2)
    (hsmall : 2*(m+r)-2<p^2) (hm : 0<m) (hmJ : m≤featureStart m r p) :
    finrank (PadicResidueField p) (FirstRestrictionKernel N m r hp2 hsmall)=
      r-featureRankBound N m r p := by
  have h := (reducedRestrictionMatrix N m r hp2 hsmall).mulVecLin.finrank_range_add_finrank_ker
  rw [Module.finrank_pi,Fintype.card_fin] at h
  change (reducedRestrictionMatrix N m r hp2 hsmall).rank+
    finrank (PadicResidueField p) (FirstRestrictionKernel N m r hp2 hsmall)=r at h
  rw [reducedRestrictionMatrix_rank N m r hp2 hsmall hm hmJ] at h
  omega

theorem secondKernelFeatureSpace_codimension (N m r u : ℕ) (hp2 : p≠2)
    (hsmall : 2*(m+r)-2<p^2) (hm : 0<m) (hmJ : m≤featureStart m r p) (hu : u≤1) :
    finrank (PadicResidueField p) ((FirstRestrictionKernel N m r hp2 hsmall) ⧸
      secondKernelFeatureSpace N m r u hp2 hsmall hmJ)=(1-u)*featureTopKernel N m r p := by
  by_cases hu0 : u=0
  · subst u
    rw [secondKernelFeatureSpace,if_pos rfl,Nat.sub_zero,one_mul,
      (firstKernelTopMap N m r hp2 hsmall hmJ).quotKerEquivRange.finrank_eq]
    exact firstKernelTopMap_finrank N m r hp2 hsmall hm hmJ
  · have hu1 : u=1 := by omega
    subst u
    have he : secondKernelFeatureSpace N m r 1 hp2 hsmall hmJ=⊤ := if_neg (by omega)
    rw [he,Nat.sub_self,zero_mul]
    exact Module.finrank_zero_of_subsingleton

def secondKernelFeatureInclusion (N m r u : ℕ) (hp2 : p≠2) (hsmall : 2*(m+r)-2<p^2)
    (hmJ : m≤featureStart m r p) :
    secondKernelFeatureSpace N m r u hp2 hsmall hmJ →ₗ[PadicResidueField p] (Fin r→PadicResidueField p) :=
  (FirstRestrictionKernel N m r hp2 hsmall).subtype.comp
    (secondKernelFeatureSpace N m r u hp2 hsmall hmJ).subtype

theorem secondKernelFeatureSpace_degree (N m r c u : ℕ) (hp2 : p≠2)
    (hsmall : 2*(m+r)-2<p^2) (hmJ : m≤featureStart m r p) (hu : u≤1)
    (x : secondKernelFeatureSpace N m r u hp2 hsmall hmJ) :
    (residueWindowLocal m r hp2 hsmall (secondKernelFeatureInclusion N m r u hp2 hsmall hmJ x) c).degree<
      (restrictionDepth m r p+u:ℕ) := by
  by_cases hu0 : u=0
  · subst u
    rw [Nat.add_zero]
    apply residueWindowLocal_degree_lt_of_top_zero m r c hp2 hsmall hmJ
    exact x.property
  · have hu1 : u=1 := by omega
    subst u
    exact residueWindowLocal_degree_lt_succ m r hp2 hsmall _ c

def secondKernelFeatureCoordinates (N m r c u : ℕ) (hp2 : p≠2)
    (hsmall : 2*(m+r)-2<p^2) (hmJ : m≤featureStart m r p) :
    secondKernelFeatureSpace N m r u hp2 hsmall hmJ →ₗ[PadicResidueField p]
      (Fin (secondLocalFeatureCount m r p c u)→PadicResidueField p) :=
  (localFeatureCoordinateMap m r c (secondLocalFeatureCount m r p c u) hp2 hsmall).comp
    (secondKernelFeatureInclusion N m r u hp2 hsmall hmJ)

theorem secondKernelFeature_expansion (N m r c u : ℕ) (hp2 : p≠2)
    (hsmall : 2*(m+r)-2<p^2) (hmJ : m≤featureStart m r p)
    (hc : 0<c) (hcp : 2*c<p) (hu : u≤1)
    (x : secondKernelFeatureSpace N m r u hp2 hsmall hmJ) :
    residueWindowLocal m r hp2 hsmall (secondKernelFeatureInclusion N m r u hp2 hsmall hmJ x) c=
      ∑ j:Fin (secondLocalFeatureCount m r p c u),
        C (secondKernelFeatureCoordinates N m r c u hp2 hsmall hmJ x j)*residueLocalBasis m c j.val :=
  residueWindowLocal_feature_expansion m r c u hp2 hsmall hmJ hc hcp _
    (secondKernelFeatureSpace_degree N m r c u hp2 hsmall hmJ hu x)

end Zeta3.Construction.Features

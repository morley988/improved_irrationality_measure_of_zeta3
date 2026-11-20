import Zeta3.Construction.SecondKernelFeatures

/-! The genuine local second form factors through the centered feature
matrix, so its dimension and parity caps apply to the actual windows. -/
noncomputable section
namespace Zeta3.Construction.Features
open Polynomial Finset Matrix Module Zeta5.Arithmetic Zeta3.Arithmetic OddZeta.FourValue
variable {p : ℕ} [Fact p.Prime]

def secondRestrictedLocalBilinear (N m₁ m₂ r c u₁ u₂ : ℕ) (hp : 2<p)
    (h₁ : 2*(m₁+r)-2<p^2) (h₂ : 2*(m₂+r)-2<p^2)
    (hN : 2*N<p^2) (hc : 0<c) (hcp : 2*c<p)
    (hD : restrictionDepth m₁ r p+restrictionDepth m₂ r p<p)
    (hmJ₁ : m₁≤featureStart m₁ r p) (hmJ₂ : m₂≤featureStart m₂ r p) :
    secondKernelFeatureSpace N m₁ r u₁ (by omega : p≠2) h₁ hmJ₁ →ₗ[PadicResidueField p]
      Module.Dual (PadicResidueField p)
        (secondKernelFeatureSpace N m₂ r u₂ (by omega : p≠2) h₂ hmJ₂) :=
  (residueLocalBilinear N m₁ m₂ r c hp h₁ h₂ hN hc hcp hD).compl₁₂
    (secondKernelFeatureInclusion N m₁ r u₁ (by omega) h₁ hmJ₁)
    (secondKernelFeatureInclusion N m₂ r u₂ (by omega) h₂ hmJ₂)

set_option maxHeartbeats 200000 in
theorem secondRestrictedLocalBilinear_rank_le
    (N m₁ m₂ r c u₁ u₂ : ℕ) (hp : 2<p)
    (h₁ : 2*(m₁+r)-2<p^2) (h₂ : 2*(m₂+r)-2<p^2)
    (hN : 2*N<p^2) (hc : 0<c) (hcp : 2*c<p)
    (hD : restrictionDepth m₁ r p+restrictionDepth m₂ r p<p)
    (hmJ₁ : m₁≤featureStart m₁ r p) (hmJ₂ : m₂≤featureStart m₂ r p)
    (hu₁ : u₁≤1) (hu₂ : u₂≤1) (hnot : c∉maximalReflectedClasses N p) :
    finrank (PadicResidueField p)
      (secondRestrictedLocalBilinear N m₁ m₂ r c u₁ u₂ hp h₁ h₂ hN hc hcp hD hmJ₁ hmJ₂).range≤
      secondLocalRankCap N m₁ m₂ r p c u₁ u₂ := by
  let A := secondKernelFeatureCoordinates N m₁ r c u₁ (by omega : p≠2) h₁ hmJ₁
  let Cc := secondKernelFeatureCoordinates N m₂ r c u₂ (by omega : p≠2) h₂ hmJ₂
  let M := secondLocalFeatureMatrix N m₁ m₂ r c u₁ u₂ hp hc hcp hN hD
  let B := secondRestrictedLocalBilinear N m₁ m₂ r c u₁ u₂ hp h₁ h₂ hN hc hcp hD hmJ₁ hmJ₂
  have hB : ∀ x y,B x y=∑ i:Fin (secondLocalFeatureCount m₁ r p c u₁),
      ∑ j:Fin (secondLocalFeatureCount m₂ r p c u₂),A x i*M i j*Cc y j := by
    intro x y
    let L := residuePhysicalFunctional N c (restrictionDepth m₁ r p+restrictionDepth m₂ r p)
      hp hc hcp hN (by omega)
    let P := residueWindowLocal m₁ r (by omega : p≠2) h₁
      (secondKernelFeatureInclusion N m₁ r u₁ (by omega) h₁ hmJ₁ x) c
    let Q := residueWindowLocal m₂ r (by omega : p≠2) h₂
      (secondKernelFeatureInclusion N m₂ r u₂ (by omega) h₂ hmJ₂ y) c
    have hP : P=∑ i:Fin (secondLocalFeatureCount m₁ r p c u₁),
        C (A x i)*residueLocalBasis m₁ c i.val :=
      secondKernelFeature_expansion N m₁ r c u₁ (by omega) h₁ hmJ₁ hc hcp hu₁ x
    have hQ : Q=∑ j:Fin (secondLocalFeatureCount m₂ r p c u₂),
        C (Cc y j)*residueLocalBasis m₂ c j.val :=
      secondKernelFeature_expansion N m₂ r c u₂ (by omega) h₂ hmJ₂ hc hcp hu₂ y
    change L (P*Q)=∑ i:Fin (secondLocalFeatureCount m₁ r p c u₁),
      ∑ j:Fin (secondLocalFeatureCount m₂ r p c u₂),A x i*M i j*Cc y j
    rw [hP,hQ]
    simp only [Finset.sum_mul,Finset.mul_sum,map_sum]
    rw [Finset.sum_comm]
    apply sum_congr rfl
    intro i hi
    apply sum_congr rfl
    intro j hj
    have he : (C (A x i)*residueLocalBasis (p:=p) m₁ c i.val)*
        (C (Cc y j)*residueLocalBasis (p:=p) m₂ c j.val)=
        C (A x i*Cc y j)*(residueLocalBasis m₁ c i.val*residueLocalBasis m₂ c j.val) := by
      rw [map_mul]
      ring
    rw [he,← smul_eq_C_mul,map_smul,smul_eq_mul]
    change (A x i*Cc y j)*L (residueLocalBasis m₁ c i.val*residueLocalBasis m₂ c j.val)=
      A x i*L (residueLocalBasis m₁ c i.val*residueLocalBasis m₂ c j.val)*Cc y j
    ring

  let f := M.transpose.mulVecLin.comp A
  have hker : f.ker≤B.ker := by
    intro x hx
    apply LinearMap.ext
    intro y
    change B x y=0
    rw [hB,Finset.sum_comm]
    apply Finset.sum_eq_zero
    intro j hj
    have hz : (∑ i:Fin (secondLocalFeatureCount m₁ r p c u₁),M i j*A x i)=0 := congrFun hx j
    calc
      (∑ i:Fin (secondLocalFeatureCount m₁ r p c u₁),A x i*M i j*Cc y j)=
        (∑ i:Fin (secondLocalFeatureCount m₁ r p c u₁),M i j*A x i)*Cc y j := by
          rw [Finset.sum_mul]
          apply Finset.sum_congr rfl
          intro i hi
          ring
      _ = 0 := by rw [hz,zero_mul]
  have hk := Submodule.finrank_mono hker
  have hBdim := LinearMap.finrank_range_add_finrank_ker
    (K := PadicResidueField p)
    (V := secondKernelFeatureSpace N m₁ r u₁ (by omega : p≠2) h₁ hmJ₁)
    (V₂ := Module.Dual (PadicResidueField p)
      (secondKernelFeatureSpace N m₂ r u₂ (by omega : p≠2) h₂ hmJ₂)) B
  have hfdim := LinearMap.finrank_range_add_finrank_ker
    (K := PadicResidueField p)
    (V := secondKernelFeatureSpace N m₁ r u₁ (by omega : p≠2) h₁ hmJ₁)
    (V₂ := Fin (secondLocalFeatureCount m₂ r p c u₂)→PadicResidueField p) f
  have hr : finrank (PadicResidueField p) B.range≤finrank (PadicResidueField p) f.range := by
    omega
  have hcomp : f.range≤M.transpose.mulVecLin.range := by
    rintro z ⟨x,rfl⟩
    exact ⟨A x,rfl⟩
  have hg := Submodule.finrank_mono hcomp
  change finrank (PadicResidueField p) f.range≤M.transpose.rank at hg
  rw [Matrix.rank_transpose] at hg
  exact hr.trans (hg.trans (secondLocalFeatureMatrix_rank_le
    N m₁ m₂ r c u₁ u₂ hp hc hcp hN hD hu₁ hu₂ hnot))

end Zeta3.Construction.Features

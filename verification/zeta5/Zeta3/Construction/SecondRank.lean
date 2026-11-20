import Zeta3.Construction.SecondLocalRank

/-! The actual second residue form has the minimum of the two kernel
sizes and all four top-feature/parity rank bounds. -/
noncomputable section
set_option maxHeartbeats 300000
namespace Zeta3.Construction.Features
open Polynomial Finset Matrix Module Zeta5.Arithmetic Zeta3.Arithmetic OddZeta.FourValue

private theorem linear_rank_smul_le {F V W : Type*} [Field F]
    [AddCommGroup V] [Module F V] [AddCommGroup W] [Module F W]
    [FiniteDimensional F W] (a : F) (f : V →ₗ[F] W) :
    finrank F (a • f).range ≤ finrank F f.range := by
  apply Submodule.finrank_mono
  rintro z ⟨x,rfl⟩
  exact Submodule.smul_mem f.range a ⟨x,rfl⟩

variable {p : ℕ} [Fact p.Prime]

def secondRestrictedResidueBilinear (N m₁ m₂ r u₁ u₂ : ℕ) (hp : 2<p)
    (h₁ : 2*(m₁+r)-2<p^2) (h₂ : 2*(m₂+r)-2<p^2)
    (hN : 2*N<p^2) (hD : restrictionDepth m₁ r p+restrictionDepth m₂ r p<p)
    (hmJ₁ : m₁≤featureStart m₁ r p) (hmJ₂ : m₂≤featureStart m₂ r p) :
    secondKernelFeatureSpace N m₁ r u₁ (ne_of_gt hp) h₁ hmJ₁ →ₗ[PadicResidueField p]
      Module.Dual (PadicResidueField p)
        (secondKernelFeatureSpace N m₂ r u₂ (ne_of_gt hp) h₂ hmJ₂) :=
  (secondKernelFeatureSpace N m₂ r u₂ (ne_of_gt hp) h₂ hmJ₂).dualRestrict.comp
    ((secondResidueBilinear N m₁ m₂ r hp h₁ h₂ hN hD).domRestrict
      (secondKernelFeatureSpace N m₁ r u₁ (ne_of_gt hp) h₁ hmJ₁))

theorem secondRestrictedResidueBilinear_eq_sum (N m₁ m₂ r u₁ u₂ : ℕ) (hp : 2<p)
    (h₁ : 2*(m₁+r)-2<p^2) (h₂ : 2*(m₂+r)-2<p^2)
    (hN : 2*N<p^2) (hD : restrictionDepth m₁ r p+restrictionDepth m₂ r p<p)
    (hmJ₁ : m₁≤featureStart m₁ r p) (hmJ₂ : m₂≤featureStart m₂ r p) :
    secondRestrictedResidueBilinear N m₁ m₂ r u₁ u₂ hp h₁ h₂ hN hD hmJ₁ hmJ₂=
      ∑ c : nonmaximalReflectedClasses N p,
        (padicReduction p ⟨secondLocalMultiplier N p c.val,
          secondLocalMultiplier_integral (by omega : N<p^2)⟩) •
          secondRestrictedLocalBilinear N m₁ m₂ r c.val u₁ u₂ hp h₁ h₂ hN
            (nonmaximalReflectedClasses_half N p c.property).1
            (nonmaximalReflectedClasses_half N p c.property).2 hD hmJ₁ hmJ₂ := by
  apply LinearMap.ext
  intro x
  apply LinearMap.ext
  intro y
  let ev₁ : ((Fin r→PadicResidueField p) →ₗ[PadicResidueField p]
      Module.Dual (PadicResidueField p) (Fin r→PadicResidueField p)) →+ PadicResidueField p :=
    { toFun := fun B => B x.val.val y.val.val
      map_zero' := rfl
      map_add' := fun _ _ => rfl }
  let ev₂ : (secondKernelFeatureSpace N m₁ r u₁ (ne_of_gt hp) h₁ hmJ₁ →ₗ[PadicResidueField p]
      Module.Dual (PadicResidueField p)
        (secondKernelFeatureSpace N m₂ r u₂ (ne_of_gt hp) h₂ hmJ₂)) →+ PadicResidueField p :=
    { toFun := fun B => B x y
      map_zero' := rfl
      map_add' := fun _ _ => rfl }
  change ev₁ (secondResidueFullBilinear N m₁ m₂ r hp h₁ h₂ hN hD)=
    ev₂ (∑ c : nonmaximalReflectedClasses N p,
        (padicReduction p ⟨secondLocalMultiplier N p c.val,
          secondLocalMultiplier_integral (by omega : N<p^2)⟩) •
          secondRestrictedLocalBilinear N m₁ m₂ r c.val u₁ u₂ hp h₁ h₂ hN
            (nonmaximalReflectedClasses_half N p c.property).1
            (nonmaximalReflectedClasses_half N p c.property).2 hD hmJ₁ hmJ₂)
  rw [secondResidueFullBilinear,map_sum,map_sum]
  apply Finset.sum_congr rfl
  intro c hc
  rfl

theorem secondResidueBilinear_rank_le_featureCost
    (N m₁ m₂ r u₁ u₂ : ℕ) (hp : 2<p)
    (h₁ : 2*(m₁+r)-2<p^2) (h₂ : 2*(m₂+r)-2<p^2)
    (hN : 2*N<p^2) (hD : restrictionDepth m₁ r p+restrictionDepth m₂ r p<p)
    (hm₁ : 0<m₁) (hm₂ : 0<m₂)
    (hmJ₁ : m₁≤featureStart m₁ r p) (hmJ₂ : m₂≤featureStart m₂ r p)
    (hu₁ : u₁≤1) (hu₂ : u₂≤1) :
    finrank (PadicResidueField p) (secondResidueBilinear N m₁ m₂ r hp h₁ h₂ hN hD).range≤
      secondFeatureCost N m₁ m₂ r p u₁ u₂ := by
  classical
  have hr : finrank (PadicResidueField p)
      (secondRestrictedResidueBilinear N m₁ m₂ r u₁ u₂ hp h₁ h₂ hN hD hmJ₁ hmJ₂).range≤
      ∑ c∈nonmaximalReflectedClasses N p,secondLocalRankCap N m₁ m₂ r p c u₁ u₂ := by
    rw [secondRestrictedResidueBilinear_eq_sum]
    refine (linear_rank_sum_le (K := PadicResidueField p)
      (V := secondKernelFeatureSpace N m₁ r u₁ (ne_of_gt hp) h₁ hmJ₁)
      (W := Module.Dual (PadicResidueField p)
        (secondKernelFeatureSpace N m₂ r u₂ (ne_of_gt hp) h₂ hmJ₂))
      Finset.univ _).trans ?_
    rw [← Finset.sum_coe_sort (nonmaximalReflectedClasses N p)
      (fun c => secondLocalRankCap N m₁ m₂ r p c u₁ u₂)]
    apply Finset.sum_le_sum
    intro c hc
    let B := secondRestrictedLocalBilinear N m₁ m₂ r c.val u₁ u₂ hp h₁ h₂ hN
      (nonmaximalReflectedClasses_half N p c.property).1
      (nonmaximalReflectedClasses_half N p c.property).2 hD hmJ₁ hmJ₂
    let a := padicReduction p ⟨secondLocalMultiplier N p c.val,
      secondLocalMultiplier_integral (by omega : N<p^2)⟩
    have hs : (a • B).range≤B.range := by
      rintro z ⟨x,rfl⟩
      exact Submodule.smul_mem B.range a ⟨x,rfl⟩
    exact (Submodule.finrank_mono hs).trans
      (secondRestrictedLocalBilinear_rank_le N m₁ m₂ r c.val u₁ u₂ hp h₁ h₂ hN
        (nonmaximalReflectedClasses_half N p c.property).1
        (nonmaximalReflectedClasses_half N p c.property).2 hD hmJ₁ hmJ₂ hu₁ hu₂
        (mem_sdiff.mp c.property).2)

  have h := bilinear_rank_restrict_loss (K := PadicResidueField p)
    (V := FirstRestrictionKernel N m₁ r (ne_of_gt hp) h₁)
    (W := FirstRestrictionKernel N m₂ r (ne_of_gt hp) h₂)
    (secondResidueBilinear N m₁ m₂ r hp h₁ h₂ hN hD)
    (secondKernelFeatureSpace N m₁ r u₁ (ne_of_gt hp) h₁ hmJ₁)
    (secondKernelFeatureSpace N m₂ r u₂ (ne_of_gt hp) h₂ hmJ₂)
  rw [secondKernelFeatureSpace_codimension N m₁ r u₁ (by omega) h₁ hm₁ hmJ₁ hu₁,
    secondKernelFeatureSpace_codimension N m₂ r u₂ (by omega) h₂ hm₂ hmJ₂ hu₂] at h
  exact h.trans (Nat.add_le_add_right (Nat.add_le_add_right hr _) _)

theorem secondResidueBilinear_rank_le
    (N m₁ m₂ r : ℕ) (hp : 2<p)
    (h₁ : 2*(m₁+r)-2<p^2) (h₂ : 2*(m₂+r)-2<p^2)
    (hN : 2*N<p^2) (hD : restrictionDepth m₁ r p+restrictionDepth m₂ r p<p)
    (hm₁ : 0<m₁) (hm₂ : 0<m₂)
    (hmJ₁ : m₁≤featureStart m₁ r p) (hmJ₂ : m₂≤featureStart m₂ r p) :
    finrank (PadicResidueField p) (secondResidueBilinear N m₁ m₂ r hp h₁ h₂ hN hD).range≤
      secondRankBound N m₁ m₂ r p := by
  have hleft := (secondResidueBilinear N m₁ m₂ r hp h₁ h₂ hN hD).finrank_range_le
  have hright := (secondResidueBilinear N m₁ m₂ r hp h₁ h₂ hN hD).range.finrank_le
  rw [Subspace.dual_finrank_eq] at hright
  rw [firstRestrictionKernel_finrank N m₁ r (by omega) h₁ hm₁ hmJ₁] at hleft
  rw [firstRestrictionKernel_finrank N m₂ r (by omega) h₂ hm₂ hmJ₂] at hright
  exact le_min (le_min hleft hright)
    (le_min
      (le_min
        (secondResidueBilinear_rank_le_featureCost N m₁ m₂ r 0 0 hp h₁ h₂ hN hD hm₁ hm₂ hmJ₁ hmJ₂ (by omega) (by omega))
        (secondResidueBilinear_rank_le_featureCost N m₁ m₂ r 0 1 hp h₁ h₂ hN hD hm₁ hm₂ hmJ₁ hmJ₂ (by omega) (by omega)))
      (le_min
        (secondResidueBilinear_rank_le_featureCost N m₁ m₂ r 1 0 hp h₁ h₂ hN hD hm₁ hm₂ hmJ₁ hmJ₂ (by omega) (by omega))
        (secondResidueBilinear_rank_le_featureCost N m₁ m₂ r 1 1 hp h₁ h₂ hN hD hm₁ hm₂ hmJ₁ hmJ₂ (by omega) (by omega))))

end Zeta3.Construction.Features

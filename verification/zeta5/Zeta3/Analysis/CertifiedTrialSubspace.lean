import Zeta3.Analysis.CertifiedTrialNorm
import Zeta3.Analysis.SpectralMinmaxOperator

/-! # The actual trial subspaces in the fixed polynomial space -/

noncomputable section
namespace Zeta3.Analysis
open Polynomial Set

def polynomialMultiplyIntoDegreeLT (H : ℝ[X]) (d r : ℕ) (heq : d+H.natDegree=r) :
    degreeLT ℝ d →ₗ[ℝ] degreeLT ℝ r where
  toFun p := ⟨(polynomialMultiplyTruncated H d p).val, by
    simpa only [heq] using (polynomialMultiplyTruncated H d p).property⟩
  map_add' := by
    intro p q
    apply Subtype.ext
    change H*(p.val+q.val)=H*p.val+H*q.val
    exact mul_add H p.val q.val
  map_smul' := by
    intro c p
    apply Subtype.ext
    change H*(c • p.val)=c • (H*p.val)
    exact mul_smul_comm c H p.val

theorem polynomialMultiplyIntoDegreeLT_injective (H : ℝ[X]) (d r : ℕ)
    (heq : d+H.natDegree=r) (hH : H≠0) :
    Function.Injective (polynomialMultiplyIntoDegreeLT H d r heq) := by
  intro p q hpq
  apply Subtype.ext
  have hv := congrArg (fun x : degreeLT ℝ r => x.val) hpq
  change H*p.val=H*q.val at hv
  exact mul_left_cancel₀ hH hv

theorem polynomialMultiplyIntoDegreeLT_codimension (H : ℝ[X]) (d r : ℕ)
    (heq : d+H.natDegree=r) (hH : H≠0) :
    Module.finrank ℝ ((degreeLT ℝ r) ⧸
      LinearMap.range (polynomialMultiplyIntoDegreeLT H d r heq))=H.natDegree := by
  letI : FiniteDimensional ℝ (degreeLT ℝ r) :=
    FiniteDimensional.of_injective (degreeLTEquiv ℝ r).toLinearMap (degreeLTEquiv ℝ r).injective
  have hd : Module.finrank ℝ (LinearMap.range (polynomialMultiplyIntoDegreeLT H d r heq))=d := by
    rw [LinearMap.finrank_range_of_inj (polynomialMultiplyIntoDegreeLT_injective H d r heq hH)]
    simpa using (degreeLTEquiv ℝ d).finrank_eq
  have hr : Module.finrank ℝ (degreeLT ℝ r)=r := by
    simpa using (degreeLTEquiv ℝ r).finrank_eq
  have hdim := (LinearMap.range (polynomialMultiplyIntoDegreeLT H d r heq)).finrank_quotient_add_finrank
  rw [hd,hr] at hdim
  omega

namespace CertificateResponse

theorem exists_actual_trial_subspace (n m : ℕ) (hn : 0 < n)
    (hcap : 2*(m:ℝ)/(50*n) ≤ angularCap)
    {lower : ℕ → ℝ} (hfinite : CertificateLinear.FiniteEvidence lower)
    (hguard : angularCap < angularMass CertificateAngular.coefficient
      CertificateAngular.weight CertificateAngular.pole 1) :
    ∃ S : Submodule ℝ (degreeLT ℝ (51*n)),
      Module.finrank ℝ ((degreeLT ℝ (51*n)) ⧸ S)=2*m ∧
      ∀ p ∈ S,
        positiveContourNorm (50*n) (4*n) (16*n) CertificateAngular.contour p.val ≤
          (trialNormConstant*((50*n:ℕ):ℝ)^40*
            Real.exp (((50*n:ℕ):ℝ)*response (2*(m:ℝ)/(50*n)))) *
          normalizedPhysicalNorm (50*n) (4*n) (16*n) p.val := by
  obtain ⟨h,hh,hbound⟩ := exists_actual_trial_norm_bound n m hn hcap hfinite hguard
  have hrem := trial_degree_removed_le n m hn hcap
  let H := angularZeroProduct (CertificateAngular.contour^2) h
  have hdeg : H.natDegree=2*m := angularZeroProduct_natDegree _ _
  have heq : (51*n-2*m)+H.natDegree=51*n := by omega
  let f := polynomialMultiplyIntoDegreeLT H (51*n-2*m) (51*n) heq
  refine ⟨LinearMap.range f,?_,?_⟩
  · rw [polynomialMultiplyIntoDegreeLT_codimension H _ _ heq (angularZeroProduct_monic _ _).ne_zero,hdeg]
  · intro p hp
    obtain ⟨q,rfl⟩ := LinearMap.mem_range.mp hp
    have hqd : q.val.natDegree < 51*n-2*m := by
      by_cases hq : q.val=0
      · simp only [hq,natDegree_zero]
        omega
      · exact (natDegree_lt_iff_degree_lt hq).mpr (mem_degreeLT.mp q.property)
    exact hbound q.val hqd

end CertificateResponse
end Zeta3.Analysis

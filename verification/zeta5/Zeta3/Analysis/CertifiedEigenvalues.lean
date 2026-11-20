import Zeta3.Analysis.CertifiedTrialSubspace
import Zeta3.Analysis.ContourPhysicalSpace
import Mathlib.Analysis.InnerProductSpace.Positive

/-! # Bounds for the actual positive contour operator's eigenvalues -/

noncomputable section
namespace Zeta3.Analysis.CertificateResponse
open Polynomial Set

def actualContourEigenvalues (n : ℕ) (hn : 0<n) : Fin (51*n)→ℝ :=
  (contourPolynomialOperator_isSymmetric (50*n) (4*n) (16*n) (51*n)
    (by omega) CertificateAngular.contour (by norm_num [CertificateAngular.contour])).eigenvalues
      (realDegreeLT_finrank (51*n))

theorem actualContourEigenvalues_antitone (n : ℕ) (hn : 0<n) :
    Antitone (actualContourEigenvalues n hn) :=
  (contourPolynomialOperator_isSymmetric (50*n) (4*n) (16*n) (51*n)
    (by omega) CertificateAngular.contour (by norm_num [CertificateAngular.contour])).eigenvalues_antitone _

theorem actualContourEigenvalues_nonneg (n : ℕ) (hn : 0<n) (j : Fin (51*n)) :
    0≤actualContourEigenvalues n hn j := by
  have hp : (contourPolynomialOperator (50*n) (4*n) (16*n) (51*n)
      (by omega) CertificateAngular.contour (by norm_num [CertificateAngular.contour])).IsPositive :=
    ⟨contourPolynomialOperator_isSymmetric _ _ _ _ _ _ _,
      contourPolynomialOperator_nonneg _ _ _ _ _ _ _⟩
  exact hp.nonneg_eigenvalues (realDegreeLT_finrank (51*n)) j

theorem actualContourEigenvalues_even_bound (n m : ℕ) (hn : 0<n)
    (hm : 2*m<51*n) (hcap : 2*(m:ℝ)/(50*n)≤angularCap)
    {lower : ℕ→ℝ} (hfinite : CertificateLinear.FiniteEvidence lower)
    (hguard : angularCap<angularMass CertificateAngular.coefficient
      CertificateAngular.weight CertificateAngular.pole 1) :
    actualContourEigenvalues n hn ⟨2*m,hm⟩≤
      trialNormConstant*((50*n:ℕ):ℝ)^40*
        Real.exp (((50*n:ℕ):ℝ)*response (2*(m:ℝ)/(50*n))) := by
  obtain ⟨S,hcodim,hbound⟩ := exists_actual_trial_subspace n m hn hcap hfinite hguard
  exact positiveContour_eigenvalue_le_of_subspace
    (50*n) (4*n) (16*n) (51*n) (by omega) CertificateAngular.contour
    (by norm_num [CertificateAngular.contour]) ⟨2*m,hm⟩ S hcodim.le _ hbound

end Zeta3.Analysis.CertificateResponse

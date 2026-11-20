import Zeta3.Analysis.CertifiedResponse

/-! # Continuity at the actual spectral cutoff -/

noncomputable section
namespace Zeta3.Analysis.CertificateResponse
open Set

theorem response_continuousAt_cutoff : ContinuousAt response cutoff := by
  have hΓ : ContinuousAt gamma (delta-cutoff) :=
    (physicalGamma_hasDerivAt (2/25) (8/25) CertificateAngular.contour
      (by norm_num) (by norm_num) contour_pos (by norm_num [delta,cutoff])).continuousAt
  have hF := (angularProfile_hasDerivAt CertificateAngular.coefficient
    CertificateAngular.weight CertificateAngular.pole CertificateAngular.coefficient_pos
    CertificateAngular.weight_nonneg CertificateAngular.pole_pos cutoff_pos).continuousAt
  exact (hΓ.comp (continuous_const.sub continuous_id).continuousAt).add hF

theorem response_continuousWithinAt_cutoff :
    ContinuousWithinAt response (Icc 0 cutoff) cutoff :=
  response_continuousAt_cutoff.continuousWithinAt

end Zeta3.Analysis.CertificateResponse

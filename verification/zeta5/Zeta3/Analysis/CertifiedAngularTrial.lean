import Zeta3.Analysis.PhysicalTrialParameters

/-!
# Concrete trial spaces with the actual certified response exponent

All parameters, measures, polynomial factors and exponents are the actual
ones. The only external inputs are the finite angular support guard and
the finite linear-correction certificate.
-/

noncomputable section
namespace Zeta3.Analysis.CertificateResponse
open Set Polynomial
open scoped BigOperators

def trialConstant : ℝ :=
  angularQuantileConstant CertificateAngular.coefficient CertificateAngular.weight CertificateAngular.pole*
    physicalNormComparisonConstant delta (physicalDensityCompactConstant (2/25) (8/25) 5)

theorem trialConstant_pos : 0 < trialConstant := by
  unfold trialConstant
  apply mul_pos (angularQuantileConstant_pos _ _ _)
  exact physicalNormComparisonConstant_pos delta _ (by norm_num [delta])
    (physicalDensityCompactConstant_pos _ _ _ (by norm_num))

theorem exists_actual_trial_circle_bound (n m : ℕ) (hn : 0 < n)
    (hcap : 2*(m:ℝ)/(50*n) ≤ angularCap)
    {lower : ℕ → ℝ} (hfinite : CertificateLinear.FiniteEvidence lower)
    (hguard : angularCap < angularMass CertificateAngular.coefficient
      CertificateAngular.weight CertificateAngular.pole 1) :
    ∃ h : Fin m → ℝ, (∀ i, h i ∈ Icc 0 1) ∧
      ∀ p : ℝ[X], p.natDegree < 51*n-2*m → ∀ z : ℂ,
        Complex.normSq z=CertificateAngular.contour^4 →
        Real.exp (((50*n:ℕ):ℝ)*rationalContourPotential (2/25) (8/25) z)*
          ‖(angularZeroProduct (CertificateAngular.contour^2) h*p).eval₂ Complex.ofRealHom z‖^2 ≤
          trialConstant*((50*n:ℕ):ℝ)^36*
            normalizedPhysicalNorm (50*n) (4*n) (16*n) (angularZeroProduct (CertificateAngular.contour^2) h*p)*
              Real.exp (((50*n:ℕ):ℝ)*response (2*(m:ℝ)/(50*n))) := by
  have hN : 0 < 50*n := by omega
  have hN1 : (1:ℝ) ≤ ((50*n:ℕ):ℝ) := by exact_mod_cast hN
  have hNN : (0:ℝ) < ((50*n:ℕ):ℝ) := by exact_mod_cast hN
  have hcap' : 2*(m:ℝ)/((50*n:ℕ):ℝ) ≤ angularCap := by
    simpa only [Nat.cast_mul,Nat.cast_ofNat] using hcap
  obtain ⟨h,hh,hquantile⟩ := exists_certified_angular_factors hN1 m hcap' hguard
  refine ⟨h,hh,?_⟩
  intro p hp z hz
  have hrat := concrete_window_ratios n hn
  have hr₁ : ((4*n:ℕ):ℝ)/((50*n:ℕ):ℝ)=2/25 := by
    simpa only [Nat.cast_mul,Nat.cast_ofNat] using hrat.1
  have hr₂ : ((16*n:ℕ):ℝ)/((50*n:ℕ):ℝ)=8/25 := by
    simpa only [Nat.cast_mul,Nat.cast_ofNat] using hrat.2
  have hb := trialEndpoint_bounds n m hn hcap
  have hb0 : 0 ≤ trialEndpoint n m := by linarith [hb.1]
  have hbs := trialEndpoint_square_bounds n m hn hcap
  have hmass := trialEndpoint_mass_index n m hn hcap
  have hnr : p.natDegree ≤ 51*n := by omega
  have hdim : ((51*n:ℕ):ℝ) ≤ delta*((50*n:ℕ):ℝ) := by
    norm_num only [Nat.cast_mul,Nat.cast_ofNat,delta]
    nlinarith
  have ht : 2*(m:ℝ)/(50*n) ∈ Icc 0 angularCap := ⟨by positivity,hcap⟩
  have hpot := actual_contour_exponent_bound hfinite ht z hz
  have hy := contourAngularCoordinate_mem (by norm_num [CertificateAngular.contour] : 0 < CertificateAngular.contour) hz
  let F := angularProfile CertificateAngular.coefficient CertificateAngular.weight CertificateAngular.pole
    CertificateAngular.coefficient_pos CertificateAngular.weight_nonneg CertificateAngular.pole_pos (2*(m:ℝ)/(50*n))
  have hmain := angular_trial_weighted_contour_bound
    CertificateAngular.coefficient CertificateAngular.weight CertificateAngular.pole h hh
    p (51*n) (50*n) (4*n) (16*n) (51*n-2*m) delta (trialEndpoint n m) 5
    CertificateAngular.contour F (gamma (delta-2*(m:ℝ)/(50*n)))
    hnr hp hN (by omega) (by omega) (by norm_num [delta]) hdim hb0 hbs.2 hbs.1
    (by norm_num [CertificateAngular.contour])
    (by rw [hr₁,hr₂]; exact hmass) z hz
    (by simpa only [F,Nat.cast_mul,Nat.cast_ofNat] using hquantile (contourAngularCoordinate CertificateAngular.contour z) hy.1)
    (by
      simpa only [hr₁,hr₂,contourExponent,physicalContourExponent,trialEndpoint,trialMass,physicalEquilibrium] using hpot)
  rw [hr₁,hr₂] at hmain
  simpa only [trialConstant,response,simpleResponse,F,Nat.cast_mul,Nat.cast_ofNat,mul_assoc] using hmain

end Zeta3.Analysis.CertificateResponse

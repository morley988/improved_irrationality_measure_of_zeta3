import Zeta3.Arithmetic.CellCoverage
import Zeta3.Analysis.ArithmeticRate
import Zeta3.Endpoint.ConcreteRateTransfer

/-!
# Arithmetic rate from a finite rational profile

Coverage and area are finite rational assertions. The local valuation
comparison remains an explicit mathematical premise of this generic
assembly theorem, to be discharged by the actual feature-rank results.
-/

noncomputable section
namespace Zeta3.Endpoint
open Filter Zeta3.Arithmetic Zeta3.Arithmetic.ProfileCertificate Zeta3.Construction
open Zeta5.Reuse.PrimePiecewise
open scoped Topology

theorem actualArithmeticRate_of_finite_cells (cells : List Cell) (upper : ℚ)
    (hcoverage : CoverageCertificate cells upper) (hupper : (upper:ℝ)≤Parameters.arithmeticUpper)
    (K : ℝ) (hK : 0≤K) (width : ℕ)
    (hregular : ∀ᶠ n : ℕ in atTop,∀ c∈cells,∀ p : ℕ,p.Prime →
      (c.lo:ℝ)<(p:ℝ)/((50*n:ℕ):ℝ) → (p:ℝ)/((50*n:ℕ):ℝ)<(c.hi:ℝ) →
      (p:ℝ)+width<(c.hi:ℝ)*((50*n:ℕ):ℝ) →
      (padicValRat p (windowNormalizer n):ℝ)≤
        ((50*n:ℕ):ℝ)*c.affine.real ((p:ℝ)/((50*n:ℕ):ℝ))+K) :
    ActualArithmeticRate := by
  let pieces := cells.map Cell.toPiece
  have hfit : CellsFit (1/500) pieces (67/25) := hcoverage.cellsFit
  have hlocal : ∀ᶠ n : ℕ in atTop,∀ c∈pieces,∀ p : ℕ,p.Prime →
      c.lo<(p:ℝ)/((50*n:ℕ):ℝ) → (p:ℝ)/((50*n:ℕ):ℝ)<c.hi →
      (p:ℝ)+width<c.hi*((50*n:ℕ):ℝ) →
      (padicValRat p (windowNormalizer n):ℝ)≤
        ((50*n:ℕ):ℝ)*(c.intercept+c.slope*((p:ℝ)/((50*n:ℕ):ℝ)))+K := by
    filter_upwards [hregular] with n hn
    intro c hc
    obtain ⟨d,hd,rfl⟩ := List.mem_map.mp hc
    exact hn d hd
  have hprime := windowNormalizer_finiteStripProfile_bound_eventually pieces hfit K hK width hlocal
  exact Zeta3.Analysis.exists_arithmetic_rate_error_of_prime_profile pieces hcoverage.valid
    (primeErrorCoefficient pieces K) (stripEndpointErrorCoefficient pieces width)
    Parameters.arithmeticUpper (hcoverage.area_bound.trans hupper) hprime

end Zeta3.Endpoint

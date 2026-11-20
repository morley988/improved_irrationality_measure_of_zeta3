import Zeta3.Arithmetic.SecondTransportActual
import Zeta3.Construction.SecondRank

/-! The actual second-layer determinant bound, with its feature and parity
rank proved internally. No residue-rank assumption remains. -/
noncomputable section
namespace Zeta3.Arithmetic
open Polynomial Matrix Module Finset Zeta5.Arithmetic Zeta5.Construction
open Zeta3.Construction.Features OddZeta.FourValue
variable {p : ℕ} [Fact p.Prime]

theorem unscaledCentralPencil_second_bound (N m₁ m₂ r : ℕ) (hp : 2<p)
    (hNmax : N≤max (m₁+r) (m₂+r))
    (hstrong : 8*max (m₁+r) (m₂+r)+100<p^2)
    (hm₁ : 0<m₁) (hm₂ : 0<m₂)
    (hmJ₁ : m₁≤featureStart m₁ r p) (hmJ₂ : m₂≤featureStart m₂ r p) :
    PolynomialPadicLower p
      (-(1+((2*(N%p)/p:ℕ):ℤ))*(r:ℤ)-featureRankBound N m₁ r p-
        featureRankBound N m₂ r p-secondRankBound N m₁ m₂ r p)
      (unscaledCentralPencil N m₁ m₂ r).det := by
  obtain ⟨h₁,h₂,hN,hD⟩ := second_transport_window_conditions N m₁ m₂ r p hNmax hstrong
  exact unscaledCentralPencil_second_bound_of_rank N m₁ m₂ r hp hNmax hstrong
    h₁ h₂ hN hD hm₁ hm₂ hmJ₁ hmJ₂
    (secondResidueBilinear_rank_le N m₁ m₂ r hp h₁ h₂ hN hD hm₁ hm₂ hmJ₁ hmJ₂)

end Zeta3.Arithmetic

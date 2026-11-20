import Zeta3.Arithmetic.SecondTransport
import Zeta3.Arithmetic.SecondTransportReduction

/-!
# Actual two-kernel determinant transport for the cubic Pearson pencil

All matrix identifications and valuation losses are proved for the genuine
pencil. The rank hypothesis here is the rank of its explicitly defined
finite residue bilinear form, to be supplied by the separate feature/parity
rank theorem.
-/

noncomputable section
namespace Zeta3.Arithmetic
open Polynomial Matrix Module Finset Zeta5.Arithmetic Zeta5.Construction
open Zeta3.Construction.Features OddZeta.FourValue
open scoped BigOperators
variable {p : ℕ} [Fact p.Prime]

theorem second_transport_window_conditions (N m₁ m₂ r p : ℕ)
    (hN : N≤max (m₁+r) (m₂+r)) (h : 8*max (m₁+r) (m₂+r)+100<p^2) :
    (2*(m₁+r)-2<p^2) ∧ (2*(m₂+r)-2<p^2) ∧ (2*N<p^2) ∧
      restrictionDepth m₁ r p+restrictionDepth m₂ r p<p := by
  have hm₁ := le_max_left (m₁+r) (m₂+r)
  have hm₂ := le_max_right (m₁+r) (m₂+r)
  refine ⟨by omega,by omega,by omega,?_⟩
  have hq₁ := (Nat.div_mul_le_self (2*(m₁+r)-2) p).trans (Nat.sub_le (2*(m₁+r)) 2)
  have hq₂ := (Nat.div_mul_le_self (2*(m₂+r)-2) p).trans (Nat.sub_le (2*(m₂+r)) 2)
  unfold restrictionDepth
  by_contra! hn
  have hh := Nat.mul_le_mul_right p hn
  nlinarith

theorem scaledCentralPencil_divided_pair_constant (N m₁ m₂ r : ℕ)
    (x y : Fin r→padicIntegralSubring p) :
    (C ((p:ℚ)⁻¹)*localMatrixPair (scaledCentralPencil N m₁ m₂ r p) x y).coeff 0=
      (p:ℚ)^(2+2*(N%p)/p)*
      (normalizedCentralFunctional N (centralWindowPolynomial m₁ r (fun i => (x i:ℚ))*
        centralWindowPolynomial m₂ r (fun i => (y i:ℚ)))).coeff 0 := by
  have hp0 : (p:ℚ)≠0 := by exact_mod_cast (Fact.out:p.Prime).ne_zero
  rw [localMatrixPair_scaledCentralPencil,←mul_assoc,←C_mul,coeff_C_mul]
  have he : (p:ℚ)⁻¹*(p:ℚ)^localPencilScale N p=(p:ℚ)^(2+2*(N%p)/p) := by
    rw [show localPencilScale N p=(2+2*(N%p)/p)+1 by unfold localPencilScale;omega,pow_succ]
    field_simp
  rw [he]

theorem scaledCentralPencil_second_form (N m₁ m₂ r : ℕ) (hp : 2<p)
    (hNmax : N≤max (m₁+r) (m₂+r))
    (hstrong : 8*max (m₁+r) (m₂+r)+100<p^2)
    (h₁ : 2*(m₁+r)-2<p^2) (h₂ : 2*(m₂+r)-2<p^2)
    (hN : 2*N<p^2) (hD : restrictionDepth m₁ r p+restrictionDepth m₂ r p<p)
    (x : Fin r→padicIntegralSubring p)
    (hx : (reducedRestrictionMatrix N m₁ r (by omega : p≠2) h₁).mulVecLin
      (localReducedVector x)=0)
    (y : Fin r→padicIntegralSubring p)
    (hy : (reducedRestrictionMatrix N m₂ r (by omega : p≠2) h₂).mulVecLin
      (localReducedVector y)=0)
    (h : PadicLower p 0 ((C ((p:ℚ)⁻¹)*
      localMatrixPair (scaledCentralPencil N m₁ m₂ r p) x y).coeff 0)) :
    padicReduction p ⟨(C ((p:ℚ)⁻¹)*
      localMatrixPair (scaledCentralPencil N m₁ m₂ r p) x y).coeff 0,h⟩=
      secondResidueBilinear N m₁ m₂ r hp h₁ h₂ hN hD
        ⟨localReducedVector x,hx⟩ ⟨localReducedVector y,hy⟩ := by
  have he := scaledCentralPencil_divided_pair_constant N m₁ m₂ r x y
  have hv := h
  rw [he] at hv
  calc
    _=padicReduction p ⟨(p:ℚ)^(2+2*(N%p)/p)*
      (normalizedCentralFunctional N (centralWindowPolynomial m₁ r (fun i => (x i:ℚ))*
        centralWindowPolynomial m₂ r (fun i => (y i:ℚ)))).coeff 0,hv⟩ := by
      apply congrArg (padicReduction p)
      apply Subtype.ext
      exact he
    _=_ := normalizedCentralWindow_second_residue N m₁ m₂ r hp hNmax hstrong h₁ h₂ hN hD x y hx hy hv

theorem scaledCentralPencil_second_bound_of_rank (N m₁ m₂ r : ℕ) (hp : 2<p)
    (hNmax : N≤max (m₁+r) (m₂+r))
    (hstrong : 8*max (m₁+r) (m₂+r)+100<p^2)
    (h₁ : 2*(m₁+r)-2<p^2) (h₂ : 2*(m₂+r)-2<p^2)
    (hN : 2*N<p^2) (hD : restrictionDepth m₁ r p+restrictionDepth m₂ r p<p)
    (hm₁ : 0<m₁) (hm₂ : 0<m₂)
    (hmJ₁ : m₁≤featureStart m₁ r p) (hmJ₂ : m₂≤featureStart m₂ r p)
    (hrank : finrank (PadicResidueField p)
      (secondResidueBilinear N m₁ m₂ r hp h₁ h₂ hN hD).range≤secondRankBound N m₁ m₂ r p) :
    PolynomialPadicLower p (2*(r:ℤ)-featureRankBound N m₁ r p-featureRankBound N m₂ r p-
      secondRankBound N m₁ m₂ r p) (scaledCentralPencil N m₁ m₂ r p).det := by
  have hweak : 4*max (m₁+r) (m₂+r)+4<p^2 := by omega
  have hdet := two_kernel_lower_of_residue_bilinear
    (scaledCentralPencil N m₁ m₂ r p)
    (reducedRestrictionMatrix N m₁ r (by omega : p≠2) h₁).mulVecLin
    (reducedRestrictionMatrix N m₂ r (by omega : p≠2) h₂).mulVecLin
    (secondResidueBilinear N m₁ m₂ r hp h₁ h₂ hN hD) (secondRankBound N m₁ m₂ r p)
    (scaledCentralPencil_integral N m₁ m₂ r hp hNmax hweak)
    (localMatrixPair_scaledCentralPencil_left N m₁ m₂ r hp hNmax hweak h₁)
    (localMatrixPair_scaledCentralPencil_right N m₁ m₂ r hp hNmax hweak h₂)
    (scaledCentralPencil_coeff_pos_two N m₁ m₂ r hp hN)
    (scaledCentralPencil_second_form N m₁ m₂ r hp hNmax hstrong h₁ h₂ hN hD) hrank
  simp only [Fintype.card_fin] at hdet
  change PolynomialPadicLower p (2*(r:ℤ)-
    (reducedRestrictionMatrix N m₁ r (by omega : p≠2) h₁).rank-
    (reducedRestrictionMatrix N m₂ r (by omega : p≠2) h₂).rank-secondRankBound N m₁ m₂ r p) _ at hdet
  rw [reducedRestrictionMatrix_rank N m₁ r (by omega) h₁ hm₁ hmJ₁,
    reducedRestrictionMatrix_rank N m₂ r (by omega) h₂ hm₂ hmJ₂] at hdet
  exact hdet

theorem unscaledCentralPencil_second_bound_of_rank (N m₁ m₂ r : ℕ) (hp : 2<p)
    (hNmax : N≤max (m₁+r) (m₂+r))
    (hstrong : 8*max (m₁+r) (m₂+r)+100<p^2)
    (h₁ : 2*(m₁+r)-2<p^2) (h₂ : 2*(m₂+r)-2<p^2)
    (hN : 2*N<p^2) (hD : restrictionDepth m₁ r p+restrictionDepth m₂ r p<p)
    (hm₁ : 0<m₁) (hm₂ : 0<m₂)
    (hmJ₁ : m₁≤featureStart m₁ r p) (hmJ₂ : m₂≤featureStart m₂ r p)
    (hrank : finrank (PadicResidueField p)
      (secondResidueBilinear N m₁ m₂ r hp h₁ h₂ hN hD).range≤secondRankBound N m₁ m₂ r p) :
    PolynomialPadicLower p
      (-(1+((2*(N%p)/p:ℕ):ℤ))*(r:ℤ)-featureRankBound N m₁ r p-
        featureRankBound N m₂ r p-secondRankBound N m₁ m₂ r p)
      (unscaledCentralPencil N m₁ m₂ r).det := by
  have hdet := scaledCentralPencil_second_bound_of_rank N m₁ m₂ r hp hNmax hstrong
    h₁ h₂ hN hD hm₁ hm₂ hmJ₁ hmJ₂ hrank
  have h := (PolynomialPadicLower.constant
    (inverse_prime_power_padicLower (p:=p) (localPencilScale N p*r))).mul hdet
  rw [scaledCentralPencil_det,←mul_assoc,←C_mul] at h
  have hp0 : (p:ℚ)≠0 := by exact_mod_cast (Fact.out:p.Prime).ne_zero
  rw [inv_mul_cancel₀ (pow_ne_zero _ hp0),C_1,one_mul] at h
  convert h using 1
  simp only [localPencilScale,Nat.cast_mul,Nat.cast_add,Nat.cast_ofNat]
  ring

end Zeta3.Arithmetic

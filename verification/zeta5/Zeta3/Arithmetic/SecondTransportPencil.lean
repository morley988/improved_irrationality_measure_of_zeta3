import Zeta3.Arithmetic.SecondTransportAlgebra
import Zeta3.Arithmetic.FeatureFirstLayer
import Zeta3.Arithmetic.LocalLinear

/-! Actual Pearson-pencil inputs for the two-kernel determinant transport. -/

noncomputable section
namespace Zeta3.Arithmetic
open Matrix Module Polynomial Finset OddZeta.FourValue Zeta5.Arithmetic
open Zeta5.Construction Zeta3.Construction Zeta3.Construction.Features
open scoped BigOperators
variable {p : ℕ} [Fact p.Prime]

theorem normalizedCentralWindow_pairing_both (N m₁ m₂ r : ℕ)
    (x y : Fin r→ℚ) :
    normalizedCentralFunctional N
      (centralWindowPolynomial m₁ r x*centralWindowPolynomial m₂ r y)=
        ∑i,∑j,C (x i)*Zeta3.Construction.entry N (m₁+i.val) (m₂+j.val)*C (y j) := by
  simp only [centralWindowPolynomial,Finset.sum_mul,Finset.mul_sum,normalizedCentralFunctional_sum]
  conv_lhs => rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  rw [show C (x i)*centralPolynomial (m₁+i.val)*(C (y j)*centralPolynomial (m₂+j.val))=
      C (x i*y j)*(centralPolynomial (m₁+i.val)*centralPolynomial (m₂+j.val)) by
        rw [C_mul];ring]
  rw [normalizedCentralFunctional_C_mul,←entry_eq_normalizedCentralFunctional,C_mul]
  ring

theorem localMatrixPair_scaledCentralPencil (N m₁ m₂ r : ℕ)
    (x y : Fin r→padicIntegralSubring p) :
    localMatrixPair (scaledCentralPencil N m₁ m₂ r p) x y=
      C ((p:ℚ)^localPencilScale N p)*normalizedCentralFunctional N
        (centralWindowPolynomial m₁ r (fun i => (x i:ℚ))*
          centralWindowPolynomial m₂ r (fun i => (y i:ℚ))) := by
  rw [normalizedCentralWindow_pairing_both]
  simp only [localMatrixPair,scaledCentralPencil,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  ring

theorem localMatrixPair_scaledCentralPencil_left (N m₁ m₂ r : ℕ) (hp : 2<p)
    (hN : N≤max (m₁+r) (m₂+r)) (hsmall : 4*max (m₁+r) (m₂+r)+4<p^2)
    (h₁ : 2*(m₁+r)-2<p^2)
    (x : Fin r→padicIntegralSubring p)
    (hx : (reducedRestrictionMatrix N m₁ r (by omega : p≠2) h₁).mulVecLin
      (localReducedVector x)=0)
    (y : Fin r→padicIntegralSubring p) :
    PolynomialPadicLower p 1 (localMatrixPair (scaledCentralPencil N m₁ m₂ r p) x y) := by
  rw [localMatrixPair_eq_left]
  apply PolynomialPadicLower.sum
  intro j hj
  have h := scaledCentralPencil_restriction_radical N m₁ m₂ r hp hN hsmall
    (fun i => (x i:ℚ)) (fun i => (x i).property)
    (reducedRestriction_kernel_padic N m₁ r (by omega) h₁ x hx) j
  simpa only [add_zero] using h.mul (PolynomialPadicLower.constant (y j).property)

theorem scaledCentralPencil_swap (N m₁ m₂ r : ℕ) (i j : Fin r) :
    scaledCentralPencil N m₁ m₂ r p i j=scaledCentralPencil N m₂ m₁ r p j i := by
  simp only [scaledCentralPencil,entry_eq_normalizedCentralFunctional]
  rw [mul_comm (centralPolynomial (m₁+i.val)) (centralPolynomial (m₂+j.val))]

theorem localMatrixPair_scaledCentralPencil_right (N m₁ m₂ r : ℕ) (hp : 2<p)
    (hN : N≤max (m₁+r) (m₂+r)) (hsmall : 4*max (m₁+r) (m₂+r)+4<p^2)
    (h₂ : 2*(m₂+r)-2<p^2)
    (y : Fin r→padicIntegralSubring p)
    (hy : (reducedRestrictionMatrix N m₂ r (by omega : p≠2) h₂).mulVecLin
      (localReducedVector y)=0)
    (x : Fin r→padicIntegralSubring p) :
    PolynomialPadicLower p 1 (localMatrixPair (scaledCentralPencil N m₁ m₂ r p) x y) := by
  rw [localMatrixPair_scaledCentralPencil]
  rw [mul_comm (centralWindowPolynomial m₁ r _) (centralWindowPolynomial m₂ r _)]
  rw [←localMatrixPair_scaledCentralPencil N m₂ m₁ r y x]
  exact localMatrixPair_scaledCentralPencil_left N m₂ m₁ r hp
    (by simpa only [max_comm] using hN) (by simpa only [max_comm] using hsmall) h₂ y hy x

theorem scaledCentralPencil_coeff_pos_two (N m₁ m₂ r : ℕ) (hp : 2<p)
    (hsmall : 2*N<p^2) (i j : Fin r) (k : ℕ) (hk : 0<k) :
    PadicLower p 2 ((scaledCentralPencil N m₁ m₂ r p i j).coeff k) :=
  (scaledCentralPencil_coeff_pos_three N m₁ m₂ r hp hsmall i j k hk).mono (by norm_num)

end Zeta3.Arithmetic

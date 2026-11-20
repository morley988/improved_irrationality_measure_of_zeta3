import Zeta3.Arithmetic.LocalFunctional
import Zeta3.Construction.Asymmetric
import Zeta5.Arithmetic.RestrictionPencil

/-!
# Coefficient restriction for the actual unequal cubic windows

The row restriction uses the first factorial window; the companion factor
uses the second. The kernel is controlled coefficient by coefficient, with
no equality of the windows assumed.
-/

noncomputable section
namespace Zeta3.Arithmetic
open Polynomial Finset OddZeta.FourValue Zeta5.Construction Zeta3.Construction
open Zeta5.Arithmetic

variable {p : ℕ} [Fact p.Prime]

def localPencilScale (N p : ℕ) : ℕ := 3 + 2 * (N % p) / p

def scaledCentralPencil (N m₁ m₂ r p : ℕ) : Matrix (Fin r) (Fin r) ℚ[X] :=
  fun i j => C ((p : ℚ) ^ localPencilScale N p) *
    Zeta3.Construction.entry N (m₁ + i.val) (m₂ + j.val)

theorem entry_eq_normalizedCentralFunctional (N j k : ℕ) :
    Zeta3.Construction.entry N j k =
      normalizedCentralFunctional N (centralPolynomial j * centralPolynomial k) := by
  rw [Zeta3.Construction.entry_eq_numeratorFunctional, normalizedCentralFunctional_eq, mul_comp]
  rfl

theorem scaledCentralPencil_integral (N m₁ m₂ r : ℕ) (hp : 2 < p)
    (hN : N ≤ max (m₁ + r) (m₂ + r))
    (hsmall : 4 * max (m₁ + r) (m₂ + r) + 4 < p ^ 2) :
    ∀ i j, PolynomialPadicLower p 0 (scaledCentralPencil N m₁ m₂ r p i j) := by
  intro i j
  have hm₁ := le_max_left (m₁ + r) (m₂ + r)
  have hm₂ := le_max_right (m₁ + r) (m₂ + r)
  have hdeg : (centralPolynomial (m₁ + i.val) * centralPolynomial (m₂ + j.val)).natDegree ≤
      2 * max (m₁ + r) (m₂ + r) := by
    apply natDegree_mul_le.trans
    rw [centralPolynomial_natDegree, centralPolynomial_natDegree]
    have hi := i.isLt
    have hj := j.isLt
    omega
  have hg : SquareValuedLower p 0
      (centralPolynomial (m₁ + i.val) * centralPolynomial (m₂ + j.val)) := by
    exact (centralPolynomial_squareValued (by omega : p ≠ 2) _).mul
      (centralPolynomial_squareValued (by omega) _)
  have h := normalizedCentralFunctional_padicLower (N := N) hp hg (by omega)
  have hscaled := (PolynomialPadicLower.constant
    (prime_power_padicLower (p := p) (localPencilScale N p))).mul h
  rw [scaledCentralPencil, entry_eq_normalizedCentralFunctional]
  convert hscaled using 1
  simp [localPencilScale]

theorem normalizedCentralFunctional_C_mul (N : ℕ) (a : ℚ) (g : ℚ[X]) :
    normalizedCentralFunctional N (C a * g) = C a * normalizedCentralFunctional N g := by
  unfold normalizedCentralFunctional
  rw [mul_comp, C_comp]
  have he : C ((N.factorial : ℚ) ^ 2) * (C a * g.comp (-X)) =
      a • (C ((N.factorial : ℚ) ^ 2) * g.comp (-X)) := by rw [smul_eq_C_mul]; ring
  rw [he, map_smul, smul_eq_C_mul]

theorem normalizedCentralFunctional_sum {ι : Type*} (N : ℕ) (s : Finset ι) (g : ι → ℚ[X]) :
    normalizedCentralFunctional N (∑ i ∈ s, g i) =
      ∑ i ∈ s, normalizedCentralFunctional N (g i) := by
  simp only [normalizedCentralFunctional, Polynomial.sum_comp, mul_sum, map_sum]

theorem centralWindow_pairing (N m₁ m₂ r : ℕ) (x : Fin r → ℚ) (j : Fin r) :
    normalizedCentralFunctional N
      (centralWindowPolynomial m₁ r x * centralPolynomial (m₂ + j.val)) =
      ∑ i, C (x i) * Zeta3.Construction.entry N (m₁ + i.val) (m₂ + j.val) := by
  have he : centralWindowPolynomial m₁ r x * centralPolynomial (m₂ + j.val) =
      ∑ i : Fin r, C (x i) *
        (centralPolynomial (m₁ + i.val) * centralPolynomial (m₂ + j.val)) := by
    simp only [centralWindowPolynomial, sum_mul, mul_assoc]
  rw [he, normalizedCentralFunctional_sum]
  apply sum_congr rfl
  intro i hi
  rw [normalizedCentralFunctional_C_mul, entry_eq_normalizedCentralFunctional]

theorem scaledCentralPencil_restriction_radical (N m₁ m₂ r : ℕ) (hp : 2 < p)
    (hN : N ≤ max (m₁ + r) (m₂ + r))
    (hsmall : 4 * max (m₁ + r) (m₂ + r) + 4 < p ^ 2)
    (x : Fin r → ℚ) (hx : ∀ i, PadicLower p 0 (x i))
    (hR : ∀ a, PadicLower p 1 (∑ i, centralRestrictionMatrix N m₁ r p a i * x i)) :
    ∀ j, PolynomialPadicLower p 1
      (∑ i, C (x i) * scaledCentralPencil N m₁ m₂ r p i j) := by
  intro j
  have hp2 : p ≠ 2 := by omega
  have hm₁ := le_max_left (m₁ + r) (m₂ + r)
  have hm₂ := le_max_right (m₁ + r) (m₂ + r)
  have hF := centralWindowPolynomial_squareValued hp2 m₁ r x hx
  have hG := centralPolynomial_squareValued (p := p) hp2 (m₂ + j.val)
  have hg : SquareValuedLower p 0
      (centralWindowPolynomial m₁ r x * centralPolynomial (m₂ + j.val)) := hF.mul hG
  have hdeg : (centralWindowPolynomial m₁ r x * centralPolynomial (m₂ + j.val)).natDegree ≤
      2 * max (m₁ + r) (m₂ + r) := by
    have hmul := natDegree_mul_le (p := centralWindowPolynomial m₁ r x)
      (q := centralPolynomial (m₂ + j.val))
    rw [centralPolynomial_natDegree] at hmul
    have hFdeg := centralWindowPolynomial_natDegree_le m₁ r x
    have hj := j.isLt
    omega
  have hkernel : ∀ c ∈ maximalReflectedClasses N p,
      PolynomialPadicLower p 1
        ((centralWindowPolynomial m₁ r x * centralPolynomial (m₂ + j.val)).comp
          ((localAffine p c) ^ 2)) := by
    intro c hc
    have hFgain := centralRestrictionMatrix_kernel N m₁ r hp2 (by omega) x hx hR c hc
    have hGlocal := centralPolynomial_local_integral hp2 (j := m₂ + j.val)
      (by have := j.isLt; omega) (c : ℤ)
    rw [mul_comp]
    simpa only [comp_assoc, pow_comp, X_comp, add_zero] using hFgain.mul hGlocal
  have h := normalizedCentralFunctional_padicLower_on_kernel hp hg (by omega) hkernel
  have hscaled := (PolynomialPadicLower.constant
    (prime_power_padicLower (p := p) (localPencilScale N p))).mul h
  have he : (∑ i, C (x i) * scaledCentralPencil N m₁ m₂ r p i j) =
      C ((p : ℚ) ^ localPencilScale N p) * normalizedCentralFunctional N
        (centralWindowPolynomial m₁ r x * centralPolynomial (m₂ + j.val)) := by
    rw [centralWindow_pairing, mul_sum]
    apply sum_congr rfl
    intro i hi
    unfold scaledCentralPencil
    ring
  rw [he]
  convert hscaled using 1
  simp [localPencilScale]

end Zeta3.Arithmetic

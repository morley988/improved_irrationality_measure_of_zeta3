import Zeta5.Arithmetic.SmallPrimeEntries
import Zeta3.Arithmetic.SmallPrimeProper
import Zeta3.Construction.Determinant

/-! The actual unequal-window cubic determinant has the all-prime bound
-r(9 log_p(268n+4)+v_p(96)), where r=51n. This is a proved coefficient
valuation bound for every prime, without a large-prime hypothesis. -/
noncomputable section
namespace Zeta3.Arithmetic
open Polynomial Finset OddZeta.FourValue Zeta5.Construction
open Zeta5.Arithmetic
variable {p : ℕ} [Fact p.Prime]

theorem numeratorFunctional_scaledCentral_padicLower (N R l : ℕ)
    (hNR : N ≤ R) (hl : l ≤ 2*R-2) :
    PolynomialPadicLower p (-9*(Nat.log p (4*R+4) : ℤ)-(padicValNat p 24 : ℤ))
      (Zeta3.Construction.numeratorFunctional N (scaledCentralNumerator N l)) := by
  by_cases hlN : l ≤ N
  · exact numeratorFunctional_scaledCentral_proper_padicLower_log N l (4*R+4) hlN (by omega)
  · let k := l-N-1
    have hrep : N+k+1 = l := by dsimp [k]; omega
    rw [← hrep, numeratorFunctional_scaledCentral_high]
    exact PolynomialPadicLower.constant (centralQuotientMoment_padicLower_log N k (4*R+4)
      (by omega) (by omega))

lemma entry_central_expansion (N j k : ℕ) {d : ℕ → ℚ}
    (hd : centralPolynomial j*centralPolynomial k =
      ∑ a ∈ range (j+k+1), C (d a)*centralPolynomial a) :
    Zeta3.Construction.entry N j k = ∑ a ∈ range (j+k+1),
      C (d a)*Zeta3.Construction.numeratorFunctional N (scaledCentralNumerator N a) := by
  rw [Zeta3.Construction.entry_eq_numeratorFunctional]
  have he : C ((Nat.factorial N : ℚ)^2)*Zeta3.Construction.numeratorFunctional N (windowBasis j*windowBasis k) =
      Zeta3.Construction.numeratorFunctional N (C ((Nat.factorial N : ℚ)^2)*(windowBasis j*windowBasis k)) := by
    simpa only [Polynomial.smul_eq_C_mul] using
      ((Zeta3.Construction.numeratorFunctional N).map_smul ((Nat.factorial N : ℚ)^2) (windowBasis j*windowBasis k)).symm
  rw [he, scaledCentralProduct_expansion N j k hd, map_sum]
  apply sum_congr rfl
  intro a _
  simpa only [Polynomial.smul_eq_C_mul] using
    (Zeta3.Construction.numeratorFunctional N).map_smul (d a) (scaledCentralNumerator N a)

/-- The manuscript's actual small-prime Zeta3.Construction.entry bound, valid at every prime.
The hypothesis `N≤R` covers the chosen window parameters. -/
theorem entry_smallPrime_padicLower (N R j k : ℕ) (hNR : N ≤ R) (hj : j < R) (hk : k < R) :
    PolynomialPadicLower p (-9*(Nat.log p (4*R+4) : ℤ)-(padicValNat p 96 : ℤ))
      (Zeta3.Construction.entry N j k) := by
  obtain ⟨d, hd, he⟩ := centralProduct_expansion (p := p) j k
  rw [entry_central_expansion N j k he]
  apply PolynomialPadicLower.sum
  intro a ha
  have hT := numeratorFunctional_scaledCentral_padicLower (p := p) N R a hNR
    (by have := mem_range.mp ha; omega)
  have h := (PolynomialPadicLower.constant (hd a)).mul hT
  convert! h using 1
  rw [padicValNat_ninetySix]
  simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat]
  ring

theorem windowPencil_smallPrime_padicLower (n : ℕ) (i j : Fin (51*n)) :
    PolynomialPadicLower p (-9*(Nat.log p (268*n+4) : ℤ)-(padicValNat p 96 : ℤ))
      (Zeta3.Construction.windowPencil n i j) := by
  have h := entry_smallPrime_padicLower (p := p) (50*n) (67*n) (4*n+i.val) (16*n+j.val)
    (by omega) (by have := i.isLt; omega) (by have := j.isLt; omega)
  simpa only [Zeta3.Construction.windowPencil, show 4*(67*n)+4 = 268*n+4 by omega] using h

/-- All coefficients of the actual determinant have the logarithmic
small-prime loss times the matrix dimension. -/
theorem windowDeterminant_smallPrime_padicLower (n : ℕ) :
    PolynomialPadicLower p
      (-((51*n : ℕ) : ℤ)*(9*(Nat.log p (268*n+4) : ℤ)+(padicValNat p 96 : ℤ)))
      (Zeta3.Construction.windowDeterminant n) := by
  have h := polynomialPadicLower_det_weighted (p := p) (Zeta3.Construction.windowPencil n)
    (fun _ => 0) (fun _ => 0)
    (-9*(Nat.log p (268*n+4) : ℤ)-(padicValNat p 96 : ℤ))
    (fun i j => by simpa using windowPencil_smallPrime_padicLower (p := p) n i j)
  simp only [sum_const_zero, zero_add, Fintype.card_fin] at h
  convert! h using 1
  ring

end Zeta3.Arithmetic

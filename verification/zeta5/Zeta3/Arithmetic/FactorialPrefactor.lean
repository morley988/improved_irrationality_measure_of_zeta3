import Zeta3.Arithmetic.UpperBandAssembly

/-! Exact signed factorial charge for the two unequal factorial windows. -/
noncomputable section
namespace Zeta3.Arithmetic
open Polynomial OddZeta.FourValue Zeta5.Construction
open Zeta5.Arithmetic
variable {p : ℕ} [Fact p.Prime]

def factorialCharge (N m₁ m₂ r p : ℕ) : ℤ :=
  (∑ k : Fin r, (((2 * (m₁ + k.val)) / p : ℕ) : ℤ)) +
  (∑ k : Fin r, (((2 * (m₂ + k.val)) / p : ℕ) : ℤ)) -
    2 * r * ((N / p : ℕ) : ℤ)

theorem factorialPrefactor_padicLower (N m₁ m₂ r : ℕ)
    (hN : N < p ^ 2)
    (hR₁ : ∀ k : Fin r, 2 * (m₁ + k.val) < p ^ 2)
    (hR₂ : ∀ k : Fin r, 2 * (m₂ + k.val) < p ^ 2) :
    PadicLower p (-factorialCharge N m₁ m₂ r p)
      (Zeta3.Construction.factorialPrefactor N m₁ m₂ r) := by
  have htop : PadicLower p (2 * (r : ℤ) * ((N / p : ℕ) : ℤ))
      ((Nat.factorial N : ℚ) ^ (2 * r)) := by
    right
    rw [padicValRat.pow, padicValRat.of_nat, factorial_padicVal_of_lt_sq hN]
    push_cast
    rfl
  have hinv (a : ℕ) (ha : a < p ^ 2) :
      PadicLower p (-((a / p : ℕ) : ℤ)) ((Nat.factorial a : ℚ)⁻¹) := by
    right
    rw [padicValRat.inv, padicValRat.of_nat, factorial_padicVal_of_lt_sq ha]
  have hbot := padicLower_prod (p := p) Finset.univ
    (fun k : Fin r => (Nat.factorial (2 * (m₁ + k.val)) : ℚ)⁻¹ *
      (Nat.factorial (2 * (m₂ + k.val)) : ℚ)⁻¹)
    (fun k => -(((2 * (m₁ + k.val)) / p : ℕ) : ℤ) -
      (((2 * (m₂ + k.val)) / p : ℕ) : ℤ)) (by
      intro k hk
      simpa only [sub_eq_add_neg] using
        (hinv _ (hR₁ k)).mul (hinv _ (hR₂ k)))
  have h := htop.mul hbot
  convert h using 1 <;> first | rfl |
    (simp only [factorialCharge, Finset.sum_sub_distrib, Finset.sum_neg_distrib]; ring)

theorem windowDeterminant_padicLower_of_hankel (n : ℕ) (w : ℤ)
    (hlarge : 134 * n < p ^ 2)
    (hM : PolynomialPadicLower p w (Zeta3.Construction.hankelPencil n).det) :
    PolynomialPadicLower p (-factorialCharge (50 * n) (4 * n) (16 * n) (51 * n) p + w)
      (Zeta3.Construction.windowDeterminant n) := by
  rw [Zeta3.Construction.concrete_windowDeterminant_change_of_basis]
  exact (PolynomialPadicLower.constant
    (factorialPrefactor_padicLower (50 * n) (4 * n) (16 * n) (51 * n) (by omega)
      (fun k => by have hk := k.isLt; omega)
      (fun k => by have hk := k.isLt; omega))).mul hM

theorem windowDeterminant_upperBand_bound (n : ℕ) (hn : 0 < n) (hp : 2 < p)
    (hmp : 32 * n < p) (hpN : p ≤ 50 * n) (hN : 50 * n < 3 * p)
    (hlarge : 134 * n < p ^ 2) :
    PolynomialPadicLower p
      (-factorialCharge (50 * n) (4 * n) (16 * n) (51 * n) p -
        5 * (upperHighCount (50 * n) p : ℤ) + upperWindowSaving (50 * n) (4 * n) p +
        upperWindowSaving (50 * n) (16 * n) p -
        (min (mixedTerminalSize (50 * n) (4 * n) (16 * n) (51 * n) p)
          (51 * n - upperHighCount (50 * n) p) : ℕ))
      (Zeta3.Construction.windowDeterminant n) := by
  have hHr : upperHighCount (50 * n) p ≤ 51 * n := by unfold upperHighCount; omega
  have h := mixedMonomialPencil_upperBand_bound (50 * n) (4 * n) (16 * n) (51 * n)
    hp (by omega) (by omega) (by omega) (by omega) hpN hN (by omega) hHr
  rw [mixedMonomialPencil_concrete] at h
  have hf := windowDeterminant_padicLower_of_hankel n _ hlarge h
  convert hf using 1
  ring

end Zeta3.Arithmetic

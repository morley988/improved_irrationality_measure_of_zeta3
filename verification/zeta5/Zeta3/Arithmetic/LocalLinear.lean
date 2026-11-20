import Zeta3.Arithmetic.RestrictionPencil

/-! The nonconstant coefficients of the actual cubic pencil have valuation
at least minus epsilon. Consequently its first two reduced layers are
constant in the parameter. This uses the physical residue formula. -/
noncomputable section
namespace Zeta3.Arithmetic
open Polynomial Finset OddZeta.FourValue Zeta5.Construction Zeta3.Construction
open Zeta5.Arithmetic
variable {p : ℕ} [Fact p.Prime]

def normalizedResidueLinear (N : ℕ) (g : ℚ[X]) (i : ℕ) : ℚ[X] :=
  C ((N.factorial : ℚ) ^ 2 * g.eval ((i : ℚ) ^ 2) /
    (denominator N).derivative.eval (pole i)) * (X * C ((i : ℚ) ^ 2))

theorem normalizedResidue_coeff_pos_eq_linear (N : ℕ) (g : ℚ[X]) (i k : ℕ)
    (hk : 0 < k) :
    (normalizedResidue N g i).coeff k = (normalizedResidueLinear N g i).coeff k := by
  simp [normalizedResidue, normalizedResidueLinear, Zeta3.Construction.stieltjes,
    mul_add, coeff_C, show k ≠ 0 by omega]

theorem normalizedResidueLinear_reflected_bound {N c i : ℕ} {g : ℚ[X]} {w : ℤ}
    (hp : 2 < p) (hc : 0 < c) (hcp : 2 * c < p)
    (hi : i ∈ reflectedNodes N p c) (hsmall : 2 * N < p ^ 2)
    (hg : PadicLower p w (g.eval ((i : ℚ) ^ 2))) :
    PolynomialPadicLower p (w + 2 * ((N / p : ℕ) : ℤ) - reflectedSize N p c + 1)
      (normalizedResidueLinear N g i) := by
  have hiN := (mem_reflectedNodes.mp hi).2.1
  have hd := denominator_derivative_reflected_valuation N c i (by omega) hc hcp hi (by omega)
  have hinv : PadicLower p (-((reflectedSize N p c : ℤ) - 1))
      (((denominator N).derivative.eval (pole i))⁻¹) := by
    right
    rw [padicValRat.inv, hd]
  have hs := ((factorial_square_padicLower (by omega : N < p ^ 2)).mul hg).mul hinv
  have h := (PolynomialPadicLower.constant hs).mul (stieltjes_linear_integral (p := p) i)
  convert h using 1
  · ring
  · simp only [normalizedResidueLinear, div_eq_mul_inv]

theorem normalizedResidue_coeff_pos_global_bound {N i : ℕ} {g : ℚ[X]}
    (hp : 2 < p) (hi : 0 < i) (hiN : i ≤ N) (hsmall : 2 * N < p ^ 2)
    (hg : SquareValuedLower p 0 g) (k : ℕ) (hk : 0 < k) :
    PadicLower p (-((2 * (N % p) / p : ℕ) : ℤ)) ((normalizedResidue N g i).coeff k) := by
  have heps : 0 ≤ ((2 * (N % p) / p : ℕ) : ℤ) := Int.natCast_nonneg _
  have hgi : PadicLower p 0 (g.eval ((i : ℚ) ^ 2)) := by
    simpa only [Int.cast_natCast] using hg (i : ℤ)
  by_cases hpi : p ∣ i
  · exact (normalizedResidue_zero_class_integral hp hi hiN hpi hsmall hgi k).mono (by omega)
  · let c := reflectedLabel p i
    have hodd := (Fact.out : p.Prime).mod_two_eq_one_iff_ne_two.mpr (by omega : p ≠ 2)
    have hc : 0 < c := Nat.pos_of_ne_zero ((reflectedLabel_eq_zero p i (by omega)).not.mpr hpi)
    have hchalf : c ≤ (p - 1) / 2 := reflectedLabel_le_half p i (by omega) hodd
    have hcp : 2 * c < p := by omega
    have himem : i ∈ reflectedNodes N p c :=
      mem_reflectedNodes.mpr ⟨hi, hiN, (reflectedLabel_eq_iff p i c (by omega) hc hcp).mp rfl⟩
    have hsize := reflectedSize_le_max N p c hodd hc hchalf
    have hsize' : (reflectedSize N p c : ℤ) ≤
        2 * ((N / p : ℕ) : ℤ) + 1 + ((2 * (N % p) / p : ℕ) : ℤ) := by exact_mod_cast hsize
    rw [normalizedResidue_coeff_pos_eq_linear N g i k hk]
    exact (normalizedResidueLinear_reflected_bound hp hc hcp himem hsmall hgi k).mono (by omega)

theorem normalizedCentralFunctional_coeff_pos_bound {N : ℕ} {g : ℚ[X]}
    (hp : 2 < p) (hg : SquareValuedLower p 0 g) (hsmall : 2 * N < p ^ 2)
    (k : ℕ) (hk : 0 < k) :
    PadicLower p (-((2 * (N % p) / p : ℕ) : ℤ))
      ((normalizedCentralFunctional N g).coeff k) := by
  rw [normalizedCentralFunctional_decomposition]
  simp only [coeff_add, coeff_C, show k ≠ 0 by omega, if_false, zero_add,
    finsetSum_coeff]
  apply padicLower_sum
  intro i hi
  exact normalizedResidue_coeff_pos_global_bound hp (by omega)
    (by simpa using mem_range.mp hi) hsmall hg k hk

theorem scaledCentralPencil_coeff_pos_three (N m₁ m₂ r : ℕ) (hp : 2 < p)
    (hsmall : 2 * N < p ^ 2) (i j : Fin r) (k : ℕ) (hk : 0 < k) :
    PadicLower p 3 ((scaledCentralPencil N m₁ m₂ r p i j).coeff k) := by
  have hg : SquareValuedLower p 0
      (centralPolynomial (m₁ + i.val) * centralPolynomial (m₂ + j.val)) :=
    (centralPolynomial_squareValued (by omega : p ≠ 2) _).mul
      (centralPolynomial_squareValued (by omega) _)
  have h := (prime_power_padicLower (p := p) (localPencilScale N p)).mul
    (normalizedCentralFunctional_coeff_pos_bound hp hg hsmall k hk)
  rw [scaledCentralPencil, entry_eq_normalizedCentralFunctional, coeff_C_mul]
  convert h using 1
  simp [localPencilScale]

end Zeta3.Arithmetic

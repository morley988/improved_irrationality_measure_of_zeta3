import Zeta3.Arithmetic.ReflectedBounds
import Zeta3.Arithmetic.ZeroClass
import Zeta5.Arithmetic.UpperBandAssembly

/-! Complete cubic monomial upper-band bound. Both unequal common-root
savings and the shared quotient/atom dimension are retained. -/
noncomputable section
namespace Zeta3.Arithmetic
open Polynomial OddZeta.FourValue Zeta5.Construction Finset
open Zeta5.Arithmetic Zeta5.Arithmetic.Allocation
variable {p : ℕ} [Fact p.Prime]

def upperWindowSaving (N m p : ℕ) : ℕ :=
  if N < 2 * p then upperAffectedCount N m p else 0

theorem upperWindowSaving_eq (N m p : ℕ) (hp : 0 < p) (hpN : p ≤ N) :
    upperWindowSaving N m p =
      if N < 2 * p then min (m - 1) (N % p) + (m + N % p - p) else 0 := by
  unfold upperWindowSaving
  split_ifs with h
  · have hq : N / p = 1 := by
      have hlo : 1 ≤ N / p := (Nat.le_div_iff_mul_le hp).mpr (by simpa using hpN)
      have hhi := (Nat.div_lt_iff_lt_mul hp).mpr h
      omega
    simp [upperAffectedCount, hq]
  · rfl

theorem sum_affected_high (N m p : ℕ) (hm : 0 < m) (hpN : p ≤ N)
    (hmp : 2 * m < p) :
    (∑ c ∈ Icc 1 ((p - 1) / 2),
      if c < m then ((highReflectedNodes N p c).card : ℤ) else 0) =
      (upperAffectedCount N m p : ℤ) := by
  have hfilter : (Icc 1 ((p - 1) / 2)).filter (fun c => c < m) = Icc 1 (m - 1) := by
    ext c
    simp only [mem_filter, mem_Icc]
    omega
  have hA : (∑ c ∈ Icc 1 ((p - 1) / 2),
      if c < m then (highReflectedNodes N p c).card else 0) = upperAffectedCount N m p := by
    rw [← sum_filter, hfilter]
    exact affected_highReflectedNodes N p m hm hpN hmp
  exact_mod_cast hA

theorem sum_reflectedPenalty (N m₁ m₂ p : ℕ) (hm₁ : 0 < m₁) (hm₂ : 0 < m₂)
    (hpN : p ≤ N) (hmp₁ : 2 * m₁ < p) (hmp₂ : 2 * m₂ < p) (hodd : p % 2 = 1) :
    (∑ c ∈ Icc 1 ((p - 1) / 2), reflectedPenalty N m₁ m₂ p c) =
      5 * (upperHighCount N p : ℤ) - upperWindowSaving N m₁ p - upperWindowSaving N m₂ p := by
  have hHZ : (∑ c ∈ Icc 1 ((p - 1) / 2), ((highReflectedNodes N p c).card : ℤ)) =
      (upperHighCount N p : ℤ) := by
    exact_mod_cast total_highReflectedNodes N p hpN hodd
  by_cases hhalf : N < 2 * p
  · have he (c : ℕ) : reflectedPenalty N m₁ m₂ p c =
        5 * (highReflectedNodes N p c).card -
          (if c < m₁ then ((highReflectedNodes N p c).card : ℤ) else 0) -
          (if c < m₂ then ((highReflectedNodes N p c).card : ℤ) else 0) := by
      unfold reflectedPenalty reflectedRootGain
      simp only [if_pos hhalf, Nat.cast_add, Nat.cast_ite, Nat.cast_one, Nat.cast_zero]
      split_ifs <;> ring
    simp_rw [he]
    rw [sum_sub_distrib, sum_sub_distrib, ← mul_sum, hHZ,
      sum_affected_high N m₁ p hm₁ hpN hmp₁,
      sum_affected_high N m₂ p hm₂ hpN hmp₂]
    simp only [upperWindowSaving, if_pos hhalf]
  · simp only [reflectedPenalty, if_neg hhalf, ← mul_sum, hHZ,
      upperWindowSaving, Nat.cast_zero, sub_zero]

theorem mixedMonomialPencil_reflected_decomposition (N m₁ m₂ r p : ℕ)
    (hp : 0 < p) (hodd : p % 2 = 1) :
    mixedMonomialPencil N m₁ m₂ r =
      (mixedQuotientPencil N m₁ m₂ r +
        ∑ i ∈ zeroClassNodes N p, mixedMonomialAtom N m₁ m₂ r i) +
      ∑ c : Fin ((p - 1) / 2), mixedMonomialReflectedClass N m₁ m₂ r p (c.val + 1) := by
  rw [mixedMonomialPencil_residue_decomposition, sum_range_succ_eq_Ioc,
    sum_reflected_partition N p hp hodd, sum_fin_succ_eq_Icc]
  simp_rw [mixedMonomialReflectedClass_eq_sum]
  rw [add_assoc]

theorem mixedMonomialPencil_upperBand_bound (N m₁ m₂ r : ℕ) (hp : 2 < p)
    (hm₁ : 0 < m₁) (hm₂ : 0 < m₂) (hmp₁ : 2 * m₁ < p) (hmp₂ : 2 * m₂ < p)
    (hpN : p ≤ N) (hN : N < 3 * p) (hsmall : 2 * N < p ^ 2)
    (hHr : upperHighCount N p ≤ r) :
    PolynomialPadicLower p
      (-5 * (upperHighCount N p : ℤ) + upperWindowSaving N m₁ p + upperWindowSaving N m₂ p -
        (min (mixedTerminalSize N m₁ m₂ r p) (r - upperHighCount N p) : ℕ))
      (mixedMonomialPencil N m₁ m₂ r).det := by
  have hp0 : 0 < p := by omega
  have hodd : p % 2 = 1 := (Fact.out : p.Prime).mod_two_eq_one_iff_ne_two.mpr (by omega)
  let Z : Matrix (Fin r) (Fin r) ℚ[X] :=
    ∑ i ∈ zeroClassNodes N p, mixedMonomialAtom N m₁ m₂ r i
  let Q := mixedQuotientPencil N m₁ m₂ r + Z
  let A : Fin ((p - 1) / 2) → Matrix (Fin r) (Fin r) ℚ[X] :=
    fun c => mixedMonomialReflectedClass N m₁ m₂ r p (c.val + 1)
  let high : Fin ((p - 1) / 2) → ℕ := fun c => (highReflectedNodes N p (c.val + 1)).card
  let pen : Fin ((p - 1) / 2) → ℤ := fun c => reflectedPenalty N m₁ m₂ p (c.val + 1)
  have hhigh : (∑ c, high c) = upperHighCount N p := by
    rw [show (∑ c, high c) = ∑ c ∈ Icc 1 ((p - 1) / 2), (highReflectedNodes N p c).card from
      sum_fin_succ_eq_Icc ((p - 1) / 2) (fun c => (highReflectedNodes N p c).card)]
    exact total_highReflectedNodes N p hpN hodd
  have hpen : (∑ c, pen c) = 5 * (upperHighCount N p : ℤ) -
      upperWindowSaving N m₁ p - upperWindowSaving N m₂ p := by
    rw [show (∑ c, pen c) = ∑ c ∈ Icc 1 ((p - 1) / 2), reflectedPenalty N m₁ m₂ p c from
      sum_fin_succ_eq_Icc ((p - 1) / 2) (reflectedPenalty N m₁ m₂ p)]
    exact sum_reflectedPenalty N m₁ m₂ p hm₁ hm₂ hpN hmp₁ hmp₂ hodd
  have hZ : ∀ i j, PolynomialPadicLower p 0 (Z i j) := by
    intro i j
    simp only [Z, Matrix.sum_apply]
    apply PolynomialPadicLower.sum
    intro k hk
    obtain ⟨hkI, hpk⟩ := mem_filter.mp hk
    obtain ⟨hk0, hkN⟩ := mem_Ioc.mp hkI
    exact zero_class_atom_integral N m₁ m₂ r k hp hm₁ hm₂ hk0 hkN hpk hN hsmall i j
  have hQ : MinorLower (p := p) Q (fun a => -(min a (mixedTerminalSize N m₁ m₂ r p) : ℤ)) := by
    apply minorLower_add_integral _ Z _ hZ
    intro a rows cols
    simpa only [Nat.cast_min] using mixedQuotientPencil_minor_padicLower N m₁ m₂ r a hp rows cols
  have hA (c : Fin ((p - 1) / 2)) := reflected_class_dual_bounds N m₁ m₂ r (c.val + 1)
    hp (by omega) (by have hc := c.isLt; omega) hpN hN hsmall
  have h := shared_dimension_matrix_bound (p := p) Q A pen high (mixedTerminalSize N m₁ m₂ r p)
    (by rw [hhigh]; exact hHr) hQ (fun c => (hA c).1) (fun c => (hA c).2)
  have heq : Q + ∑ c, A c = mixedMonomialPencil N m₁ m₂ r :=
    (mixedMonomialPencil_reflected_decomposition N m₁ m₂ r p hp0 hodd).symm
  rw [heq, hhigh, hpen] at h
  convert h using 1
  ring

end Zeta3.Arithmetic

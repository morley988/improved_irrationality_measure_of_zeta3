import Zeta3.Arithmetic.LowPairs
import Zeta5.Arithmetic.IntegralMatrices

/-! Uniform dual minor bounds for the actual cubic reflected classes.
The gain from each window is retained only in the upper half band. -/
noncomputable section
namespace Zeta3.Arithmetic
open Polynomial OddZeta.FourValue Zeta5.Construction
open Zeta5.Arithmetic Zeta5.Arithmetic.Allocation
variable {p : ℕ} [Fact p.Prime]

theorem low_reflected_class_integral (N m₁ m₂ r c : ℕ) (hp : 2 < p)
    (hc : 0 < c) (hcp : 2 * c < p) (hpN : p ≤ N) (hsmall : 2 * N < p ^ 2)
    (hhigh : (highReflectedNodes N p c).card = 0) :
    ∀ k l : Fin r, PolynomialPadicLower p 0 (mixedMonomialReflectedClass N m₁ m₂ r p c k l) := by
  have hh := highReflectedNodes_card_add_two N p c hc hcp hpN
  have hcard : (reflectedNodes N p c).card = 2 := by
    rw [reflectedNodes_card N p c hc hcp]
    omega
  have hall : (reflectedNodes N p c).filter (fun i => i ≤ p) = reflectedNodes N p c := by
    apply Finset.filter_eq_self.mpr
    intro i hi
    by_contra h
    have hmem : i ∈ highReflectedNodes N p c := Finset.mem_filter.mpr ⟨hi, by omega⟩
    have hpos := Finset.card_pos.mpr ⟨i, hmem⟩
    omega
  have hset : reflectedNodes N p c = {c, p - c} := by
    rw [← hall]
    exact reflected_low_nodes N p c hc hcp hpN
  have hpair := low_reflected_pair_integral N m₁ m₂ r c hp hc hcp (by omega) hsmall hcard
  intro k l
  rw [mixedMonomialReflectedClass_eq_sum, hset,
    Finset.sum_pair (by omega : c ≠ p - c), Matrix.add_apply]
  exact hpair k l

def reflectedPenalty (N m₁ m₂ p c : ℕ) : ℤ :=
  (if N < 2 * p then 5 - (reflectedRootGain m₁ m₂ c : ℤ) else 5) *
    (highReflectedNodes N p c).card

theorem reflected_class_dual_bounds (N m₁ m₂ r c : ℕ) (hp : 2 < p)
    (hc : 0 < c) (hcp : 2 * c < p) (hpN : p ≤ N) (hN : N < 3 * p)
    (hsmall : 2 * N < p ^ 2) :
    MinorLower (p := p) (mixedMonomialReflectedClass N m₁ m₂ r p c)
      (fun _ => -reflectedPenalty N m₁ m₂ p c) ∧
    MinorLower (p := p) (mixedMonomialReflectedClass N m₁ m₂ r p c)
      (fun k => -(k : ℤ) -
        (reflectedPenalty N m₁ m₂ p c - (highReflectedNodes N p c).card)) := by
  by_cases hz : (highReflectedNodes N p c).card = 0
  · have h := integral_matrix_minorLower (p := p) (mixedMonomialReflectedClass N m₁ m₂ r p c)
      (low_reflected_class_integral N m₁ m₂ r c hp hc hcp hpN hsmall hz)
    constructor
    · simpa [reflectedPenalty, hz] using h
    · intro k rows cols
      exact (h k rows cols).mono (by simp [reflectedPenalty, hz])
  have hpos : 1 ≤ (highReflectedNodes N p c).card := by omega
  by_cases hhalf : N < 2 * p
  · have htwo := highReflectedNodes_card_le_two N p c hc hcp hpN hhalf
    have h := gained_reflected_class_minorLower N m₁ m₂ r c hp hc hcp hpN hsmall
    constructor
    · intro k rows cols
      apply (h k rows cols).mono
      have he := gainedClusterCost_le_with_deficit_all (highReflectedNodes N p c).card
        (reflectedRootGain m₁ m₂ c) k hpos htwo (reflectedRootGain_le_two _ _ _)
      have hd := Int.natCast_nonneg ((highReflectedNodes N p c).card - k)
      simp only [reflectedPenalty, if_pos hhalf]
      linarith
    · intro k rows cols
      apply (h k rows cols).mono
      have he := gainedClusterCost_le_with_deficit_all (highReflectedNodes N p c).card
        (reflectedRootGain m₁ m₂ c) k hpos htwo (reflectedRootGain_le_two _ _ _)
      have hd : ((highReflectedNodes N p c).card : ℤ) - k ≤
          ((highReflectedNodes N p c).card - k : ℕ) := by omega
      simp only [reflectedPenalty, if_pos hhalf]
      linarith
  · have hfour := highReflectedNodes_card_le_four N p c hc hcp hpN hN
    have h := reflected_class_minorLower N m₁ m₂ r c hp hc hcp hpN hsmall
    constructor
    · intro k rows cols
      apply (h k rows cols).mono
      have he := clusterCost_le_with_deficit_all (highReflectedNodes N p c).card k hpos hfour
      have hd := Int.natCast_nonneg ((highReflectedNodes N p c).card - k)
      simp only [reflectedPenalty, if_neg hhalf]
      linarith
    · intro k rows cols
      apply (h k rows cols).mono
      have he := clusterCost_le_with_deficit_all (highReflectedNodes N p c).card k hpos hfour
      have hd : ((highReflectedNodes N p c).card : ℤ) - k ≤
          ((highReflectedNodes N p c).card - k : ℕ) := by omega
      simp only [reflectedPenalty, if_neg hhalf]
      linarith

end Zeta3.Arithmetic

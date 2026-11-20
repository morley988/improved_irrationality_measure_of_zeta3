import Zeta3.Arithmetic.FinsetAtomicMinors
import Zeta3.Arithmetic.MixedResidues
import Zeta3.Arithmetic.ClusterCosts
import Zeta5.Arithmetic.ReflectedMinors

/-! Sharp cubic reflected-class minor bounds with unequal common roots. -/
noncomputable section
namespace Zeta3.Arithmetic
open Polynomial OddZeta.FourValue Zeta5.Construction
open Zeta5.Arithmetic Zeta5.Arithmetic.Allocation
variable {p : ℕ} [Fact p.Prime]

def mixedMonomialReflectedClass (N m₁ m₂ r p c : ℕ) : Matrix (Fin r) (Fin r) ℚ[X] :=
  finsetAtomicMatrix (reflectedNodes N p c) (mixedMonomialAtomWeight N m₁ m₂) pole r

theorem mixedMonomialReflectedClass_eq_sum (N m₁ m₂ r p c : ℕ) :
    mixedMonomialReflectedClass N m₁ m₂ r p c =
      ∑ i ∈ reflectedNodes N p c, mixedMonomialAtom N m₁ m₂ r i := by
  funext k l
  simp only [mixedMonomialReflectedClass, finsetAtomicMatrix, mixedMonomialAtom, Matrix.sum_apply]

theorem highReflectedNodes_card_le_two (N p c : ℕ) (hc : 0 < c)
    (hcp : 2 * c < p) (hpN : p ≤ N) (hN : N < 2 * p) :
    (highReflectedNodes N p c).card ≤ 2 := by
  have hp : 0 < p := by omega
  have hq : N / p < 2 := (Nat.div_lt_iff_lt_mul hp).mpr (by omega)
  have hh := highReflectedNodes_card_add_two N p c hc hcp hpN
  unfold reflectedSize at hh
  split_ifs at hh <;> omega

theorem gained_reflected_class_minorLower (N m₁ m₂ r c : ℕ) (hp : 2 < p)
    (hc : 0 < c) (hcp : 2 * c < p) (hpN : p ≤ N) (hsmall : 2 * N < p ^ 2) :
    MinorLower (p := p) (mixedMonomialReflectedClass N m₁ m₂ r p c)
      (fun k => -gainedClusterCost (highReflectedNodes N p c).card
        (reflectedRootGain m₁ m₂ c) k) := by
  have h := finset_atomic_minorLower (reflectedNodes N p c)
    (highReflectedNodes N p c) (Finset.filter_subset _ _)
    (mixedMonomialAtomWeight N m₁ m₂) pole r (pole c)
    ((reflectedRootGain m₁ m₂ c : ℤ) - (highReflectedNodes N p c).card - 1)
    (pole_padicIntegral c) (fun i hi => reflected_pole_congr hc hcp hi) (by
      intro i hi
      have hiN := (mem_reflectedNodes.mp hi).2.1
      simpa only [highReflectedNodes, Finset.mem_filter, hi, true_and] using
        mixed_reflected_atomWeight_bound N m₁ m₂ c i hp hc hcp hpN hi (by omega))
  intro k rows cols
  convert h k rows cols using 1 <;> first | rfl | (unfold gainedClusterCost; ring)

theorem reflected_class_minorLower (N m₁ m₂ r c : ℕ) (hp : 2 < p)
    (hc : 0 < c) (hcp : 2 * c < p) (hpN : p ≤ N) (hsmall : 2 * N < p ^ 2) :
    MinorLower (p := p) (mixedMonomialReflectedClass N m₁ m₂ r p c)
      (fun k => -clusterCost (highReflectedNodes N p c).card k) := by
  intro k rows cols
  apply (gained_reflected_class_minorLower N m₁ m₂ r c hp hc hcp hpN hsmall k rows cols).mono
  unfold clusterCost gainedClusterCost
  nlinarith [mul_nonneg (Int.natCast_nonneg k)
    (Int.natCast_nonneg (reflectedRootGain m₁ m₂ c))]

end Zeta3.Arithmetic

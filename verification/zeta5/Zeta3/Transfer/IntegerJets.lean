import Zeta5.Endpoint.IntegerPolynomial
import Mathlib.Algebra.Polynomial.HasseDeriv
import Mathlib.Tactic.NormNum

/-!
# Integer-polynomial jets at rational points

This is a generic algebraic component of the quantitative transfer argument.
The Hasse derivative is an integer polynomial and represents the ordinary
derivative divided by its factorial.  Its rational evaluation therefore has
the degree-dependent denominator bound needed even when the original
polynomial vanishes at the rational point.

No analytic estimate or numerical certificate is assumed in this file.
-/

noncomputable section
namespace Zeta3.Transfer
open Polynomial

theorem one_le_abs_int_cast {z : ℤ} (hz : z ≠ 0) :
    (1 : ℝ) ≤ |(z : ℝ)| := by
  have hzpos : (0 : ℤ) < |z| := abs_pos.mpr hz
  have hzge : (1 : ℤ) ≤ |z| := by omega
  exact_mod_cast hzge

/-- A nonzero rational value of an integer polynomial cannot be smaller than
the reciprocal of its clearing denominator. The exponent may be any proved
upper bound for the degree. -/
theorem one_le_scaled_abs_eval (P : ℤ[X]) (p : ℤ) (q d : ℕ)
    (hq : 0 < q) (hdeg : P.natDegree ≤ d)
    (hnonzero : P.eval₂ (Int.castRingHom ℝ) ((p : ℝ) / q) ≠ 0) :
    1 ≤ (q : ℝ) ^ d * |P.eval₂ (Int.castRingHom ℝ) ((p : ℝ) / q)| := by
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  have hqZ : (q : ℤ) ≠ 0 := by exact_mod_cast hq.ne'
  have hcast := Zeta5.Endpoint.scaledEvalInt_cast P p (q : ℤ) d hqZ hdeg
  simp only [Int.cast_natCast] at hcast
  have hzR : (Zeta5.Endpoint.scaledEvalInt P p (q : ℤ) d : ℝ) ≠ 0 := by
    rw [hcast]
    exact mul_ne_zero (pow_ne_zero _ hqR.ne') hnonzero
  have hz : Zeta5.Endpoint.scaledEvalInt P p (q : ℤ) d ≠ 0 := by
    intro h
    apply hzR
    simp [h]
  have h := one_le_abs_int_cast hz
  rw [hcast, abs_mul, abs_of_pos (pow_pos hqR _)] at h
  exact h

theorem inv_pow_le_abs_eval (P : ℤ[X]) (p : ℤ) (q d : ℕ)
    (hq : 0 < q) (hdeg : P.natDegree ≤ d)
    (hnonzero : P.eval₂ (Int.castRingHom ℝ) ((p : ℝ) / q) ≠ 0) :
    1 / (q : ℝ) ^ d ≤ |P.eval₂ (Int.castRingHom ℝ) ((p : ℝ) / q)| := by
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  apply (div_le_iff₀ (pow_pos hqR d)).mpr
  simpa only [mul_comm] using one_le_scaled_abs_eval P p q d hq hdeg hnonzero

/-- The sharp clearing exponent for the order-`m` Hasse derivative is
`natDegree P - m`, including the zero-polynomial degree convention. -/
theorem one_le_scaled_abs_hasse_eval (P : ℤ[X]) (p : ℤ) (q m : ℕ)
    (hq : 0 < q)
    (hnonzero : (hasseDeriv m P).eval₂ (Int.castRingHom ℝ) ((p : ℝ) / q) ≠ 0) :
    1 ≤ (q : ℝ) ^ (P.natDegree - m) *
      |(hasseDeriv m P).eval₂ (Int.castRingHom ℝ) ((p : ℝ) / q)| := by
  exact one_le_scaled_abs_eval (hasseDeriv m P) p q (P.natDegree - m) hq
    (natDegree_hasseDeriv_le P m) hnonzero

/-- A coarser but useful version, which clears every bounded-order jet with
the same degree exponent. The discarded factor is asymptotically harmless. -/
theorem one_le_degree_scaled_abs_hasse_eval (P : ℤ[X]) (p : ℤ) (q m d : ℕ)
    (hq : 0 < q) (hdeg : P.natDegree ≤ d)
    (hnonzero : (hasseDeriv m P).eval₂ (Int.castRingHom ℝ) ((p : ℝ) / q) ≠ 0) :
    1 ≤ (q : ℝ) ^ d *
      |(hasseDeriv m P).eval₂ (Int.castRingHom ℝ) ((p : ℝ) / q)| := by
  apply one_le_scaled_abs_eval (hasseDeriv m P) p q d hq _ hnonzero
  exact (natDegree_hasseDeriv_le P m).trans ((Nat.sub_le _ _).trans hdeg)

/-- The quantitative argument needs a uniformly bounded nonzero jet at each
rational point. A bounded rational-root multiplicity theorem supplies this
property. This definition does not assert it for any concrete polynomial. -/
def HasBoundedRationalJets (P : ℕ → ℤ[X]) (B : ℕ) : Prop :=
  ∀ (n : ℕ) (p : ℤ) (q : ℕ), 0 < q → ∃ m ≤ B,
    (hasseDeriv m (P n)).eval₂ (Int.castRingHom ℝ) ((p : ℝ) / (q : ℝ)) ≠ 0

end Zeta3.Transfer

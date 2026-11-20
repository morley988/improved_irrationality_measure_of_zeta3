import Zeta3.Construction.HankelExtension

/-!
# Polynomial-adjoint divisibility for the least Hankel kernel polynomial

This is the abstract algebraic implication used in the cubic Pearson proof.
Adjointness and the operator degree bounds are explicit hypotheses.  The
nondegeneracy conclusion is derived from minimality using the proved Hankel
kernel theorem; it is not an additional nonsingularity assumption.
-/

noncomputable section
namespace Zeta3.Construction.Hankel
open Polynomial
variable {K : Type*} [Field K]

theorem minimal_kernel_dvd_of_adjoint
    (L : K[X] →ₗ[K] K) (m M d : ℕ) (p : K[X])
    (hp : p.Monic) (hsize : p.natDegree ≤ m + 1)
    (hpann : ∀ j ≤ m, L (p * X ^ j) = 0)
    (hmin : ∀ f : K[X], f.Monic → (∀ j ≤ m, L (f * X ^ j) = 0) →
      p.natDegree ≤ f.natDegree)
    (hann : ∀ j ≤ M, L (p * X ^ j) = 0)
    (S Sstar : K[X] → K[X])
    (hadjoint : ∀ f g, L (S f * g) = L (f * Sstar g))
    (hS : (S p).natDegree ≤ p.natDegree + d)
    (hSstar : ∀ k < p.natDegree, (Sstar (X ^ k)).natDegree ≤ k + d)
    (hbudget : p.natDegree + d - 1 ≤ M) : p ∣ S p := by
  by_cases hp1 : p = 1
  · simp [hp1]
  apply (Polynomial.modByMonic_eq_zero_iff_dvd hp).mp
  apply minimal_kernel_leading_nondegenerate L m p hp hsize hpann hmin
    ((S p) %ₘ p) (Polynomial.natDegree_modByMonic_lt (S p) hp hp1)
  intro k hk
  have hSp : L (S p * X ^ k) = 0 := by
    rw [hadjoint]
    apply recurrence_relations_span L p M hann
    have hd := hSstar k hk
    omega
  have hquot : ((S p) /ₘ p).natDegree ≤ d := by
    rw [Polynomial.natDegree_divByMonic (S p) hp]
    omega
  have hzero : L (p * (((S p) /ₘ p) * X ^ k)) = 0 := by
    apply recurrence_relations_span L p M hann
    have hd := Polynomial.natDegree_mul_le (p := (S p) /ₘ p) (q := X ^ k)
    simp only [Polynomial.natDegree_X_pow] at hd
    omega
  have heq := congrArg (fun f : K[X] => L (f * X ^ k))
    (Polynomial.modByMonic_add_div (S p) p)
  rw [add_mul, map_add, mul_assoc, hzero, add_zero, hSp] at heq
  exact heq

end Zeta3.Construction.Hankel

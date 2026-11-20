import Mathlib.Algebra.Polynomial.RingDivision
import Mathlib.Algebra.Polynomial.Degree.Support
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.LinearAlgebra.Dimension.Finite
import Mathlib.Tactic.Push
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

/-!
# Truncated Hankel algebra reused from the four-value project

Source: morley988/four-odd-zeta, commit
fd23dd59e5d638c9684eb2d7776fb51e8b427b55 (MIT).
This extraction preserves the mathematical proofs, changes the namespace and
imports, and does not import the four-value numerical certificate interfaces.
The monomial recurrence propagation is proved directly by monic division.
-/

noncomputable section
namespace Zeta3.Construction.Hankel
open Polynomial

variable {K : Type*} [Field K]

/-- Extend a truncated recurrence by first reducing every test polynomial
modulo its monic annihilator. -/
def recurrenceExtension (L : K[X] →ₗ[K] K) (p : K[X]) : K[X] →ₗ[K] K :=
  L.comp (Polynomial.modByMonicHom p)

@[simp] theorem recurrenceExtension_apply (L : K[X] →ₗ[K] K) (p q : K[X]) :
    recurrenceExtension L p q = L (q %ₘ p) := rfl

/-- The extended functional is annihilated on every multiple of `p`. -/
theorem recurrenceExtension_annihilates (L : K[X] →ₗ[K] K)
    {p : K[X]} (hp : p.Monic) (q : K[X]) :
    recurrenceExtension L p (p * q) = 0 := by
  rw [recurrenceExtension_apply, (Polynomial.modByMonic_eq_zero_iff_dvd hp).2
    (dvd_mul_right p q), map_zero]

/-- Monomial recurrence relations imply all relations in the same degree
range by linearity. -/
theorem recurrence_relations_span (L : K[X] →ₗ[K] K) (p : K[X]) (b : ℕ)
    (h : ∀ j ≤ b, L (p * X ^ j) = 0) (q : K[X])
    (hq : q.natDegree ≤ b) : L (p * q) = 0 := by
  conv_lhs => rw [q.as_sum_range_C_mul_X_pow]
  rw [Finset.mul_sum, map_sum]
  apply Finset.sum_eq_zero
  intro i hi
  have hi' : i ≤ b := by
    have := Finset.mem_range.mp hi
    omega
  rw [show p * (C (q.coeff i) * X ^ i) =
    q.coeff i • (p * X ^ i) by simp [Polynomial.smul_eq_C_mul, mul_left_comm]]
  simp [h i hi']

/-- Agreement extends through `b + degree p`, including a degree-zero
annihilator. This accounts for the root-at-infinity degree loss. -/
theorem recurrenceExtension_agrees (L : K[X] →ₗ[K] K)
    {p : K[X]} (hp : p.Monic) (b : ℕ)
    (h : ∀ j ≤ b, L (p * X ^ j) = 0) (q : K[X])
    (hq : q.natDegree ≤ b + p.natDegree) :
    recurrenceExtension L p q = L q := by
  have hdiv : (q /ₘ p).natDegree ≤ b := by
    rw [Polynomial.natDegree_divByMonic q hp]
    omega
  have hz := recurrence_relations_span L p b h (q /ₘ p) hdiv
  have heq := congrArg L (Polynomial.modByMonic_add_div q p)
  simpa [recurrenceExtension_apply, map_add, hz] using heq

/-- The exact degree of agreement appearing in the paper's apolar extension. -/
theorem recurrenceExtension_hankel_agrees (L : K[X] →ₗ[K] K)
    {p : K[X]} (hp : p.Monic) (m r : ℕ)
    (h : ∀ j ≤ 2 * m - r, L (p * X ^ j) = 0)
    (q : K[X]) (hq : q.natDegree ≤ 2 * m - r + p.natDegree) :
    recurrenceExtension L p q = L q :=
  recurrenceExtension_agrees L hp (2 * m - r) h q hq

/-- For a degree-zero monic annihilator the extension is the zero functional. -/
theorem recurrenceExtension_one (L : K[X] →ₗ[K] K) :
    recurrenceExtension L (1 : K[X]) = 0 := by
  ext q
  simp [recurrenceExtension_apply]


/-- A Hankel matrix with rows and columns from zero through m. -/
def momentHankel (L : K[X] →ₗ[K] K) (m : ℕ) :
    Matrix (Fin (m + 1)) (Fin (m + 1)) K :=
  fun i j => L (X ^ (i.val + j.val))

def HasShortAnnihilator (L : K[X] →ₗ[K] K) (m r : ℕ) : Prop :=
  ∃ p : K[X], p.Monic ∧ p.natDegree ≤ r ∧
    ∀ j ≤ 2 * m - r, L (p * X ^ j) = 0

/-- Once p annihilates the functional, degree(p) consecutive monomial tests
suffice; polynomial division proves this without a finite-quotient axiom. -/
theorem annihilator_propagates_monomial_tests (L : K[X] →ₗ[K] K)
    {p : K[X]} (hp : p.Monic) (hann : ∀ f : K[X], L (p * f) = 0)
    (A : K[X]) (hinit : ∀ j < p.natDegree, L (A * X ^ j) = 0) :
    ∀ j : ℕ, L (A * X ^ j) = 0 := by
  intro j
  by_cases hp1 : p = 1
  · simpa [hp1] using hann (A * X ^ j)
  · have hrem := Polynomial.natDegree_modByMonic_lt (X ^ j : K[X]) hp hp1
    have hdpos : 0 < p.natDegree := by omega
    have hz := recurrence_relations_span L A (p.natDegree - 1)
      (fun k hk => hinit k (by omega)) ((X ^ j : K[X]) %ₘ p) (by omega)
    have hdiv : L (A * (p * ((X ^ j : K[X]) /ₘ p))) = 0 := by
      rw [show A * (p * ((X ^ j : K[X]) /ₘ p)) =
        p * (A * ((X ^ j : K[X]) /ₘ p)) by ring]
      exact hann _
    have heq := congrArg (fun f : K[X] => L (A * f))
      (Polynomial.modByMonic_add_div (X ^ j : K[X]) p)
    simpa [mul_add, map_add, hz, hdiv] using heq.symm

end Zeta3.Construction.Hankel


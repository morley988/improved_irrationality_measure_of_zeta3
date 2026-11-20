import Zeta3.Construction.HankelAdjoint
import Mathlib.Algebra.Polynomial.Roots

/-!
# The cubic Pearson polynomials and their integer-root propagation

The concrete degree-nine polynomials A and B are defined here.  Given the two
polynomial divisibilities furnished by the adjoint argument, every root of
the even lifted kernel polynomial is an integer.  This module proves that
root-propagation implication, without postulating a classification of finite
Pearson solutions.

The remaining connection to the actual cubic functional is explicit: one
must prove its Pearson identity, the relevant adjoints and degree budgets,
and then instantiate the divisibility hypotheses below.
-/

noncomputable section
namespace Zeta3.Construction.Pearson
open Polynomial
variable {K : Type*} [Field K] [CharZero K]

def polynomialA (N m₁ m₂ : ℕ) : K[X] :=
  (X - 1) ^ 6 * (X - C (m₁ : K)) * (X - C (m₂ : K)) * (X + C (N : K))

def polynomialB (N m₁ m₂ : ℕ) : K[X] :=
  (X + 1) ^ 6 * (X + C (m₁ : K)) * (X + C (m₂ : K)) * (X - C (N : K))

theorem polynomialB_reflection (N m₁ m₂ : ℕ) :
    (polynomialB N m₁ m₂ : K[X]).comp (-X) = -polynomialA N m₁ m₂ := by
  simp only [polynomialB, polynomialA, mul_comp, pow_comp, add_comp, sub_comp,
    X_comp, C_comp, one_comp]
  ring

theorem polynomialB_monic (N m₁ m₂ : ℕ) : (polynomialB N m₁ m₂ : K[X]).Monic := by
  apply Monic.mul
  · apply Monic.mul
    · apply Monic.mul
      · simpa using (monic_X_add_C (1 : K)).pow 6
      · exact monic_X_add_C _
    · exact monic_X_add_C _
  · exact monic_X_sub_C _

theorem polynomialB_natDegree (N m₁ m₂ : ℕ) :
    (polynomialB N m₁ m₂ : K[X]).natDegree = 9 := by
  have h₁ : ((X + 1 : K[X]) ^ 6).Monic := by
    simpa using (monic_X_add_C (1 : K)).pow 6
  have hdeg : ((X + 1 : K[X]) ^ 6).natDegree = 6 := by
    simpa only [C_1] using Polynomial.natDegree_pow_X_add_C 6 (1 : K)
  rw [polynomialB, ((h₁.mul (monic_X_add_C _)).mul (monic_X_add_C _)).natDegree_mul
    (monic_X_sub_C _), (h₁.mul (monic_X_add_C _)).natDegree_mul (monic_X_add_C _),
    h₁.natDegree_mul (monic_X_add_C _)]
  rw [hdeg, natDegree_X_add_C, natDegree_X_add_C, natDegree_X_sub_C]

def evenPart (f : K[X]) : K[X] := C ((2 : K)⁻¹) * (f + f.comp (-X))

def operatorD (B f : K[X]) : K[X] :=
  B * (f.comp (X + 1) - f) - B.comp (-X) * (f.comp (X - 1) - f)

def operatorQ (B f : K[X]) : K[X] := evenPart (B * f.comp (X + 1))

def operatorR (B f : K[X]) : K[X] := X * operatorD B f

theorem even_eval_neg {P : K[X]} (hEven : P.comp (-X) = P) (x : K) :
    P.eval (-x) = P.eval x := by
  have h := congrArg (Polynomial.eval x) hEven
  simpa using h

theorem eval_eq_zero_of_dvd {P Q : K[X]} (hPQ : P ∣ Q) {a : K}
    (hP : P.eval a = 0) : Q.eval a = 0 := by
  obtain ⟨S, rfl⟩ := hPQ
  simp [hP]

/-- The two adjoint divisibilities force the forward transport identity at
every nonzero root of an even polynomial. -/
theorem transport_at_nonzero_root (B P : K[X])
    (hEven : P.comp (-X) = P)
    (hQ : P ∣ operatorQ B P) (hR : P ∣ operatorR B P)
    {a : K} (hP : P.eval a = 0) (ha : a ≠ 0) :
    B.eval a * P.eval (a + 1) = 0 := by
  have hq := eval_eq_zero_of_dvd hQ hP
  have hr := eval_eq_zero_of_dvd hR hP
  have he : P.eval (-a + 1) = P.eval (a - 1) := by
    rw [show -a + 1 = -(a - 1) by ring, even_eval_neg hEven]
  simp only [operatorQ, evenPart, eval_mul, eval_C, eval_add, eval_comp,
    eval_neg, eval_X, eval_one] at hq
  rw [he] at hq
  have hsum : B.eval a * P.eval (a + 1) + B.eval (-a) * P.eval (a - 1) = 0 :=
    (mul_eq_zero.mp hq).resolve_left (inv_ne_zero (by norm_num))
  simp only [operatorR, operatorD, eval_mul, eval_X, eval_sub, eval_comp,
    eval_add, eval_one, eval_neg, hP, sub_zero] at hr
  have hdiff : B.eval a * P.eval (a + 1) - B.eval (-a) * P.eval (a - 1) = 0 :=
    (mul_eq_zero.mp hr).resolve_left ha
  have htwo : (2 : K) * (B.eval a * P.eval (a + 1)) = 0 := by
    linear_combination hsum + hdiff
  exact (mul_eq_zero.mp htwo).resolve_left (by norm_num)

theorem polynomialB_roots_integer (N m₁ m₂ : ℕ) {a : K}
    (hB : (polynomialB N m₁ m₂ : K[X]).eval a = 0) :
    ∃ z : ℤ, a = (z : K) := by
  simp only [polynomialB, eval_mul, eval_pow, eval_add, eval_sub, eval_X,
    eval_one, eval_C] at hB
  rcases mul_eq_zero.mp hB with hB | hB
  · rcases mul_eq_zero.mp hB with hB | hB
    · rcases mul_eq_zero.mp hB with hB | hB
      · have ha : a + 1 = 0 := (pow_eq_zero_iff (by decide : (6 : ℕ) ≠ 0)).mp hB
        refine ⟨-1, ?_⟩
        push_cast
        linear_combination ha
      · refine ⟨-(m₁ : ℤ), ?_⟩
        push_cast
        linear_combination hB
    · refine ⟨-(m₂ : ℤ), ?_⟩
      push_cast
      linear_combination hB
  · refine ⟨(N : ℤ), ?_⟩
    push_cast
    exact sub_eq_zero.mp hB

/-- A nonintegral root could propagate indefinitely; finiteness of the root
set rules this out. -/
theorem roots_integer_of_forward_transport (B P : K[X]) (hP : P ≠ 0)
    (hB : ∀ a : K, B.eval a = 0 → ∃ z : ℤ, a = (z : K))
    (hstep : ∀ a : K, P.eval a = 0 → a ≠ 0 → B.eval a * P.eval (a + 1) = 0)
    {a : K} (ha : P.eval a = 0) : ∃ z : ℤ, a = (z : K) := by
  by_contra hnot
  have hnotn (n : ℕ) : ¬∃ z : ℤ, a + (n : K) = (z : K) := by
    rintro ⟨z, hz⟩
    apply hnot
    refine ⟨z - (n : ℤ), ?_⟩
    push_cast
    linear_combination hz
  have hnzero (n : ℕ) : a + (n : K) ≠ 0 := by
    intro hz
    exact hnotn n ⟨0, by simpa using hz⟩
  have hBnonzero (n : ℕ) : B.eval (a + (n : K)) ≠ 0 := by
    intro hz
    exact hnotn n (hB _ hz)
  have hall : ∀ n : ℕ, P.eval (a + (n : K)) = 0 := by
    intro n
    induction n with
    | zero => simpa using ha
    | succ n ih =>
      have h := (mul_eq_zero.mp (hstep _ ih (hnzero n))).resolve_left (hBnonzero n)
      simpa only [Nat.cast_add, Nat.cast_one, add_assoc] using h
  have hinj : Function.Injective (fun n : ℕ => a + (n : K)) := by
    intro n m hnm
    exact_mod_cast add_left_cancel hnm
  have hinf : Set.Infinite {x : K | P.IsRoot x} :=
    (Set.infinite_range_of_injective hinj).mono (by
      rintro x ⟨n, rfl⟩
      exact hall n)
  exact hP (Polynomial.eq_zero_of_infinite_isRoot P hinf)

theorem cubic_kernel_roots_integer (N m₁ m₂ : ℕ) (P : K[X]) (hP : P ≠ 0)
    (hEven : P.comp (-X) = P)
    (hQ : P ∣ operatorQ (polynomialB N m₁ m₂) P)
    (hR : P ∣ operatorR (polynomialB N m₁ m₂) P)
    {a : K} (ha : P.eval a = 0) : ∃ z : ℤ, a = (z : K) := by
  apply roots_integer_of_forward_transport (polynomialB N m₁ m₂) P hP
    (fun a ha => polynomialB_roots_integer N m₁ m₂ ha)
    (fun a ha hane => transport_at_nonzero_root _ _ hEven hQ hR ha hane) ha

end Zeta3.Construction.Pearson

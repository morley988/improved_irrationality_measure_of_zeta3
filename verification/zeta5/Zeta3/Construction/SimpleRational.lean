import Zeta3.Construction.RationalLaurent
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.LinearAlgebra.Finsupp.LinearCombination

/-!
# Polynomials and finitely many simple integer poles

The representation map into the actual rational-function field is proved
injective using its local Laurent residues. Thus prescribing a polynomial
functional and values on integer simple poles is consistent. The linear
left inverse used later is only an extension outside this proved subspace;
all Pearson applications are proved to belong to the subspace.
-/

noncomputable section
namespace Zeta3.Construction.Rational
open Polynomial
open scoped RatFunc
variable {K : Type*} [Field K] [CharZero K]

def polynomialEmbedding : K[X] →ₗ[K] RatFunc K :=
  (IsScalarTower.toAlgHom K K[X] (RatFunc K)).toLinearMap

@[simp] theorem polynomialEmbedding_apply (p : K[X]) :
    polynomialEmbedding p = algebraMap K[X] (RatFunc K) p := rfl

def simpleRepresentation : (K[X] × (ℤ →₀ K)) →ₗ[K] RatFunc K :=
  polynomialEmbedding.comp (LinearMap.fst K K[X] (ℤ →₀ K)) +
    (Finsupp.linearCombination K (fun i : ℤ => rationalPole (i : K) 1)).comp
      (LinearMap.snd K K[X] (ℤ →₀ K))

theorem simpleRepresentation_apply (p : K[X]) (r : ℤ →₀ K) :
    simpleRepresentation (p, r) = algebraMap K[X] (RatFunc K) p +
      ∑ i ∈ r.support, r i • rationalPole (i : K) 1 := by
  rfl

@[simp] theorem simpleRepresentation_polynomial (p : K[X]) :
    simpleRepresentation (p, (0 : ℤ →₀ K)) = algebraMap K[X] (RatFunc K) p := by
  rw [simpleRepresentation_apply]
  simp

@[simp] theorem simpleRepresentation_pole (i : ℤ) (a : K) :
    simpleRepresentation (0, Finsupp.single i a) = a • rationalPole (i : K) 1 := by
  simp [simpleRepresentation, Finsupp.linearCombination_single]

theorem rationalCoefficientAt_integer_pole (i j : ℤ) :
    rationalCoefficientAt (i : K) (-1) (rationalPole (j : K) 1) =
      if i = j then 1 else 0 := by
  by_cases hij : i = j
  · subst j
    simp [rationalCoefficientAt_pole_self]
  · rw [if_neg hij]
    apply rationalCoefficientAt_pole_other_neg (j : K) (i : K) 1 _ (-1) (by norm_num)
    exact_mod_cast hij

theorem simpleRepresentation_residue (p : K[X]) (r : ℤ →₀ K) (i : ℤ) :
    rationalCoefficientAt (i : K) (-1) (simpleRepresentation (p, r)) = r i := by
  rw [simpleRepresentation_apply, map_add,
    rationalCoefficientAt_polynomial_neg _ _ _ (by norm_num), zero_add, map_sum]
  simp_rw [map_smul, rationalCoefficientAt_integer_pole, smul_eq_mul, mul_ite,
    mul_one, mul_zero]
  rw [Finset.sum_ite_eq]
  by_cases hi : i ∈ r.support
  · simp [hi]
  · simp [hi, Finsupp.notMem_support_iff.mp hi]

theorem simpleRepresentation_injective :
    Function.Injective (simpleRepresentation (K := K)) := by
  rintro ⟨p, r⟩ ⟨q, s⟩ h
  have hrs : r = s := by
    ext i
    have hi := congrArg (rationalCoefficientAt (i : K) (-1)) h
    simpa only [simpleRepresentation_residue] using hi
  subst s
  have hpq : p = q := by
    rw [simpleRepresentation_apply, simpleRepresentation_apply, add_left_inj] at h
    exact RatFunc.algebraMap_injective K h
  subst q
  rfl

def simpleRational : Submodule K (RatFunc K) := (simpleRepresentation (K := K)).range

theorem polynomial_mem_simpleRational (p : K[X]) :
    algebraMap K[X] (RatFunc K) p ∈ simpleRational :=
  ⟨(p, 0), simpleRepresentation_polynomial p⟩

theorem pole_mem_simpleRational (i : ℤ) : rationalPole (i : K) 1 ∈ simpleRational := by
  exact ⟨(0, Finsupp.single i 1), by simp⟩

theorem simpleRational_induction {f : RatFunc K} (hf : f ∈ simpleRational)
    (P : RatFunc K → Prop)
    (hpoly : ∀ p : K[X], P (algebraMap K[X] (RatFunc K) p))
    (hpole : ∀ i : ℤ, P (rationalPole (i : K) 1))
    (hadd : ∀ f g, P f → P g → P (f + g))
    (hsmul : ∀ (c : K) (f : RatFunc K), P f → P (c • f)) : P f := by
  obtain ⟨⟨p, r⟩, rfl⟩ := hf
  rw [simpleRepresentation_apply]
  apply hadd _ _ (hpoly p)
  apply Finset.sum_induction
  · exact hadd
  · simpa using hpoly 0
  · intro i hi
    exact hsmul (r i) _ (hpole i)

theorem rationalShift_mem_simpleRational {f : RatFunc K} (hf : f ∈ simpleRational) (a : ℤ) :
    rationalShift (a : K) f ∈ simpleRational := by
  apply simpleRational_induction hf (fun f => rationalShift (a : K) f ∈ simpleRational)
  · intro p
    rw [rationalShift_polynomial]
    exact polynomial_mem_simpleRational _
  · intro i
    rw [rationalPole_shift, ← Int.cast_sub]
    exact pole_mem_simpleRational _
  · intro f g hf hg
    rw [map_add]
    exact simpleRational.add_mem hf hg
  · intro c f hf
    change (rationalShift (a : K)).toLinearMap (c • f) ∈ simpleRational
    rw [map_smul]
    exact simpleRational.smul_mem c hf

theorem polynomial_mul_pole (p : K[X]) (a : K) :
    algebraMap K[X] (RatFunc K) p * rationalPole a 1 =
      algebraMap K[X] (RatFunc K) (p /ₘ (X - C a)) + p.eval a • rationalPole a 1 := by
  have h := congrArg (algebraMap K[X] (RatFunc K)) (modByMonic_add_div p (X - C a))
  rw [modByMonic_X_sub_C_eq_C_eval, map_add, map_mul, RatFunc.algebraMap_C] at h
  have hn : algebraMap K[X] (RatFunc K) (X - C a) ≠ 0 :=
    RatFunc.algebraMap_ne_zero (monic_X_sub_C a).ne_zero
  rw [rationalPole, pow_one, RatFunc.smul_eq_C_mul]
  rw [← h]
  field_simp
  ring

theorem polynomial_mul_mem_simpleRational (p : K[X]) {f : RatFunc K}
    (hf : f ∈ simpleRational) : algebraMap K[X] (RatFunc K) p * f ∈ simpleRational := by
  apply simpleRational_induction hf
    (fun f => algebraMap K[X] (RatFunc K) p * f ∈ simpleRational)
  · intro q
    rw [← map_mul]
    exact polynomial_mem_simpleRational _
  · intro i
    rw [polynomial_mul_pole]
    exact simpleRational.add_mem (polynomial_mem_simpleRational _)
      (simpleRational.smul_mem _ (pole_mem_simpleRational i))
  · intro f g hf hg
    rw [mul_add]
    exact simpleRational.add_mem hf hg
  · intro c f hf
    rw [mul_smul_comm]
    exact simpleRational.smul_mem c hf

end Zeta3.Construction.Rational

import Zeta3.Construction.SimpleRational

/-! Reflection x↦−x on actual rational functions and its action on simple poles. -/

noncomputable section
namespace Zeta3.Construction.Rational
open Polynomial
open scoped RatFunc
variable {K : Type*} [Field K] [CharZero K]

def polynomialReflection : K[X] →ₐ[K] K[X] where
  toRingHom := Polynomial.compRingHom (-X)
  commutes' c := by simp

@[simp] theorem polynomialReflection_apply (p : K[X]) :
    polynomialReflection p = p.comp (-X) := rfl

theorem polynomialReflection_injective : Function.Injective (polynomialReflection (K := K)) := by
  apply Function.LeftInverse.injective (g := polynomialReflection)
  intro p
  exact Polynomial.comp_neg_X_comp_neg_X p

def rationalReflection : RatFunc K →ₐ[K] RatFunc K :=
  RatFunc.mapAlgHom polynomialReflection
    (nonZeroDivisors_le_comap_nonZeroDivisors_of_injective _ polynomialReflection_injective)

theorem rationalReflection_fraction (p q : K[X]) :
    rationalReflection (algebraMap K[X] (RatFunc K) p / algebraMap K[X] (RatFunc K) q) =
      algebraMap K[X] (RatFunc K) (p.comp (-X)) /
        algebraMap K[X] (RatFunc K) (q.comp (-X)) := by
  exact RatFunc.map_apply_div polynomialReflection
    (nonZeroDivisors_le_comap_nonZeroDivisors_of_injective _ polynomialReflection_injective) p q

theorem rationalReflection_polynomial (p : K[X]) :
    rationalReflection (algebraMap K[X] (RatFunc K) p) =
      algebraMap K[X] (RatFunc K) (p.comp (-X)) := by
  simpa using rationalReflection_fraction p 1

theorem rationalReflection_pole (a : K) :
    rationalReflection (rationalPole a 1) = -rationalPole (-a) 1 := by
  rw [rationalPole_fraction, rationalReflection_fraction, rationalPole_fraction]
  have hp : (X - C a : K[X]).comp (-X) = -(X - C (-a)) := by simp; ring
  simp only [pow_one, one_comp, map_one, one_div, hp, map_neg, inv_neg]

theorem rationalReflection_involution (f : RatFunc K) :
    rationalReflection (rationalReflection f) = f := by
  induction f using RatFunc.induction_on' with
  | _pq p q hq =>
    simp only [RatFunc.mk_eq_div, rationalReflection_fraction, comp_neg_X_comp_neg_X]

theorem rationalReflection_mem_simpleRational {f : RatFunc K} (hf : f ∈ simpleRational) :
    rationalReflection f ∈ simpleRational := by
  apply simpleRational_induction hf (fun f => rationalReflection f ∈ simpleRational)
  · intro p
    rw [rationalReflection_polynomial]
    exact polynomial_mem_simpleRational _
  · intro i
    rw [rationalReflection_pole, ← Int.cast_neg]
    exact simpleRational.neg_mem (pole_mem_simpleRational (-i))
  · intro f g hf hg
    rw [map_add]
    exact simpleRational.add_mem hf hg
  · intro c f hf
    change rationalReflection.toLinearMap (c • f) ∈ simpleRational
    rw [map_smul]
    exact simpleRational.smul_mem c hf

end Zeta3.Construction.Rational

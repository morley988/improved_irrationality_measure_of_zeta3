import Zeta3.Construction.RationalReflection
import Zeta5.Construction.PartialFractions
import Mathlib.Data.Int.Interval

/-!
# Centered products for the cubic Pearson weight

The centered-product identities are reused from the MIT-licensed four-value
project, commit fd23dd59e5d638c9684eb2d7776fb51e8b427b55. They are generic
polynomial identities; no four-value parameters or certificates are imported.
-/

noncomputable section
namespace Zeta3.Construction.Rational
open Polynomial
variable {K : Type*} [Field K] [CharZero K]

def centeredDenominator : ℕ → K[X]
  | 0 => X
  | a+1 => centeredDenominator a * (X-C ((a+1:ℕ):K)) * (X+C ((a+1:ℕ):K))

@[simp] theorem centeredDenominator_zero : centeredDenominator (K:=K) 0=X := rfl

theorem centeredDenominator_succ (a : ℕ) :
    centeredDenominator (K:=K) (a+1)=centeredDenominator a *
      (X^2-C (((a+1:ℕ):K)^2)) := by
  rw [centeredDenominator]
  simp only [map_pow]
  ring

theorem centeredDenominator_product (a : ℕ) :
    centeredDenominator (K:=K) a = X*∏ j ∈ Finset.range a,
      (X^2-C (((j+1:ℕ):K)^2)) := by
  induction a with
  | zero => simp
  | succ a ih => rw [centeredDenominator_succ,ih,Finset.prod_range_succ,mul_assoc]

theorem centeredDenominator_monic (a : ℕ) : (centeredDenominator (K:=K) a).Monic := by
  induction a with
  | zero => exact Polynomial.monic_X
  | succ a ih =>
      exact (ih.mul (Polynomial.monic_X_sub_C _)).mul (Polynomial.monic_X_add_C _)

theorem centeredDenominator_degree (a : ℕ) :
    (centeredDenominator (K:=K) a).natDegree=2*a+1 := by
  induction a with
  | zero => simp
  | succ a ih =>
      rw [centeredDenominator,
        ((centeredDenominator_monic a).mul (Polynomial.monic_X_sub_C _)).natDegree_mul
          (Polynomial.monic_X_add_C _),
        (centeredDenominator_monic a).natDegree_mul (Polynomial.monic_X_sub_C _),
        Polynomial.natDegree_X_sub_C,Polynomial.natDegree_X_add_C,ih]
      omega

/-- The centered product contains each integer root from -a to a once. -/
theorem centeredDenominator_eval_zero_iff (a : ℕ) (x : K) :
    (centeredDenominator a).eval x=0 ↔
      ∃ j : ℤ, -(a:ℤ)≤j ∧ j≤a ∧ x=(j:K) := by
  induction a with
  | zero =>
      simp only [centeredDenominator_zero,Polynomial.eval_X,Nat.cast_zero,Int.cast_zero,neg_zero]
      constructor
      · intro h
        exact ⟨0,le_refl _,le_refl _,by simpa using h⟩
      · rintro ⟨j,hj,hj',rfl⟩
        have : j=0 := le_antisymm hj' hj
        simp [this]
  | succ a ih =>
      rw [centeredDenominator,Polynomial.eval_mul,Polynomial.eval_mul,
        Polynomial.eval_sub,Polynomial.eval_add,Polynomial.eval_X,Polynomial.eval_C,
        mul_eq_zero,mul_eq_zero,ih]
      constructor
      · rintro ((⟨j,hj,hj',hx⟩ | hp) | hn)
        · exact ⟨j,by omega,by omega,hx⟩
        · refine ⟨a+1,by omega,by omega,?_⟩
          simpa using sub_eq_zero.mp hp
        · refine ⟨-(a+1),by omega,by omega,?_⟩
          simpa using eq_neg_of_add_eq_zero_left hn
      · rintro ⟨j,hj,hj',hx⟩
        by_cases hlow : -(a:ℤ)≤j
        · by_cases hhigh : j≤a
          · exact Or.inl (Or.inl ⟨j,hlow,hhigh,hx⟩)
          · have hjtop : j=(a:ℤ)+1 := by omega
            left; right
            rw [hx,hjtop]
            simp
        · have hjbottom : j=-((a:ℤ)+1) := by omega
          right
          rw [hx,hjbottom]
          simp


/-- Exact cancellation of consecutive centered products. -/
theorem centeredDenominator_shift (a : ℕ) :
    (centeredDenominator (K:=K) a).comp (X+1)*(X-C (a:K)) =
      centeredDenominator a*(X+C ((a+1:ℕ):K)) := by
  induction a with
  | zero => simp [mul_comm]
  | succ a ih =>
      simp only [centeredDenominator,Polynomial.mul_comp,Polynomial.sub_comp,
        Polynomial.add_comp,Polynomial.X_comp,Polynomial.C_comp]
      have h₁ : (X+1-C ((a+1:ℕ):K):K[X])=X-C (a:K) := by
        simp [Nat.cast_add,map_add] <;> ring
      have h₂ : (X+1+C ((a+1:ℕ):K):K[X])=X+C ((a+1+1:ℕ):K) := by
        simp [Nat.cast_add,map_add] <;> ring
      rw [h₁,h₂]
      calc
        _ = ((centeredDenominator a).comp (X+1)*(X-C (a:K))) *
            (X-C ((a+1:ℕ):K))*(X+C ((a+1+1:ℕ):K)) := by ring
        _ = _ := by rw [ih]; ring


def poleWindow (b : ℕ) : Finset ℤ := Finset.Icc (-(b:ℤ)) b

def integerRootProduct (S : Finset ℤ) : K[X] := ∏ j ∈ S, (X-C (j:K))

theorem integerRootProduct_monic (S : Finset ℤ) : (integerRootProduct (K:=K) S).Monic :=
  Polynomial.monic_prod_of_monic _ _ (fun j _ => Polynomial.monic_X_sub_C _)

theorem integerRootProduct_degree (S : Finset ℤ) :
    (integerRootProduct (K:=K) S).natDegree=S.card := by
  rw [integerRootProduct,Polynomial.natDegree_prod_of_monic S (fun (j:ℤ) => X-C (j:K))
    (fun j _ => Polynomial.monic_X_sub_C (j:K))]
  simp only [Polynomial.natDegree_X_sub_C]
  simp

theorem integerRootProduct_eval_zero_iff (S : Finset ℤ) (x : K) :
    (integerRootProduct S).eval x=0 ↔ ∃ j ∈ S, x=(j:K) := by
  simp [integerRootProduct,Polynomial.eval_prod,Finset.prod_eq_zero_iff,sub_eq_zero]

theorem centeredDenominator_integerProduct (b : ℕ) :
    centeredDenominator (K:=K) b=integerRootProduct (poleWindow b) := by
  apply Polynomial.eq_of_monic_of_dvd_of_natDegree_le
    (integerRootProduct_monic _) (centeredDenominator_monic b)
  · apply Finset.prod_dvd_of_coprime
    · intro i hi j hj hij
      exact Polynomial.pairwise_coprime_X_sub_C (Int.cast_injective) hij
    · intro j hj
      apply Polynomial.dvd_iff_isRoot.mpr
      apply (centeredDenominator_eval_zero_iff b (j:K)).mpr
      exact ⟨j,(Finset.mem_Icc.mp hj).1,(Finset.mem_Icc.mp hj).2,rfl⟩
  · rw [centeredDenominator_degree,integerRootProduct_degree,poleWindow,Int.card_Icc]
    omega


end Zeta3.Construction.Rational


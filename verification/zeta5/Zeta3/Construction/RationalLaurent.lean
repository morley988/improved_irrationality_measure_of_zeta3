import Mathlib.RingTheory.LaurentSeries
import Mathlib.RingTheory.PowerSeries.WellKnown
import Mathlib.Algebra.Polynomial.Taylor
import Zeta3.Construction.PearsonDegrees

/-!
# Rational shifts and local Laurent coefficients

Extracted from the MIT-licensed four-value project, commit
fd23dd59e5d638c9684eb2d7776fb51e8b427b55. The proofs below are algebraic
identities of actual rational functions and Laurent series. No numerical
certificate or four-value theorem is imported.
-/

noncomputable section
namespace Zeta3.Construction.Rational
open Polynomial
open scoped LaurentSeries PowerSeries RatFunc
variable {K : Type*} [Field K] [CharZero K]

def rationalShift (a : K) : RatFunc K →ₐ[K] RatFunc K :=
  RatFunc.mapAlgHom (Polynomial.taylorAlgHom a)
    (nonZeroDivisors_le_comap_nonZeroDivisors_of_injective _ (Polynomial.taylor_injective a))

theorem rationalShift_fraction (a : K) (p q : K[X]) :
    rationalShift a (algebraMap K[X] (RatFunc K) p / algebraMap K[X] (RatFunc K) q) =
      algebraMap K[X] (RatFunc K) (p.taylor a) / algebraMap K[X] (RatFunc K) (q.taylor a) := by
  exact RatFunc.map_apply_div (Polynomial.taylorAlgHom a)
    (nonZeroDivisors_le_comap_nonZeroDivisors_of_injective _ (Polynomial.taylor_injective a)) p q

theorem rationalShift_polynomial (a : K) (p : K[X]) :
    rationalShift a (algebraMap K[X] (RatFunc K) p) =
      algebraMap K[X] (RatFunc K) (p.taylor a) := by
  simpa using rationalShift_fraction a p 1

theorem rationalShift_add (a b : K) (f : RatFunc K) :
    rationalShift a (rationalShift b f)=rationalShift (a+b) f := by
  induction f using RatFunc.induction_on' with
  | _pq p q hq => simp only [RatFunc.mk_eq_div,rationalShift_fraction,Polynomial.taylor_taylor]

theorem rationalShift_zero (f : RatFunc K) : rationalShift 0 f=f := by
  induction f using RatFunc.induction_on' with
  | _pq p q hq => simp only [RatFunc.mk_eq_div,rationalShift_fraction,Polynomial.taylor_zero]

def rationalLaurentAt (a : K) : RatFunc K →+* K⸨X⸩ :=
  (algebraMap (RatFunc K) K⸨X⸩).comp (rationalShift a).toRingHom

theorem rationalLaurentAt_C (a c : K) :
    rationalLaurentAt a (RatFunc.C c)=HahnSeries.C c := by
  change algebraMap (RatFunc K) K⸨X⸩ (rationalShift a (algebraMap K[X] (RatFunc K) (C c))) = _
  rw [rationalShift_polynomial,Polynomial.taylor_C]
  rw [← IsScalarTower.algebraMap_apply K[X] (RatFunc K) K⸨X⸩]
  simp

def rationalCoefficientAt (a : K) (j : ℤ) : RatFunc K →ₗ[K] K where
  toFun f := (rationalLaurentAt a f).coeff j
  map_add' f g := by simp
  map_smul' c f := by
    change (rationalLaurentAt a (c • f)).coeff j = c * (rationalLaurentAt a f).coeff j
    rw [RatFunc.smul_eq_C_mul,map_mul,rationalLaurentAt_C]
    simp

theorem rationalCoefficientAt_shift (a b : K) (j : ℤ) (f : RatFunc K) :
    rationalCoefficientAt a j (rationalShift b f)=rationalCoefficientAt (a+b) j f := by
  change (algebraMap (RatFunc K) K⸨X⸩ (rationalShift a (rationalShift b f))).coeff j = _
  rw [rationalShift_add]
  rfl


theorem rationalLaurentAt_polynomial (a : K) (p : K[X]) :
    rationalLaurentAt a (algebraMap K[X] (RatFunc K) p) =
      (((p.taylor a : K[X]) : K⟦X⟧) : K⸨X⸩) := by
  change algebraMap (RatFunc K) K⸨X⸩ (rationalShift a (algebraMap K[X] (RatFunc K) p)) = _
  rw [rationalShift_polynomial]
  rw [← IsScalarTower.algebraMap_apply K[X] (RatFunc K) K⸨X⸩]
  rfl

theorem rationalCoefficientAt_polynomial (a : K) (p : K[X]) (h : ℕ) :
    rationalCoefficientAt a h (algebraMap K[X] (RatFunc K) p)=(p.taylor a).coeff h := by
  change (rationalLaurentAt a _).coeff _ = _
  rw [rationalLaurentAt_polynomial,LaurentSeries.coeff_coe_powerSeries,Polynomial.coeff_coe]

theorem rationalCoefficientAt_polynomial_neg (a : K) (p : K[X]) (j : ℤ) (hj : j<0) :
    rationalCoefficientAt a j (algebraMap K[X] (RatFunc K) p)=0 := by
  change (rationalLaurentAt a _).coeff _ = _
  rw [rationalLaurentAt_polynomial,PowerSeries.coeff_coe,if_pos hj]

theorem powerSeries_inv_coe (f : K⟦X⟧) (hf : PowerSeries.constantCoeff f≠0) :
    ((f⁻¹ : K⟦X⟧) : K⸨X⸩)=(f:K⸨X⸩)⁻¹ := by
  apply eq_inv_of_mul_eq_one_left
  rw [← PowerSeries.coe_mul,PowerSeries.inv_mul_cancel f hf,PowerSeries.coe_one]

theorem rationalLaurentAt_regular (a : K) (p q : K[X]) (hq : q.eval a≠0) :
    rationalLaurentAt a (algebraMap K[X] (RatFunc K) p / algebraMap K[X] (RatFunc K) q) =
      (((((p.taylor a : K[X]):K⟦X⟧) * (((q.taylor a : K[X]):K⟦X⟧)⁻¹)) : K⟦X⟧) : K⸨X⸩) := by
  rw [map_div₀,rationalLaurentAt_polynomial,rationalLaurentAt_polynomial,PowerSeries.coe_mul,
    powerSeries_inv_coe]
  · rfl
  · simpa [Polynomial.constantCoeff_coe,Polynomial.taylor_coeff_zero] using hq

theorem rationalCoefficientAt_regular_neg (a : K) (p q : K[X]) (hq : q.eval a≠0)
    (j : ℤ) (hj : j<0) :
    rationalCoefficientAt a j (algebraMap K[X] (RatFunc K) p / algebraMap K[X] (RatFunc K) q)=0 := by
  change (rationalLaurentAt a _).coeff _ = _
  rw [rationalLaurentAt_regular a p q hq,PowerSeries.coeff_coe,if_pos hj]

def rationalPole (a : K) (k : ℕ) : RatFunc K :=
  (algebraMap K[X] (RatFunc K) (X-C a))⁻¹ ^ k

theorem rationalPole_fraction (a : K) (k : ℕ) :
    rationalPole a k=algebraMap K[X] (RatFunc K) 1 /
      algebraMap K[X] (RatFunc K) ((X-C a)^k) := by
  simp [rationalPole,div_eq_mul_inv,inv_pow]

theorem rationalPole_shift (a t : K) (k : ℕ) :
    rationalShift t (rationalPole a k)=rationalPole (a-t) k := by
  rw [rationalPole_fraction,rationalShift_fraction,rationalPole_fraction]
  simp only [map_one,Polynomial.taylor_one,Polynomial.C_1,Polynomial.taylor_pow,
    map_sub,Polynomial.taylor_X,Polynomial.taylor_C]
  congr 3 <;> ring

theorem rationalLaurentAt_pole_self (a : K) (k : ℕ) :
    rationalLaurentAt a (rationalPole a k)=HahnSeries.single (-(k:ℤ)) (1:K) := by
  change algebraMap (RatFunc K) K⸨X⸩ (rationalShift a (rationalPole a k)) = _
  rw [rationalPole_shift,sub_self]
  simp only [rationalPole,map_zero,sub_zero,map_pow,map_inv₀,RatFunc.algebraMap_X,
    RatFunc.coe_X,HahnSeries.inv_single,inv_one]
  simp

theorem rationalCoefficientAt_pole_self (a : K) (k : ℕ) (j : ℤ) :
    rationalCoefficientAt a j (rationalPole a k)=if j=-(k:ℤ) then 1 else 0 := by
  change (rationalLaurentAt a _).coeff _ = _
  rw [rationalLaurentAt_pole_self,HahnSeries.coeff_single]
  split_ifs <;> rfl

theorem rationalCoefficientAt_pole_other_neg (a t : K) (k : ℕ) (hat : t≠a)
    (j : ℤ) (hj : j<0) : rationalCoefficientAt t j (rationalPole a k)=0 := by
  rw [rationalPole_fraction]
  apply rationalCoefficientAt_regular_neg t 1 ((X-C a)^k) _ j hj
  simpa using pow_ne_zero k (sub_ne_zero.mpr hat)


theorem rationalCoefficientAt_boundary_factor (a : K) (p q : K[X])
    (hq : q.eval a≠0) (r h : ℕ) (hh : h<r) :
    rationalCoefficientAt a h (algebraMap K[X] (RatFunc K) ((X-C a)^r*p) /
      algebraMap K[X] (RatFunc K) q)=0 := by
  change (rationalLaurentAt a _).coeff _ = _
  rw [rationalLaurentAt_regular a _ q hq,LaurentSeries.coeff_coe_powerSeries]
  simp only [Polynomial.taylor_mul,Polynomial.taylor_pow,map_sub,
    Polynomial.taylor_X,Polynomial.taylor_C,add_sub_cancel_right,
    Polynomial.coe_mul,Polynomial.coe_pow,Polynomial.coe_X]
  rw [mul_assoc,PowerSeries.coeff_X_pow_mul',if_neg (by omega)]


theorem rationalCoefficientAt_zero_pole (a : K) (h : ℕ) :
    rationalCoefficientAt 0 h (rationalPole a 1) = -(a ^ (h + 1))⁻¹ := by
  by_cases ha : a = 0
  · subst a
    rw [rationalCoefficientAt_pole_self]
    simp
  · let u : Kˣ := Units.mk0 a ha
    have hcc : PowerSeries.constantCoeff (PowerSeries.X - PowerSeries.C a) ≠ 0 := by
      simpa using neg_ne_zero.mpr ha
    have hinv : (PowerSeries.X - PowerSeries.C a : K⟦X⟧)⁻¹ =
        -PowerSeries.invUnitsSub u := by
      apply (PowerSeries.inv_eq_iff_mul_eq_one hcc).mpr
      calc
        _ = PowerSeries.invUnitsSub u * (PowerSeries.C a - PowerSeries.X) := by ring
        _ = 1 := PowerSeries.invUnitsSub_mul_sub u
    rw [rationalPole_fraction]
    change (rationalLaurentAt 0 _).coeff (h : ℤ) = _
    rw [show (X - C a : K[X]) ^ 1 = X - C a by simp,
      rationalLaurentAt_regular 0 1 (X - C a) (by simpa using neg_ne_zero.mpr ha),
      LaurentSeries.coeff_coe_powerSeries]
    simp only [Polynomial.taylor_zero, Polynomial.coe_one, one_mul,
      Polynomial.coe_sub, Polynomial.coe_X, Polynomial.coe_C, hinv, map_neg,
      PowerSeries.coeff_invUnitsSub]
    simp [u, one_divp]

end Zeta3.Construction.Rational


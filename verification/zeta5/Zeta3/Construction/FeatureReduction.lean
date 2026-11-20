import Zeta3.Construction.FeatureResidue

/-! Exact coefficientwise reduction of polynomials over the rational local
integers. These definitions retain the actual rational coefficients. -/

noncomputable section
namespace Zeta3.Construction.Features
open Polynomial Zeta5.Arithmetic OddZeta.FourValue
variable {p : ℕ} [Fact p.Prime]

def integralPolynomial (P : ℚ[X]) (hP : PolynomialPadicLower p 0 P) :
    (padicIntegralSubring p)[X] :=
  P.toSubring (padicIntegralSubring p) (polynomial_coeffs_mem_padicIntegralSubring hP)

@[simp] theorem integralPolynomial_coeff (P : ℚ[X]) (hP : PolynomialPadicLower p 0 P)
    (j : ℕ) : (integralPolynomial P hP).coeff j = ⟨P.coeff j, hP j⟩ := by
  apply Subtype.ext
  exact coeff_toSubring P _ _

@[simp] theorem integralPolynomial_map (P : ℚ[X]) (hP : PolynomialPadicLower p 0 P) :
    (integralPolynomial P hP).map (padicIntegralSubring p).subtype = P :=
  map_toSubring P _ _

def reducePolynomial (P : ℚ[X]) (hP : PolynomialPadicLower p 0 P) :
    (PadicResidueField p)[X] :=
  (integralPolynomial P hP).map (padicReduction p)

theorem reducePolynomial_congr {P Q : ℚ[X]} (h : P = Q)
    (hP : PolynomialPadicLower p 0 P) (hQ : PolynomialPadicLower p 0 Q) :
    reducePolynomial P hP = reducePolynomial Q hQ := by
  subst Q
  rfl

@[simp] theorem reducePolynomial_coeff (P : ℚ[X]) (hP : PolynomialPadicLower p 0 P)
    (j : ℕ) : (reducePolynomial P hP).coeff j = padicReduction p ⟨P.coeff j, hP j⟩ := by
  simp [reducePolynomial]

theorem reducePolynomial_eq_iff (P Q : ℚ[X])
    (hP : PolynomialPadicLower p 0 P) (hQ : PolynomialPadicLower p 0 Q) :
    reducePolynomial P hP = reducePolynomial Q hQ ↔ PolynomialPadicLower p 1 (P-Q) := by
  rw [Polynomial.ext_iff]
  constructor
  · intro h j
    have hh := sub_eq_zero.mpr (h j)
    simp only [reducePolynomial_coeff, ← map_sub] at hh
    have := (padicReduction_eq_zero _).mp hh
    change PadicLower p 1 (P.coeff j - Q.coeff j) at this
    simpa only [coeff_sub] using this
  · intro h j
    apply sub_eq_zero.mp
    rw [reducePolynomial_coeff, reducePolynomial_coeff, ← map_sub]
    apply (padicReduction_eq_zero _).mpr
    change PadicLower p 1 (P.coeff j - Q.coeff j)
    simpa only [coeff_sub] using h j

theorem reducePolynomial_mul (P Q : ℚ[X])
    (hP : PolynomialPadicLower p 0 P) (hQ : PolynomialPadicLower p 0 Q)
    (hPQ : PolynomialPadicLower p 0 (P*Q)) :
    reducePolynomial (P*Q) hPQ = reducePolynomial P hP * reducePolynomial Q hQ := by
  have he : integralPolynomial (P*Q) hPQ = integralPolynomial P hP * integralPolynomial Q hQ := by
    apply Polynomial.map_injective (padicIntegralSubring p).subtype Subtype.val_injective
    simp only [Polynomial.map_mul, integralPolynomial_map]
  simp only [reducePolynomial, he, Polynomial.map_mul]

theorem reducePolynomial_C (a : ℚ) (ha : PadicLower p 0 a) :
    reducePolynomial (C a) (PolynomialPadicLower.constant ha) =
      C (padicReduction p ⟨a,ha⟩) := by
  have he : integralPolynomial (C a) (PolynomialPadicLower.constant ha) = C ⟨a,ha⟩ := by
    apply Polynomial.map_injective (padicIntegralSubring p).subtype Subtype.val_injective
    simp
  simp only [reducePolynomial, he, map_C]

theorem reducePolynomial_C_nat (n : ℕ)
    (h : PolynomialPadicLower p 0 (C (n:ℚ))) :
    reducePolynomial (C (n:ℚ)) h = C (n : PadicResidueField p) := by
  rw [reducePolynomial_C (n:ℚ) (padicLower_nat n)]
  have he : (⟨(n:ℚ), padicLower_nat (p:=p) n⟩ : padicIntegralSubring p) = n := by
    apply Subtype.ext
    rfl
  rw [he, map_natCast]

theorem reducePolynomial_integer_map (P : ℤ[X])
    (hP : PolynomialPadicLower p 0 (P.map (Int.castRingHom ℚ))) :
    reducePolynomial (P.map (Int.castRingHom ℚ)) hP =
      P.map (Int.castRingHom (PadicResidueField p)) := by
  ext j
  have he : (⟨(P.map (Int.castRingHom ℚ)).coeff j, hP j⟩ : padicIntegralSubring p) =
      (P.coeff j : padicIntegralSubring p) := by
    apply Subtype.ext
    simp
  rw [reducePolynomial_coeff, he, coeff_map]
  exact map_intCast _ _

theorem reducePolynomial_monic (P : ℚ[X]) (hP : PolynomialPadicLower p 0 P)
    (hmonic : P.Monic) : (reducePolynomial P hP).Monic := by
  apply Polynomial.Monic.map
  exact (monic_toSubring P _ _).mpr hmonic

theorem reducePolynomial_natDegree_of_monic (P : ℚ[X])
    (hP : PolynomialPadicLower p 0 P) (hmonic : P.Monic) :
    (reducePolynomial P hP).natDegree = P.natDegree := by
  have hm : (integralPolynomial P hP).Monic := (monic_toSubring P _ _).mpr hmonic
  rw [reducePolynomial, hm.natDegree_map]
  exact natDegree_toSubring P _ _

theorem reducePolynomial_eval_int (P : ℚ[X]) (hP : PolynomialPadicLower p 0 P)
    (a : ℤ) :
    (reducePolynomial P hP).eval (a : PadicResidueField p) =
      padicReduction p ⟨P.eval (a:ℚ), hP.eval_integral (padicLower_int a)⟩ := by
  have he : (integralPolynomial P hP).eval (a : padicIntegralSubring p) =
      (⟨P.eval (a:ℚ), hP.eval_integral (padicLower_int a)⟩ : padicIntegralSubring p) := by
    apply Subtype.ext
    change (padicIntegralSubring p).subtype ((integralPolynomial P hP).eval _) = _
    rw [← eval₂_at_apply, ← eval_map, integralPolynomial_map]
    rfl
  rw [reducePolynomial, ← map_intCast (padicReduction p) a, eval_map_apply]
  exact congrArg (padicReduction p) he

end Zeta3.Construction.Features

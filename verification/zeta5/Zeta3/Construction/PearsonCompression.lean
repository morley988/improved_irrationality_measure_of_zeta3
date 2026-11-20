import Zeta3.Construction.PearsonDegrees
import Zeta3.Construction.HankelAdjoint

/-!
# Squared-coordinate compression and the least-kernel argument

The operators here are the actual cubic polynomial formulas.  The theorem
about a functional retains its Pearson and reflection identities explicitly;
it does not assert them for the rational-moment functional.
-/

noncomputable section
namespace Zeta3.Construction.Pearson
open Polynomial
variable {K : Type*} [Field K] [CharZero K]

theorem squareLift_squareCompress (f : K[X]) (hf : f.comp (-X) = f) :
    squareLift (squareCompress f) = f := by
  have heq : squareLift (squareCompress f) = expand K 2 (contract 2 f) := by
    simp only [squareLift, squareCompress, comp_assoc, neg_comp, X_comp, neg_neg]
    rfl
  rw [heq]
  ext n
  rw [coeff_expand (by norm_num : 0 < 2)]
  split_ifs with hn
  · rw [coeff_contract (by norm_num), Nat.div_mul_cancel hn]
  · have hodd : n = 2 * (n / 2) + 1 := by omega
    rw [hodd, even_polynomial_odd_coeff_zero f hf]

theorem squareCompress_squareLift (p : K[X]) : squareCompress (squareLift p) = p := by
  have heq : squareLift p = expand K 2 (p.comp (-X)) := by
    simp [squareLift, expand_eq_comp_X_pow, comp_assoc]
  rw [squareCompress, heq,
    contract_expand (R := K) (p := 2) (f := p.comp (-X)) (by norm_num),
    comp_neg_X_comp_neg_X]

def squareLiftLinear : K[X] →ₗ[K] K[X] where
  toFun := squareLift
  map_add' p q := by simp [squareLift, add_comp]
  map_smul' c p := by simp [squareLift, smul_comp]

def compressedFunctional (L : K[X] →ₗ[K] K) : K[X] →ₗ[K] K :=
  L.comp squareLiftLinear

@[simp] theorem compressedFunctional_apply (L : K[X] →ₗ[K] K) (p : K[X]) :
    compressedFunctional L p = L (squareLift p) := rfl

@[simp] theorem squareLift_mul (p q : K[X]) :
    squareLift (p * q) = squareLift p * squareLift q := by simp [squareLift, mul_comp]

theorem squareLift_dvd {p q : K[X]} (h : p ∣ q) : squareLift p ∣ squareLift q := by
  obtain ⟨a, rfl⟩ := h
  exact ⟨squareLift a, squareLift_mul p a⟩

def compressedQ (B p : K[X]) : K[X] := squareCompress (operatorQ B (squareLift p))
def compressedR (B p : K[X]) : K[X] := squareCompress (operatorR B (squareLift p))
def compressedQstar (A p : K[X]) : K[X] := squareCompress (operatorQstar A (squareLift p))
def compressedRstar (B p : K[X]) : K[X] := squareCompress (operatorRstar B (squareLift p))

theorem operatorR_even (B p : K[X]) :
    (operatorR B (squareLift p)).comp (-X) = operatorR B (squareLift p) := by
  simp only [operatorR, mul_comp, X_comp, operatorD_odd_of_even B _ (squareLift_even p)]
  ring

theorem operatorRstar_even (B p : K[X]) :
    (operatorRstar B (squareLift p)).comp (-X) = operatorRstar B (squareLift p) := by
  apply operatorD_even_of_odd
  simp [mul_comp, squareLift_even]

@[simp] theorem lift_compressedQ (B p : K[X]) :
    squareLift (compressedQ B p) = operatorQ B (squareLift p) :=
  squareLift_squareCompress _ (evenPart_reflection _)

@[simp] theorem lift_compressedR (B p : K[X]) :
    squareLift (compressedR B p) = operatorR B (squareLift p) :=
  squareLift_squareCompress _ (operatorR_even B p)

@[simp] theorem lift_compressedQstar (A p : K[X]) :
    squareLift (compressedQstar A p) = operatorQstar A (squareLift p) :=
  squareLift_squareCompress _ (evenPart_reflection _)

@[simp] theorem lift_compressedRstar (B p : K[X]) :
    squareLift (compressedRstar B p) = operatorRstar B (squareLift p) :=
  squareLift_squareCompress _ (operatorRstar_even B p)

theorem compressedQ_adjoint (L : K[X] →ₗ[K] K) (A B : K[X])
    (hPearson : ∀ f : K[X], L (B * f.comp (X + 1)) = L (A * f))
    (hEvenL : ∀ f : K[X], L (f.comp (-X)) = L f)
    (p q : K[X]) :
    compressedFunctional L (compressedQ B p * q) =
      compressedFunctional L (p * compressedQstar A q) := by
  simp only [compressedFunctional_apply, squareLift_mul, lift_compressedQ, lift_compressedQstar]
  exact operatorQ_adjoint L A B hPearson hEvenL _ _ (squareLift_even p) (squareLift_even q)

theorem compressedR_adjoint (L : K[X] →ₗ[K] K) (A B : K[X])
    (hB : B.comp (-X) = -A)
    (hPearson : ∀ f : K[X], L (B * f.comp (X + 1)) = L (A * f))
    (p q : K[X]) :
    compressedFunctional L (compressedR B p * q) =
      compressedFunctional L (p * compressedRstar B q) := by
  simp only [compressedFunctional_apply, squareLift_mul, lift_compressedR, lift_compressedRstar]
  exact operatorR_adjoint L A B hB hPearson _ _

/-- The two actual cubic operators preserve the least kernel ideal once
the displayed Pearson relation and finite annihilation budget hold. -/
theorem minimal_kernel_cubic_divisibilities
    (L : K[X] →ₗ[K] K) (N m1 m2 m M : ℕ) (p : K[X])
    (hPearson : ∀ f : K[X],
      L (polynomialB N m1 m2 * f.comp (X + 1)) = L (polynomialA N m1 m2 * f))
    (hEvenL : ∀ f : K[X], L (f.comp (-X)) = L f)
    (hp : p.Monic) (hsize : p.natDegree ≤ m + 1)
    (hpann : ∀ j ≤ m, compressedFunctional L (p * X ^ j) = 0)
    (hmin : ∀ f : K[X], f.Monic →
      (∀ j ≤ m, compressedFunctional L (f * X ^ j) = 0) →
      p.natDegree ≤ f.natDegree)
    (hann : ∀ j ≤ M, compressedFunctional L (p * X ^ j) = 0)
    (hbudget : p.natDegree + 3 ≤ M) :
    squareLift p ∣ operatorQ (polynomialB N m1 m2) (squareLift p) ∧
      squareLift p ∣ operatorR (polynomialB N m1 m2) (squareLift p) := by
  have hB : (polynomialB N m1 m2 : K[X]).natDegree ≤ 9 := by
    rw [polynomialB_natDegree]
  have hA : (polynomialA N m1 m2 : K[X]).natDegree ≤ 9 := by
    have h := congrArg Polynomial.natDegree (polynomialB_reflection (K := K) N m1 m2)
    simp only [natDegree_neg, natDegree_comp, natDegree_X, mul_one] at h
    rw [← h, polynomialB_natDegree]
  have hQ : p ∣ compressedQ (polynomialB N m1 m2) p := by
    apply Hankel.minimal_kernel_dvd_of_adjoint (compressedFunctional L) m M 4 p hp
      hsize hpann hmin hann (compressedQ (polynomialB N m1 m2))
      (compressedQstar (polynomialA N m1 m2))
      (compressedQ_adjoint L _ _ hPearson hEvenL)
      (compressedQ_degree _ p hB)
    · intro k hk
      simpa only [compressedQstar, natDegree_X_pow] using compressedQstar_degree
        (polynomialA N m1 m2 : K[X]) (X ^ k) hA
    · omega
  have hR : p ∣ compressedR (polynomialB N m1 m2) p := by
    apply Hankel.minimal_kernel_dvd_of_adjoint (compressedFunctional L) m M 4 p hp
      hsize hpann hmin hann (compressedR (polynomialB N m1 m2))
      (compressedRstar (polynomialB N m1 m2))
      (compressedR_adjoint L _ _ (polynomialB_reflection N m1 m2) hPearson)
      (compressedR_degree _ p hB)
    · intro k hk
      simpa only [compressedRstar, natDegree_X_pow] using compressedRstar_degree
        (polynomialB N m1 m2 : K[X]) (X ^ k) hB
    · omega
  constructor
  · simpa only [lift_compressedQ] using squareLift_dvd hQ
  · simpa only [lift_compressedR] using squareLift_dvd hR

end Zeta3.Construction.Pearson

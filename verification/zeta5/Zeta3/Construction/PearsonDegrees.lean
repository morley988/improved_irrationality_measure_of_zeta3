import Zeta3.Construction.PearsonAdjoints
import Mathlib.Algebra.Polynomial.Taylor
import Mathlib.Algebra.Polynomial.Expand

/-!
# The degree-four budget of the cubic Pearson operators

Parity removes the possible top degree after taking a finite difference.
The resulting physical-coordinate degree gain is eight, hence four after
compression to the squared coordinate.  The four operator bounds below are
proved for actual polynomial formulas, not supplied as numerical premises.
-/

noncomputable section
namespace Zeta3.Construction.Pearson
open Polynomial
variable {K : Type*} [Field K] [CharZero K]

theorem evenPart_reflection (f : K[X]) : (evenPart f).comp (-X) = evenPart f := by
  simp only [evenPart, mul_comp, C_comp, add_comp, comp_neg_X_comp_neg_X]
  ring

theorem evenPart_natDegree_le (f : K[X]) : (evenPart f).natDegree ≤ f.natDegree := by
  rw [evenPart, ← smul_eq_C_mul]
  refine (natDegree_smul_le _ _).trans ((natDegree_add_le _ _).trans ?_)
  simp [natDegree_comp]

theorem odd_polynomial_even_coeff_zero (f : K[X]) (hf : f.comp (-X) = -f) (k : ℕ) :
    f.coeff (2 * k) = 0 := by
  have h := congrArg (fun P : K[X] => P.coeff (2 * k)) hf
  rw [show (-X : K[X]) = C (-1) * X by simp, comp_C_mul_X_coeff, coeff_neg] at h
  simp only [pow_mul, neg_one_sq, one_pow, mul_one] at h
  have htwo : (2 : K) * f.coeff (2 * k) = 0 := by linear_combination h
  exact (mul_eq_zero.mp htwo).resolve_left (by norm_num)

theorem even_polynomial_odd_coeff_zero (f : K[X]) (hf : f.comp (-X) = f) (k : ℕ) :
    f.coeff (2 * k + 1) = 0 := by
  have h := congrArg (fun P : K[X] => P.coeff (2 * k + 1)) hf
  rw [show (-X : K[X]) = C (-1) * X by simp, comp_C_mul_X_coeff] at h
  simp only [pow_add, pow_mul, neg_one_sq, one_pow, pow_one, one_mul, mul_neg_one] at h
  have htwo : (2 : K) * f.coeff (2 * k + 1) = 0 := by linear_combination -h
  exact (mul_eq_zero.mp htwo).resolve_left (by norm_num)

theorem natDegree_le_of_next_coeff_zero (f : K[X]) (n : ℕ)
    (hdeg : f.natDegree ≤ n + 1) (hzero : f.coeff (n + 1) = 0) :
    f.natDegree ≤ n := by
  apply natDegree_le_iff_coeff_eq_zero.mpr
  intro k hk
  by_cases heq : k = n + 1
  · simpa [heq] using hzero
  · exact coeff_eq_zero_of_natDegree_lt (by omega)

theorem shift_sub_natDegree_le (f : K[X]) (c : K) :
    (f.comp (X + C c) - f).natDegree ≤ f.natDegree - 1 := by
  change (taylor c f - f).natDegree ≤ f.natDegree - 1
  by_cases hf : f = 0
  · simp [hf]
  by_cases hd : taylor c f - f = 0
  · simp [hd]
  have h := degree_sub_lt_right (degree_taylor f c) hf (leadingCoeff_taylor c f)
  rw [degree_eq_natDegree hd, degree_eq_natDegree hf] at h
  have hnat : (taylor c f - f).natDegree < f.natDegree := by exact_mod_cast h
  omega

theorem operatorD_reflection_factor (B f : K[X]) (e : K)
    (hf : f.comp (-X) = C e * f) :
    (operatorD B f).comp (-X) = C (-e) * operatorD B f := by
  have hp : (f.comp (X + 1)).comp (-X) = C e * f.comp (X - 1) := by
    calc
      _ = (f.comp (-X)).comp (X - 1) := by
        simp only [comp_assoc]
        congr 1
        simp only [add_comp, neg_comp, X_comp, one_comp]
        ring
      _ = _ := by rw [hf, mul_comp, C_comp]
  have hm : (f.comp (X - 1)).comp (-X) = C e * f.comp (X + 1) := by
    calc
      _ = (f.comp (-X)).comp (X + 1) := by
        simp only [comp_assoc]
        congr 1
        simp only [sub_comp, neg_comp, X_comp, one_comp]
        ring
      _ = _ := by rw [hf, mul_comp, C_comp]
  simp only [operatorD, sub_comp, mul_comp, hp, hm, hf, comp_neg_X_comp_neg_X, C_neg]
  ring

theorem operatorD_odd_of_even (B f : K[X]) (hf : f.comp (-X) = f) :
    (operatorD B f).comp (-X) = -operatorD B f := by
  simpa only [C_neg, C_1, neg_mul, one_mul] using
    operatorD_reflection_factor B f 1 (by simpa using hf)

theorem operatorD_even_of_odd (B f : K[X]) (hf : f.comp (-X) = -f) :
    (operatorD B f).comp (-X) = operatorD B f := by
  simpa only [neg_neg, C_1, one_mul] using
    operatorD_reflection_factor B f (-1) (by simpa using hf)

theorem operatorD_natDegree_le (B f : K[X]) (hB : B.natDegree ≤ 9) :
    (operatorD B f).natDegree ≤ f.natDegree + 8 := by
  by_cases hf : f.natDegree = 0
  · have heq := eq_C_of_natDegree_eq_zero hf
    rw [heq]
    simp [operatorD]
  · have hp : (f.comp (X + 1) - f).natDegree ≤ f.natDegree - 1 := by
      simpa only [C_1] using shift_sub_natDegree_le f (1 : K)
    have hm : (f.comp (X - 1) - f).natDegree ≤ f.natDegree - 1 := by
      simpa only [C_neg, C_1, sub_eq_add_neg] using shift_sub_natDegree_le f (-1 : K)
    have hBr : (B.comp (-X)).natDegree = B.natDegree := by simp [natDegree_comp]
    have hleft := natDegree_mul_le (p := B) (q := f.comp (X + 1) - f)
    have hright := natDegree_mul_le (p := B.comp (-X)) (q := f.comp (X - 1) - f)
    rw [hBr] at hright
    unfold operatorD
    exact (natDegree_sub_le _ _).trans (max_le (by omega) (by omega))

theorem operatorD_even_input_degree (B f : K[X]) (j : ℕ)
    (hB : B.natDegree ≤ 9) (hf : f.comp (-X) = f) (hdeg : f.natDegree ≤ 2 * j) :
    (operatorD B f).natDegree ≤ 2 * j + 7 := by
  apply natDegree_le_of_next_coeff_zero
  · have hd := operatorD_natDegree_le B f hB
    omega
  · have hz := odd_polynomial_even_coeff_zero _ (operatorD_odd_of_even B f hf) (j + 4)
    convert hz using 1 <;> congr 1 <;> omega

theorem operatorD_odd_input_degree (B f : K[X]) (j : ℕ)
    (hB : B.natDegree ≤ 9) (hf : f.comp (-X) = -f) (hdeg : f.natDegree ≤ 2 * j + 1) :
    (operatorD B f).natDegree ≤ 2 * j + 8 := by
  apply natDegree_le_of_next_coeff_zero
  · have hd := operatorD_natDegree_le B f hB
    omega
  · have hz := even_polynomial_odd_coeff_zero _ (operatorD_even_of_odd B f hf) (j + 4)
    convert hz using 1 <;> congr 1 <;> omega

theorem operatorQ_degree (B f : K[X]) (j : ℕ)
    (hB : B.natDegree ≤ 9) (hdeg : f.natDegree ≤ 2 * j) :
    (operatorQ B f).natDegree ≤ 2 * j + 8 := by
  apply natDegree_le_of_next_coeff_zero
  · have hs : (f.comp (X + 1)).natDegree = f.natDegree := by
      simpa only [taylor_apply, C_1] using natDegree_taylor f (1 : K)
    have hm := natDegree_mul_le (p := B) (q := f.comp (X + 1))
    have he := evenPart_natDegree_le (B * f.comp (X + 1))
    change (evenPart (B * f.comp (X + 1))).natDegree ≤ _
    omega
  · have hz := even_polynomial_odd_coeff_zero _
      (evenPart_reflection (B * f.comp (X + 1))) (j + 4)
    convert hz using 1 <;> congr 1 <;> omega

theorem operatorQstar_degree (A f : K[X]) (j : ℕ)
    (hA : A.natDegree ≤ 9) (hdeg : f.natDegree ≤ 2 * j) :
    (operatorQstar A f).natDegree ≤ 2 * j + 8 := by
  apply natDegree_le_of_next_coeff_zero
  · have hs : (f.comp (X - 1)).natDegree = f.natDegree := by
      simpa only [taylor_apply, C_neg, C_1, sub_eq_add_neg] using natDegree_taylor f (-1 : K)
    have hm := natDegree_mul_le (p := A) (q := f.comp (X - 1))
    have he := evenPart_natDegree_le (A * f.comp (X - 1))
    change (evenPart (A * f.comp (X - 1))).natDegree ≤ _
    omega
  · have hz := even_polynomial_odd_coeff_zero _
      (evenPart_reflection (A * f.comp (X - 1))) (j + 4)
    convert hz using 1 <;> congr 1 <;> omega

theorem operatorR_degree (B f : K[X]) (j : ℕ)
    (hB : B.natDegree ≤ 9) (hf : f.comp (-X) = f) (hdeg : f.natDegree ≤ 2 * j) :
    (operatorR B f).natDegree ≤ 2 * j + 8 := by
  have hd := operatorD_even_input_degree B f j hB hf hdeg
  have hm := natDegree_mul_le (p := (X : K[X])) (q := operatorD B f)
  simp only [natDegree_X] at hm
  exact hm.trans (by omega)

theorem operatorRstar_degree (B f : K[X]) (j : ℕ)
    (hB : B.natDegree ≤ 9) (hf : f.comp (-X) = f) (hdeg : f.natDegree ≤ 2 * j) :
    (operatorRstar B f).natDegree ≤ 2 * j + 8 := by
  have hodd : (X * f).comp (-X) = -(X * f) := by simp [mul_comp, hf]
  have hd : (X * f).natDegree ≤ 2 * j + 1 := by
    have hm := natDegree_mul_le (p := (X : K[X])) (q := f)
    simp only [natDegree_X] at hm
    omega
  exact operatorD_odd_input_degree B (X * f) j hB hodd hd

/-- Lift from t to x by the manuscript substitution t=-x². -/
def squareLift (p : K[X]) : K[X] := p.comp (-(X ^ 2))

theorem squareLift_even (p : K[X]) : (squareLift p).comp (-X) = squareLift p := by
  simp [squareLift, comp_assoc]

theorem squareLift_natDegree (p : K[X]) : (squareLift p).natDegree = 2 * p.natDegree := by
  simp [squareLift, natDegree_comp, Nat.mul_comm]

def squareCompress (f : K[X]) : K[X] := (Polynomial.contract 2 f).comp (-X)

theorem squareCompress_natDegree_le (f : K[X]) (d : ℕ)
    (hdeg : f.natDegree ≤ 2 * d + 1) : (squareCompress f).natDegree ≤ d := by
  have hc : (Polynomial.contract 2 f).natDegree ≤ d := by
    by_cases hz : Polynomial.contract 2 f = 0
    · simp [hz]
    · have htop : (Polynomial.contract 2 f).coeff (Polynomial.contract 2 f).natDegree ≠ 0 := by
        simpa only [coeff_natDegree] using leadingCoeff_ne_zero.mpr hz
      rw [Polynomial.coeff_contract (by norm_num)] at htop
      have hl := le_natDegree_of_ne_zero htop
      omega
  simpa [squareCompress, natDegree_comp] using hc

theorem compressedQ_degree (B p : K[X]) (hB : B.natDegree ≤ 9) :
    (squareCompress (operatorQ B (squareLift p))).natDegree ≤ p.natDegree + 4 := by
  apply squareCompress_natDegree_le
  have h := operatorQ_degree B (squareLift p) p.natDegree hB (by rw [squareLift_natDegree])
  omega

theorem compressedR_degree (B p : K[X]) (hB : B.natDegree ≤ 9) :
    (squareCompress (operatorR B (squareLift p))).natDegree ≤ p.natDegree + 4 := by
  apply squareCompress_natDegree_le
  have h := operatorR_degree B (squareLift p) p.natDegree hB (squareLift_even p)
    (by rw [squareLift_natDegree])
  omega

theorem compressedQstar_degree (A p : K[X]) (hA : A.natDegree ≤ 9) :
    (squareCompress (operatorQstar A (squareLift p))).natDegree ≤ p.natDegree + 4 := by
  apply squareCompress_natDegree_le
  have h := operatorQstar_degree A (squareLift p) p.natDegree hA (by rw [squareLift_natDegree])
  omega

theorem compressedRstar_degree (B p : K[X]) (hB : B.natDegree ≤ 9) :
    (squareCompress (operatorRstar B (squareLift p))).natDegree ≤ p.natDegree + 4 := by
  apply squareCompress_natDegree_le
  have h := operatorRstar_degree B (squareLift p) p.natDegree hB (squareLift_even p)
    (by rw [squareLift_natDegree])
  omega

end Zeta3.Construction.Pearson

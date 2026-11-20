import Zeta5.Arithmetic.AtomicMinors

/-! Cubic atomic minors: the harmonic loss is three prime powers.
Both Vandermonde gains are retained, giving k(k-1)+k*base-3*min(k,h). -/
noncomputable section
namespace Zeta3.Arithmetic
open Polynomial OddZeta.FourValue Zeta5.Construction
open Zeta5.Arithmetic Zeta5.Arithmetic.Allocation
variable {p : ℕ} [Fact p.Prime]

theorem atomicMinor_translated_bound {d r k : ℕ}
    (w : Fin d → ℚ[X]) (x : Fin d → ℚ) (high : Finset (Fin d)) (base : ℤ)
    (hx : ∀ i, PadicLower p 1 (x i))
    (hw : ∀ i, PolynomialPadicLower p
      (base - 3 * (if i ∈ high then (1 : ℤ) else 0)) (w i))
    (rows cols : Fin k → Fin r)
    (hr : Function.Injective rows) (hc : Function.Injective cols) :
    PolynomialPadicLower p
      ((k : ℤ) * (k - 1) + k * base - 3 * (min k high.card : ℕ))
      ((atomicMatrix w x r).submatrix rows cols).det := by
  classical
  let A : Matrix (Fin k) (Fin d) ℚ[X] := fun i a => C ((x a) ^ (rows i).val)
  let B : Matrix (Fin d) (Fin k) ℚ[X] := fun a j => w a * C ((x a) ^ (cols j).val)
  have he : (atomicMatrix w x r).submatrix rows cols = A * B := by
    funext i j
    simp only [atomicMatrix, Matrix.submatrix_apply, Matrix.mul_apply, A, B,
      pow_add, map_mul]
    apply Finset.sum_congr rfl
    intro a ha
    ring
  rw [he, rectangular_expansion]
  apply PolynomialPadicLower.sum
  intro f hf
  by_cases hinj : Function.Injective f
  · have hA : PolynomialPadicLower p (∑ i, ((rows i).val : ℤ))
        (A.submatrix id f).det := by
      have h := polynomialPadicLower_det_weighted (A.submatrix id f)
        (fun i => ((rows i).val : ℤ)) (fun _ => 0) 0 (by
          intro i j
          change PolynomialPadicLower p (((rows i).val : ℤ) + 0 + 0)
            (C ((x (f j)) ^ (rows i).val))
          simpa only [add_zero] using polynomialPower_padicLower (hx (f j)) (rows i).val)
      simpa using h
    have hB := PolynomialPadicLower.prod (p := p) Finset.univ
      (fun i => B (f i) i)
      (fun i => base - 3 * (if f i ∈ high then (1 : ℤ) else 0) + (cols i).val)
      (fun i _ => (hw (f i)).mul (polynomialPower_padicLower (hx (f i)) (cols i).val))
    have hhigh : (∑ i : Fin k, if f i ∈ high then (1 : ℤ) else 0) =
        ((Finset.univ.filter (fun i => f i ∈ high)).card : ℤ) := by simp
    have hcard : ((Finset.univ.filter (fun i => f i ∈ high)).card : ℤ) ≤
        (min k high.card : ℕ) := by exact_mod_cast selected_card_le f hinj high
    have hr' := twice_sum_injective_nat_lower (fun i => (rows i).val)
      (fun i j h => hr (Fin.ext h))
    have hc' := twice_sum_injective_nat_lower (fun i => (cols i).val)
      (fun i j h => hc (Fin.ext h))
    apply (hA.mul hB).mono
    simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_const,
      Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, ← Finset.mul_sum, hhigh]
    nlinarith
  · obtain ⟨i, j, hij, hne⟩ := Function.not_injective_iff.mp hinj
    rw [Matrix.det_zero_of_column_eq hne (fun a => by simp [Matrix.submatrix_apply, hij]),
      zero_mul]
    exact PolynomialPadicLower.zero _

theorem atomic_translated_minorLower {d : ℕ} (r : ℕ)
    (w : Fin d → ℚ[X]) (x : Fin d → ℚ) (high : Finset (Fin d)) (base : ℤ)
    (hx : ∀ i, PadicLower p 1 (x i))
    (hw : ∀ i, PolynomialPadicLower p
      (base - 3 * (if i ∈ high then (1 : ℤ) else 0)) (w i)) :
    MinorLower (p := p) (atomicMatrix w x r)
      (fun k => (k : ℤ) * (k - 1) + k * base - 3 * (min k high.card : ℕ)) := by
  intro k rows cols
  by_cases hr : Function.Injective rows
  · by_cases hc : Function.Injective cols
    · exact atomicMinor_translated_bound w x high base hx hw rows cols hr hc
    · obtain ⟨i, j, hij, hne⟩ := Function.not_injective_iff.mp hc
      rw [Matrix.det_zero_of_column_eq hne (fun a => by simp [Matrix.submatrix_apply, hij])]
      exact PolynomialPadicLower.zero _
  · obtain ⟨i, j, hij, hne⟩ := Function.not_injective_iff.mp hr
    have hrow : ((atomicMatrix w x r).submatrix rows cols) i =
        ((atomicMatrix w x r).submatrix rows cols) j := by
      funext a
      change atomicMatrix w x r (rows i) (cols a) = atomicMatrix w x r (rows j) (cols a)
      rw [hij]
    rw [Matrix.det_zero_of_row_eq hne hrow]
    exact PolynomialPadicLower.zero _


theorem atomic_minorLower {d : ℕ} (r : ℕ)
    (w : Fin d → ℚ[X]) (x : Fin d → ℚ) (c : ℚ) (high : Finset (Fin d)) (base : ℤ)
    (hc : PadicLower p 0 c) (hx : ∀ i, PadicLower p 1 (x i - c))
    (hw : ∀ i, PolynomialPadicLower p
      (base - 3 * (if i ∈ high then (1 : ℤ) else 0)) (w i)) :
    MinorLower (p := p) (atomicMatrix w x r)
      (fun k => (k : ℤ) * (k - 1) + k * base - 3 * (min k high.card : ℕ)) := by
  rw [atomic_shift_congruence w x r c]
  apply minorLower_integral_change _ _ _ _
    (atomic_translated_minorLower r w (fun i => x i - c) high base hx hw)
  · intro i j
    exact shiftMatrix_integral r hc j i
  · exact shiftMatrix_integral r hc

end Zeta3.Arithmetic

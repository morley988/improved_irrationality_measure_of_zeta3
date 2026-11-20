import Zeta5.Arithmetic.RestrictionDeterminant
import Zeta5.Arithmetic.LocalFunctional

/-!
# The determinant gain from the second reduced kernel form

This module supplies the valuation algebra behind the second layer. It
makes the two genuinely mathematical inputs explicit: divisibility on the
first set of rows, and the residue-field rank of the constant term on the
second set of columns after division of those rows by p.
-/
noncomputable section
namespace Zeta3.Arithmetic
open Module Matrix Polynomial Finset OddZeta.FourValue
open Zeta5.Arithmetic
open scoped BigOperators

theorem exists_kernel_row_basis_linearMap {K ι V : Type*} [Field K]
    [Fintype ι] [DecidableEq ι] [AddCommGroup V] [Module K V]
    (f : (ι → K) →ₗ[K] V) :
    ∃ T : Matrix ι ι K, ∃ s : Finset ι,
      T.det ≠ 0 ∧ s.card = finrank K (LinearMap.ker f) ∧
      ∀ i ∈ s, f (T i) = 0 := by
  classical
  let S := LinearMap.ker f
  let b₀ := Module.finBasis K S
  let v : Fin (finrank K S) → (ι → K) := fun i => (b₀ i : ι → K)
  have hv : LinearIndependent K v := by
    exact b₀.linearIndependent.map' S.subtype (Submodule.ker_subtype S)
  let B := Module.Basis.extend hv.linearIndepOn_id
  letI := FiniteDimensional.fintypeBasisIndex B
  have hcard : Fintype.card (hv.linearIndepOn_id.extend (Set.subset_univ _)) = Fintype.card ι := by
    rw [← Module.finrank_eq_card_basis B, Module.finrank_fintype_fun_eq_card]
  let e := Fintype.equivOfCardEq hcard
  let b := B.reindex e
  let j : Fin (finrank K S) → ι := fun k =>
    e ⟨v k, hv.linearIndepOn_id.subset_extend (Set.subset_univ _) (Set.mem_range_self k)⟩
  have hj : Function.Injective j := by
    intro k l h
    apply hv.injective
    exact congrArg (fun z : hv.linearIndepOn_id.extend (Set.subset_univ _) => (z : ι → K)) (e.injective h)
  have hbj (k : Fin (finrank K S)) : b (j k) = v k := by
    simp [b, j, Module.Basis.reindex_apply, B, Module.Basis.extend_apply_self]
  refine ⟨fun i k => b i k, Finset.univ.image j, ?_, ?_, ?_⟩
  · have h := (Pi.basisFun K ι).isUnit_det b
    rw [Pi.basisFun_det_apply] at h
    exact h.ne_zero
  · rw [Finset.card_image_of_injective _ hj]
    simp [S]
  · intro i hi
    obtain ⟨k, _, rfl⟩ := Finset.mem_image.mp hi
    change f (b (j k)) = 0
    rw [hbj]
    exact (b₀ k).property


variable {p : ℕ} [Fact p.Prime]

theorem polynomialPadicLower_det_of_residue_kernel
    {ι V : Type*} [Fintype ι] [DecidableEq ι] [AddCommGroup V]
    [Module (PadicResidueField p) V]
    (A : Matrix ι ι ℚ[X]) (f : (ι → PadicResidueField p) →ₗ[PadicResidueField p] V)
    (hA : ∀ i j, PolynomialPadicLower p 0 (A i j))
    (hker : ∀ x : ι → padicIntegralSubring p,
      f (fun i => padicReduction p (x i)) = 0 →
      ∀ j, PolynomialPadicLower p 1 (∑ i, C (x i : ℚ) * A i j)) :
    PolynomialPadicLower p
      ((Fintype.card ι : ℤ) - finrank (PadicResidueField p) (LinearMap.range f)) A.det := by
  classical
  obtain ⟨T, s, hT, hs, hTs⟩ := exists_kernel_row_basis_linearMap f
  choose TL hTL using fun i j => padicReduction_surjective (p := p) (T i j)
  let TI : Matrix ι ι (padicIntegralSubring p) := Matrix.of TL
  let TQ : Matrix ι ι ℚ := fun i j => (TL i j : ℚ)
  have hTQ (i j : ι) : PadicLower p 0 (TQ i j) := (TL i j).property
  have hmap : (padicReduction p).mapMatrix TI = T := by
    ext i j
    exact hTL i j
  have hredDet : padicReduction p (TI.det) ≠ 0 := by
    rw [RingHom.map_det, hmap]
    exact hT
  have hdetval : ((TI.det : padicIntegralSubring p) : ℚ) = TQ.det := by
    exact (padicIntegralSubring p).subtype.map_det TI
  have hinv : PadicLower p 0 (TQ.det⁻¹) := by
    rw [← hdetval]
    exact padicReduction_ne_zero_inv hredDet
  have hdet0 : TQ.det ≠ 0 := by
    intro h0
    apply hredDet
    apply (padicReduction_eq_zero _).mpr
    rw [hdetval, h0]
    exact PadicLower.zero 1
  let U : Matrix ι ι ℚ[X] := C.mapMatrix TQ * A
  have hU (i j : ι) : PolynomialPadicLower p (if i ∈ s then 1 else 0) (U i j) := by
    dsimp only [U]
    rw [Matrix.mul_apply]
    by_cases hi : i ∈ s
    · simp only [hi, ↓reduceIte, Matrix.map_apply, RingHom.mapMatrix_apply]
      apply hker (TL i) _ j
      simpa only [hTL] using hTs i hi
    · simp only [hi, ↓reduceIte, Matrix.map_apply, RingHom.mapMatrix_apply]
      apply PolynomialPadicLower.sum
      intro k hk
      simpa using (PolynomialPadicLower.constant (hTQ i k)).mul (hA k j)
  have hUdet : PolynomialPadicLower p (s.card : ℤ) U.det := by
    have hh := polynomialPadicLower_det_weighted (p := p) U
      (fun i => if i ∈ s then 1 else 0) (fun _ => 0) 0
      (fun i j => by simpa using hU i j)
    simpa using hh
  have hAdet : PolynomialPadicLower p (s.card : ℤ) A.det := by
    have hh := (PolynomialPadicLower.constant hinv).mul hUdet
    have hid : C (TQ.det⁻¹) * U.det = A.det := by
      dsimp [U]
      rw [Matrix.det_mul, ← RingHom.map_det, ← mul_assoc, ← map_mul,
        inv_mul_cancel₀ hdet0, map_one, one_mul]
    simpa only [zero_add, hid] using hh
  apply hAdet.mono
  have hnull := f.finrank_range_add_finrank_ker
  rw [Module.finrank_fintype_fun_eq_card] at hnull
  rw [hs]
  omega

theorem polynomialPadicLower_det_of_column_residue_kernel
    {ι V : Type*} [Fintype ι] [DecidableEq ι] [AddCommGroup V]
    [Module (PadicResidueField p) V]
    (A : Matrix ι ι ℚ[X]) (f : (ι → PadicResidueField p) →ₗ[PadicResidueField p] V)
    (hA : ∀ i j, PolynomialPadicLower p 0 (A i j))
    (hker : ∀ x : ι → padicIntegralSubring p,
      f (fun j => padicReduction p (x j)) = 0 →
      ∀ i, PolynomialPadicLower p 1 (∑ j, C (x j : ℚ) * A i j)) :
    PolynomialPadicLower p
      ((Fintype.card ι : ℤ) - finrank (PadicResidueField p) (LinearMap.range f)) A.det := by
  have h := polynomialPadicLower_det_of_residue_kernel A.transpose f
    (fun i j => hA j i) hker
  simpa only [Matrix.det_transpose] using h

/-- The constant residue matrix on a chosen set of columns. -/
def reducedConstantColumns {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℚ[X]) (hA : ∀ i j, PolynomialPadicLower p 0 (A i j))
    (T : Finset ι) : Matrix ι ι (PadicResidueField p) :=
  fun i j => if j ∈ T then padicReduction p ⟨(A i j).coeff 0, hA i j 0⟩ else 0

/-- If all nonconstant coefficients in the chosen columns vanish modulo p,
their only obstruction to further divisibility is the rank of their
constant residue matrix. -/
theorem polynomialPadicLower_det_of_constant_reduced_columns
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℚ[X]) (hA : ∀ i j, PolynomialPadicLower p 0 (A i j))
    (T : Finset ι)
    (hhigh : ∀ i j, j ∈ T → ∀ k : ℕ, 0 < k → PadicLower p 1 ((A i j).coeff k)) :
    PolynomialPadicLower p
      ((T.card : ℤ) - finrank (PadicResidueField p)
        (LinearMap.range (reducedConstantColumns A hA T).mulVecLin)) A.det := by
  classical
  let F := PadicResidueField p
  let Mbar := reducedConstantColumns A hA T
  let V := (↥Tᶜ → F) × LinearMap.range Mbar.mulVecLin
  let outside : (ι → F) →ₗ[F] (↥Tᶜ → F) :=
    LinearMap.pi (fun j : ↥Tᶜ => LinearMap.proj j.val)
  let f : (ι → F) →ₗ[F] V := outside.prod Mbar.mulVecLin.rangeRestrict
  have hker : ∀ x : ι → padicIntegralSubring p,
      f (fun j => padicReduction p (x j)) = 0 →
      ∀ i, PolynomialPadicLower p 1 (∑ j, C (x j : ℚ) * A i j) := by
    intro x hfx i k
    have houtside (j : ι) (hj : j ∉ T) : padicReduction p (x j) = 0 := by
      have h := congrArg (fun v : V => v.1 ⟨j, Finset.mem_compl.mpr hj⟩) hfx
      exact h
    have hM : Mbar.mulVec (fun j => padicReduction p (x j)) = 0 := by
      have h := congrArg (fun v : V => (v.2 : ι → F)) hfx
      exact h
    simp only [finsetSum_coeff, coeff_C_mul]
    let a : padicIntegralSubring p := ∑ j, x j * ⟨(A i j).coeff k, hA i j k⟩
    have ha : (a : ℚ) = ∑ j, (x j : ℚ) * (A i j).coeff k := by simp [a]
    rw [← ha]
    apply (padicReduction_eq_zero a).mp
    simp only [a, map_sum, map_mul]
    by_cases hk : k = 0
    · subst k
      have he : (∑ j, padicReduction p (x j) *
          padicReduction p ⟨(A i j).coeff 0, hA i j 0⟩) =
          ∑ j, Mbar i j * padicReduction p (x j) := by
        apply Finset.sum_congr rfl
        intro j hj
        by_cases hT : j ∈ T
        · simp [Mbar, reducedConstantColumns, hT, mul_comm]
        · simp [Mbar, reducedConstantColumns, hT, houtside j hT]
      rw [he]
      exact congrFun hM i
    · apply Finset.sum_eq_zero
      intro j hj
      by_cases hT : j ∈ T
      · have hz : padicReduction p ⟨(A i j).coeff k, hA i j k⟩ = 0 :=
          (padicReduction_eq_zero _).mpr (hhigh i j hT k (by omega))
        rw [hz, mul_zero]
      · rw [houtside j hT, zero_mul]
  have hdet := polynomialPadicLower_det_of_column_residue_kernel A f hA hker
  apply hdet.mono
  have hr := (LinearMap.range f).finrank_le
  have hdim : finrank F V = Fintype.card ι - T.card +
      finrank F (LinearMap.range Mbar.mulVecLin) := by
    simp only [V, Module.finrank_prod, Module.finrank_fintype_fun_eq_card,
      Fintype.card_coe, Finset.card_compl]
  rw [hdim] at hr
  have hcard : T.card ≤ Fintype.card ι := Finset.card_le_univ T
  change (T.card : ℤ) - finrank F (LinearMap.range Mbar.mulVecLin) ≤
    (Fintype.card ι : ℤ) - finrank F (LinearMap.range f)
  omega

def primeRowUnscale {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℚ[X]) (S : Finset ι) : Matrix ι ι ℚ[X] :=
  fun i j => if i ∈ S then C ((p : ℚ)⁻¹) * A i j else A i j

theorem primeRowUnscale_integral {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℚ[X]) (S : Finset ι)
    (hA : ∀ i j, PolynomialPadicLower p (if i ∈ S then 1 else 0) (A i j)) :
    ∀ i j, PolynomialPadicLower p 0 (primeRowUnscale (p := p) A S i j) := by
  intro i j
  by_cases hi : i ∈ S
  · have h := (PolynomialPadicLower.constant
        (inverse_prime_power_padicLower (p := p) 1)).mul (hA i j)
    simpa only [primeRowUnscale, if_pos hi, Nat.cast_one, pow_one, neg_add_cancel] using h
  · simpa only [primeRowUnscale, if_neg hi] using hA i j

theorem polynomialPadicLower_det_of_primeRowUnscale
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℚ[X]) (S : Finset ι) (w : ℤ)
    (hB : PolynomialPadicLower p w (primeRowUnscale (p := p) A S).det) :
    PolynomialPadicLower p ((S.card : ℤ) + w) A.det := by
  classical
  let D : Matrix ι ι ℚ[X] := Matrix.diagonal (fun i => C (if i ∈ S then (p : ℚ) else 1))
  have hp0 : (p : ℚ) ≠ 0 := by exact_mod_cast (Fact.out : p.Prime).ne_zero
  have he : A = D * primeRowUnscale (p := p) A S := by
    ext i j : 2
    simp only [D, Matrix.diagonal_mul, primeRowUnscale]
    by_cases hi : i ∈ S
    · simp only [if_pos hi, ← mul_assoc, ← C_mul, mul_inv_cancel₀ hp0, C_1, one_mul]
    · simp only [if_neg hi, C_1, one_mul]
  have hD : PolynomialPadicLower p (S.card : ℤ) D.det := by
    rw [show D.det = ∏ i, C (if i ∈ S then (p : ℚ) else 1) by
      exact Matrix.det_diagonal]
    have h := PolynomialPadicLower.prod (p := p) Finset.univ
      (fun i => C (if i ∈ S then (p : ℚ) else 1))
      (fun i => if i ∈ S then (1 : ℤ) else 0) (by
        intro i hi
        by_cases hs : i ∈ S
        · simp only [if_pos hs]
          apply PolynomialPadicLower.constant
          simpa only [Nat.cast_one, pow_one] using prime_power_padicLower (p := p) 1
        · simp only [if_neg hs]
          exact PolynomialPadicLower.constant (by right; simp))
    simpa using h
  rw [he, Matrix.det_mul]
  exact hD.mul hB

/-- The abstract two-kernel factorization. Here B is the rank of the
constant second form on the remaining columns, after the first rows have
been divided by p. The conclusion is exactly the extra determinant gain
used by the cubic second arithmetic layer. -/
theorem two_kernel_determinant_lower
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℚ[X]) (S T : Finset ι)
    (hA : ∀ i j, PolynomialPadicLower p (if i ∈ S then 1 else 0) (A i j))
    (hhigh : ∀ i j, j ∈ T → ∀ k : ℕ, 0 < k →
      PadicLower p 1 ((primeRowUnscale (p := p) A S i j).coeff k))
    (b : ℕ)
    (hrank : finrank (PadicResidueField p) (LinearMap.range
      (reducedConstantColumns (primeRowUnscale (p := p) A S)
        (primeRowUnscale_integral A S hA) T).mulVecLin) ≤ b) :
    PolynomialPadicLower p ((S.card : ℤ) + T.card - b) A.det := by
  have h := polynomialPadicLower_det_of_constant_reduced_columns
    (primeRowUnscale (p := p) A S) (primeRowUnscale_integral A S hA) T hhigh
  have hdet := polynomialPadicLower_det_of_primeRowUnscale A S _ h
  exact hdet.mono (by omega)

end Zeta3.Arithmetic

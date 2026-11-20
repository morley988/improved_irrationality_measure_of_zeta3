import Zeta3.Arithmetic.SecondKernelDeterminant
import Mathlib.LinearAlgebra.Matrix.Rank

/-!
# Unit lifts and bilinear matrices for the second determinant layer

These are finite algebraic transport lemmas. The lifted row bases have
unit determinants in the rational local ring, so changing bases loses no
valuation. The reduced second block is bounded by the rank of its actual
bilinear form.
-/

noncomputable section
namespace Zeta3.Arithmetic
open Matrix Module Polynomial Finset OddZeta.FourValue Zeta5.Arithmetic
open scoped BigOperators

def bilinearSampleMatrix {K V W ι κ : Type*} [Field K]
    [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W]
    (B : V →ₗ[K] W →ₗ[K] K) (x : ι → V) (y : κ → W) : Matrix ι κ K :=
  fun i j => B (x i) (y j)

/-- Sampling a bilinear form cannot increase its linear-map rank. -/
theorem bilinearSampleMatrix_rank_le {K V W ι κ : Type*} [Field K]
    [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    [AddCommGroup W] [Module K W]
    [Fintype ι] [Fintype κ]
    (B : V →ₗ[K] W →ₗ[K] K) (x : ι → V) (y : κ → W) :
    (bilinearSampleMatrix B x y).rank≤finrank K B.range := by
  classical
  let X : (ι→K) →ₗ[K] V :=
    { toFun := fun a => ∑ i,a i • x i
      map_add' := by intro a b; simp [add_smul,Finset.sum_add_distrib]
      map_smul' := by intro a b; simp [Finset.smul_sum,smul_smul] }
  let Y : (W→ₗ[K] K) →ₗ[K] (κ→K) :=
    { toFun := fun f j => f (y j)
      map_add' := by intros; rfl
      map_smul' := by intros; rfl }
  let M : Matrix ι κ K := bilinearSampleMatrix B x y
  have he : M.transpose.mulVecLin=Y.comp (B.comp X) := by
    apply LinearMap.ext
    intro a
    funext j
    change (∑i,B (x i) (y j)*a i)=B (∑i,a i • x i) (y j)
    simp [map_sum,map_smul,LinearMap.sum_apply,mul_comm]
  rw [← Matrix.rank_transpose M,Matrix.rank,he,LinearMap.range_comp]
  exact (Submodule.finrank_map_le _ _).trans
    (Submodule.finrank_mono (LinearMap.range_comp_le_range X B))

variable {p : ℕ} [Fact p.Prime]

def localRationalMatrix {ι : Type*} (L : Matrix ι ι (padicIntegralSubring p)) : Matrix ι ι ℚ :=
  fun i j => (L i j:ℚ)

def localReducedVector {ι : Type*} (x : ι→padicIntegralSubring p) : ι→PadicResidueField p :=
  fun i => padicReduction p (x i)

/-- Lift a residue-field basis adapted to a kernel, with both determinant
nonvanishing and integral determinant inverse retained explicitly. -/
theorem exists_local_kernel_row_basis {ι V : Type*} [Fintype ι] [DecidableEq ι]
    [AddCommGroup V] [Module (PadicResidueField p) V]
    (f : (ι→PadicResidueField p) →ₗ[PadicResidueField p] V) :
    ∃ L : Matrix ι ι (padicIntegralSubring p), ∃ S : Finset ι,
      (localRationalMatrix L).det≠0 ∧
      PadicLower p 0 ((localRationalMatrix L).det⁻¹) ∧
      S.card=finrank (PadicResidueField p) f.ker ∧
      ∀i∈S,f (localReducedVector (L i))=0 := by
  classical
  obtain ⟨T,S,hT,hS,hTS⟩ := exists_kernel_row_basis_linearMap f
  choose L hL using fun i j => padicReduction_surjective (p:=p) (T i j)
  let LI : Matrix ι ι (padicIntegralSubring p) := L
  have hmap : (padicReduction p).mapMatrix LI=T := by
    ext i j
    exact hL i j
  have hd : padicReduction p LI.det≠0 := by
    rw [RingHom.map_det,hmap]
    exact hT
  have he : (LI.det:ℚ)=(localRationalMatrix LI).det :=
    (padicIntegralSubring p).subtype.map_det LI
  have hinv : PadicLower p 0 ((localRationalMatrix LI).det⁻¹) := by
    rw [←he]
    exact padicReduction_ne_zero_inv hd
  refine ⟨LI,S,?_,hinv,hS,?_⟩
  · intro hz
    apply hd
    apply (padicReduction_eq_zero _).mpr
    rw [he,hz]
    exact PadicLower.zero 1
  · intro i hi
    have hei : localReducedVector (LI i)=T i := by
      funext j
      exact hL i j
    rw [hei]
    exact hTS i hi

/-- Actual polynomial pairing of two local-integral coefficient vectors. -/
def localMatrixPair {ι : Type*} [Fintype ι] (A : Matrix ι ι ℚ[X])
    (x y : ι→padicIntegralSubring p) : ℚ[X] :=
  ∑ i,∑ j,C (x i:ℚ)*A i j*C (y j:ℚ)

theorem localMatrixPair_zero_left {ι : Type*} [Fintype ι]
    (A : Matrix ι ι ℚ[X]) (y : ι→padicIntegralSubring p) :
    localMatrixPair A 0 y=0 := by simp [localMatrixPair]

theorem localMatrixPair_zero_right {ι : Type*} [Fintype ι]
    (A : Matrix ι ι ℚ[X]) (x : ι→padicIntegralSubring p) :
    localMatrixPair A x 0=0 := by simp [localMatrixPair]

def localBasisMatrix {ι : Type*} [Fintype ι] (A : Matrix ι ι ℚ[X])
    (L R : Matrix ι ι (padicIntegralSubring p)) : Matrix ι ι ℚ[X] :=
  fun i j => localMatrixPair A (L i) (R j)

theorem localMatrixPair_eq_matrix_product {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℚ[X]) (L R : Matrix ι ι (padicIntegralSubring p)) :
    localBasisMatrix A L R=
      C.mapMatrix (localRationalMatrix L)*A*(C.mapMatrix (localRationalMatrix R)).transpose := by
  ext i j
  simp only [localBasisMatrix,localMatrixPair,Matrix.mul_apply,Matrix.transpose_apply,
    RingHom.mapMatrix_apply,Matrix.map_apply,localRationalMatrix,Finset.sum_mul]
  rw [Finset.sum_comm]

theorem localMatrixPair_padicLower {ι : Type*} [Fintype ι]
    (A : Matrix ι ι ℚ[X]) (x y : ι→padicIntegralSubring p) (w : ℤ)
    (hA : ∀i j,PolynomialPadicLower p w (A i j)) :
    PolynomialPadicLower p w (localMatrixPair A x y) := by
  apply PolynomialPadicLower.sum
  intro i hi
  apply PolynomialPadicLower.sum
  intro j hj
  simpa only [zero_add,add_zero] using
    ((PolynomialPadicLower.constant (x i).property).mul (hA i j)).mul
      (PolynomialPadicLower.constant (y j).property)

theorem localMatrixPair_coeff_pos_padicLower {ι : Type*} [Fintype ι]
    (A : Matrix ι ι ℚ[X]) (x y : ι→padicIntegralSubring p) (w : ℤ)
    (hA : ∀i j k,0<k→PadicLower p w ((A i j).coeff k))
    (k : ℕ) (hk : 0<k) :
    PadicLower p w ((localMatrixPair A x y).coeff k) := by
  simp only [localMatrixPair,finsetSum_coeff,coeff_mul_C,coeff_C_mul]
  apply padicLower_sum
  intro i hi
  apply padicLower_sum
  intro j hj
  simpa only [zero_add,add_zero] using ((x i).property.mul (hA i j k hk)).mul (y j).property

theorem localMatrixPair_eq_left {ι : Type*} [Fintype ι]
    (A : Matrix ι ι ℚ[X]) (x y : ι→padicIntegralSubring p) :
    localMatrixPair A x y=∑j,(∑i,C (x i:ℚ)*A i j)*C (y j:ℚ) := by
  simp only [localMatrixPair,Finset.sum_mul]
  rw [Finset.sum_comm]

theorem localMatrixPair_eq_right {ι : Type*} [Fintype ι]
    (A : Matrix ι ι ℚ[X]) (x y : ι→padicIntegralSubring p) :
    localMatrixPair A x y=∑i,C (x i:ℚ)*(∑j,C (y j:ℚ)*A i j) := by
  simp only [localMatrixPair,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  ring

/-- Undo two unit changes of basis without losing any coefficient valuation. -/
theorem polynomialPadicLower_det_of_local_basis {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℚ[X]) (L R : Matrix ι ι (padicIntegralSubring p))
    (hL : (localRationalMatrix L).det≠0) (hR : (localRationalMatrix R).det≠0)
    (hLi : PadicLower p 0 ((localRationalMatrix L).det⁻¹))
    (hRi : PadicLower p 0 ((localRationalMatrix R).det⁻¹)) (w : ℤ)
    (hU : PolynomialPadicLower p w
      (localBasisMatrix A L R).det) :
    PolynomialPadicLower p w A.det := by
  have h := (PolynomialPadicLower.constant (hLi.mul hRi)).mul hU
  rw [localMatrixPair_eq_matrix_product,Matrix.det_mul,Matrix.det_mul,Matrix.det_transpose,
    ←RingHom.map_det,←RingHom.map_det] at h
  have he : C ((localRationalMatrix L).det⁻¹*(localRationalMatrix R).det⁻¹)*
      (C ((localRationalMatrix L).det)*A.det*C ((localRationalMatrix R).det))=A.det := by
    have hLc : C ((localRationalMatrix L).det⁻¹)*C ((localRationalMatrix L).det)=(1:ℚ[X]) := by
      rw [←C_mul,inv_mul_cancel₀ hL,C_1]
    have hRc : C ((localRationalMatrix R).det⁻¹)*C ((localRationalMatrix R).det)=(1:ℚ[X]) := by
      rw [←C_mul,inv_mul_cancel₀ hR,C_1]
    calc
      _=(C ((localRationalMatrix L).det⁻¹)*C ((localRationalMatrix L).det))*
        (C ((localRationalMatrix R).det⁻¹)*C ((localRationalMatrix R).det))*A.det := by
          rw [C_mul];ring
      _=A.det := by rw [hLc,hRc];simp
  simpa only [zero_add,he] using h

end Zeta3.Arithmetic

import Zeta3.Arithmetic.SecondTransportAlgebra

/-!
# Two actual restriction kernels and their reduced bilinear form

The only form-identification input is a coefficient-zero residue equality
for the actual divided matrix pairing. The theorem chooses and lifts both
kernel-adapted bases, proves the off-kernel blocks vanish, identifies the
remaining residue matrix, and transports the determinant valuation back.
-/

noncomputable section
namespace Zeta3.Arithmetic
open Matrix Module Polynomial Finset OddZeta.FourValue Zeta5.Arithmetic
open scoped BigOperators
variable {p : ℕ} [Fact p.Prime]

theorem two_kernel_lower_of_residue_bilinear
    {ι V W : Type*} [Fintype ι] [DecidableEq ι]
    [AddCommGroup V] [Module (PadicResidueField p) V]
    [AddCommGroup W] [Module (PadicResidueField p) W]
    (A : Matrix ι ι ℚ[X])
    (f : (ι→PadicResidueField p) →ₗ[PadicResidueField p] V)
    (g : (ι→PadicResidueField p) →ₗ[PadicResidueField p] W)
    (B : f.ker →ₗ[PadicResidueField p] g.ker →ₗ[PadicResidueField p] PadicResidueField p)
    (b : ℕ)
    (hA : ∀i j,PolynomialPadicLower p 0 (A i j))
    (hleft : ∀x : ι→padicIntegralSubring p, f (localReducedVector x)=0 →
      ∀y : ι→padicIntegralSubring p,PolynomialPadicLower p 1 (localMatrixPair A x y))
    (hright : ∀y : ι→padicIntegralSubring p,g (localReducedVector y)=0 →
      ∀x : ι→padicIntegralSubring p,PolynomialPadicLower p 1 (localMatrixPair A x y))
    (hhigh : ∀i j k,0<k→PadicLower p 2 ((A i j).coeff k))
    (hform : ∀ (x : ι→padicIntegralSubring p) (hx : f (localReducedVector x)=0)
      (y : ι→padicIntegralSubring p) (hy : g (localReducedVector y)=0)
      (h : PadicLower p 0 ((C ((p:ℚ)⁻¹)*localMatrixPair A x y).coeff 0)),
      padicReduction p ⟨(C ((p:ℚ)⁻¹)*localMatrixPair A x y).coeff 0,h⟩=
        B ⟨localReducedVector x,hx⟩ ⟨localReducedVector y,hy⟩)
    (hrank : finrank (PadicResidueField p) B.range≤b) :
    PolynomialPadicLower p
      (2*(Fintype.card ι:ℤ)-finrank (PadicResidueField p) f.range-
        finrank (PadicResidueField p) g.range-b) A.det := by
  classical
  obtain ⟨L,S,hL,hLi,hS,hLS⟩ := exists_local_kernel_row_basis f
  obtain ⟨R,T,hR,hRi,hT,hRT⟩ := exists_local_kernel_row_basis g
  let U := localBasisMatrix A L R
  have hU (i j : ι) : PolynomialPadicLower p (if i∈S then 1 else 0) (U i j) := by
    by_cases hi : i∈S
    · simpa only [if_pos hi,U,localBasisMatrix] using hleft (L i) (hLS i hi) (R j)
    · simpa only [if_neg hi,U,localBasisMatrix] using localMatrixPair_padicLower A (L i) (R j) 0 hA
  have hZ := primeRowUnscale_integral U S hU
  have hZhigh : ∀i j,j∈T→∀k:ℕ,0<k→
      PadicLower p 1 ((primeRowUnscale (p:=p) U S i j).coeff k) := by
    intro i j hj k hk
    have hh := localMatrixPair_coeff_pos_padicLower A (L i) (R j) 2 hhigh k hk
    by_cases hi : i∈S
    · have hp1 : PadicLower p (-1) ((p:ℚ)⁻¹) := by
        simpa only [Nat.cast_one,pow_one] using inverse_prime_power_padicLower (p:=p) 1
      simpa [primeRowUnscale,hi,coeff_C_mul,U,localBasisMatrix] using hp1.mul hh
    · simpa only [primeRowUnscale,if_neg hi,U,localBasisMatrix] using hh.mono (by norm_num : (1:ℤ)≤2)
  let x : ι→f.ker := fun i => if hi : i∈S then ⟨localReducedVector (L i),hLS i hi⟩ else 0
  let y : ι→g.ker := fun j => if hj : j∈T then ⟨localReducedVector (R j),hRT j hj⟩ else 0
  have he : reducedConstantColumns (primeRowUnscale (p:=p) U S) hZ T=
      bilinearSampleMatrix B x y := by
    ext i j
    by_cases hi : i∈S
    · by_cases hj : j∈T
      · simp only [reducedConstantColumns,if_pos hj,bilinearSampleMatrix,x,y,dif_pos hi,dif_pos hj]
        simp only [primeRowUnscale,if_pos hi,U,localBasisMatrix]
        exact hform (L i) (hLS i hi) (R j) (hRT j hj) _
      · simp [reducedConstantColumns,hj,bilinearSampleMatrix,y]
    · by_cases hj : j∈T
      · simp only [reducedConstantColumns,if_pos hj,bilinearSampleMatrix,x,dif_neg hi,map_zero,
          LinearMap.zero_apply]
        apply (padicReduction_eq_zero _).mpr
        simpa only [primeRowUnscale,if_neg hi,U,localBasisMatrix] using (hright (R j) (hRT j hj) (L i)) 0
      · simp [reducedConstantColumns,hj,bilinearSampleMatrix,y]
  have hRank : finrank (PadicResidueField p)
      (LinearMap.range (reducedConstantColumns (primeRowUnscale (p:=p) U S) hZ T).mulVecLin)≤b := by
    change (reducedConstantColumns (primeRowUnscale (p:=p) U S) hZ T).rank≤b
    rw [he]
    exact (bilinearSampleMatrix_rank_le B x y).trans hrank
  have hdet := two_kernel_determinant_lower U S T hU hZhigh b hRank
  have hbase := polynomialPadicLower_det_of_local_basis A L R hL hR hLi hRi _ hdet
  apply hbase.mono
  have hf := f.finrank_range_add_finrank_ker
  have hg := g.finrank_range_add_finrank_ker
  rw [Module.finrank_fintype_fun_eq_card] at hf hg
  rw [hS,hT]
  omega

end Zeta3.Arithmetic

import Zeta3.Arithmetic.SecondBuckets
import Zeta3.Arithmetic.FullProfileCells

/-! Exact homogeneity of the nine continuous root-class intervals. -/
noncomputable section
namespace Zeta3.Arithmetic
open Finset Zeta5.Arithmetic Zeta3.Construction.Features ProfileCertificate
variable {p : ℕ} [Fact p.Prime]

theorem rootLowerReal_scaled (N m a : ℕ) (s : ℚ) (j : Fin 3) (hN : 0<N)
    (ha : m/p=a) (hs : (m:ℝ)=(N:ℝ)*(s:ℝ)) :
    rootLowerReal m p j=(N:ℝ)*(rootLowerExpr a s j).eval ((p:ℝ)/N) := by
  have hN0 : (N:ℝ)≠0 := by exact_mod_cast hN.ne'
  have hd : ((m%p:ℕ):ℝ)+(p:ℝ)*a=m := by
    have hh := Nat.mod_add_div m p
    rw [ha] at hh
    exact_mod_cast hh
  have hrem : ((m%p:ℕ):ℝ)=(N:ℝ)*((s:ℝ)-(a:ℝ)*((p:ℝ)/N)) := by
    field_simp
    nlinarith
  unfold rootLowerReal rootLowerExpr
  split_ifs
  · rw [remainderExpr_eval,hrem]
  · simp
  · rw [Expr.sub_eval,Expr.variable_eval,remainderExpr_eval,hrem]
    field_simp <;> ring

theorem rootUpperReal_scaled (N m a : ℕ) (s : ℚ) (j : Fin 3) (hN : 0<N)
    (ha : m/p=a) (hs : (m:ℝ)=(N:ℝ)*(s:ℝ)) :
    rootUpperReal m p j=(N:ℝ)*(rootUpperExpr a s j).eval ((p:ℝ)/N) := by
  have hN0 : (N:ℝ)≠0 := by exact_mod_cast hN.ne'
  have hd : ((m%p:ℕ):ℝ)+(p:ℝ)*a=m := by
    have hh := Nat.mod_add_div m p
    rw [ha] at hh
    exact_mod_cast hh
  have hrem : ((m%p:ℕ):ℝ)=(N:ℝ)*((s:ℝ)-(a:ℝ)*((p:ℝ)/N)) := by
    field_simp
    nlinarith
  have hrem' : (p:ℝ)-((m%p:ℕ):ℝ)=(N:ℝ)*((p:ℝ)/N-((s:ℝ)-(a:ℝ)*((p:ℝ)/N))) := by
    rw [hrem]
    field_simp <;> ring
  unfold rootUpperReal rootUpperExpr
  split_ifs
  · rw [Expr.eval,Expr.sub_eval,Expr.variable_eval,remainderExpr_eval,hrem',hrem,
      ← mul_min_of_nonneg _ _ (Nat.cast_nonneg N)]
  · simp only [Expr.eval,Affine.real,Rat.cast_zero,Rat.cast_div,Rat.cast_one,Rat.cast_ofNat,zero_add]
    field_simp <;> ring

theorem nonmaximalLowerReal_eq_width (N : ℕ) :
    nonmaximalLowerReal N p=if 2*(N%p)/p=0 then maximalWidth N p else 0 := by
  have hp := (Fact.out : p.Prime).pos
  unfold nonmaximalLowerReal maximalWidth
  rw [reflected_epsilon N p hp]
  split_ifs <;> norm_num at *

theorem nonmaximalUpperReal_eq_width (N : ℕ) :
    nonmaximalUpperReal N p=if 2*(N%p)/p=0 then (p:ℝ)/2 else (p:ℝ)/2-maximalWidth N p := by
  have hp := (Fact.out : p.Prime).pos
  unfold nonmaximalUpperReal maximalWidth
  rw [reflected_epsilon N p hp]
  split_ifs <;> norm_num at * <;> ring

theorem nonmaximalLowerReal_scaled (N : ℕ) (e : Environment) (hN : 0<N)
    (hq : N/p=e.q) (he : 2*(N%p)/p=e.eps) :
    nonmaximalLowerReal N p=(N:ℝ)*e.nonmaximalLowerExpr.eval ((p:ℝ)/N) := by
  rw [nonmaximalLowerReal_eq_width,he]
  unfold Environment.nonmaximalLowerExpr
  split_ifs
  · rw [widthExpr_eval,maximalWidth_scaled N e.q e.eps hN hq he]
  · simp

theorem nonmaximalUpperReal_scaled (N : ℕ) (e : Environment) (hN : 0<N)
    (hq : N/p=e.q) (he : 2*(N%p)/p=e.eps) :
    nonmaximalUpperReal N p=(N:ℝ)*e.nonmaximalUpperExpr.eval ((p:ℝ)/N) := by
  have hN0 : (N:ℝ)≠0 := by exact_mod_cast hN.ne'
  rw [nonmaximalUpperReal_eq_width,he]
  unfold Environment.nonmaximalUpperExpr
  split_ifs
  · simp only [Expr.eval,Affine.real,Rat.cast_zero,Rat.cast_div,Rat.cast_one,Rat.cast_ofNat,zero_add]
    field_simp <;> ring
  · rw [Expr.sub_eval,widthExpr_eval,maximalWidth_scaled N e.q e.eps hN hq he]
    simp only [Expr.eval,Affine.real,Rat.cast_zero,Rat.cast_div,Rat.cast_one,Rat.cast_ofNat,zero_add]
    field_simp <;> ring

theorem stage_pairBucketLength_scaled (n : ℕ) (e : Environment) (i j : Fin 3) (hn : 0<n)
    (hq : (50*n)/p=e.q) (he : 2*((50*n)%p)/p=e.eps)
    (ha₁ : (4*n)/p=e.a₁) (ha₂ : (16*n)/p=e.a₂) :
    pairBucketLength (50*n) (4*n) (16*n) p i j=
      ((50*n:ℕ):ℝ)*(e.bucketExpr i j).eval ((p:ℝ)/((50*n:ℕ):ℝ)) := by
  have hN : 0<50*n := by omega
  have hs₁ : ((4*n:ℕ):ℝ)=((50*n:ℕ):ℝ)*((2/25:ℚ):ℝ) := by push_cast; ring
  have hs₂ : ((16*n:ℕ):ℝ)=((50*n:ℕ):ℝ)*((8/25:ℚ):ℝ) := by push_cast; ring
  rw [pairBucketLength,nonmaximalUpperReal_scaled _ e hN hq he,
    nonmaximalLowerReal_scaled _ e hN hq he,
    rootLowerReal_scaled _ _ _ _ i hN ha₁ hs₁,
    rootLowerReal_scaled _ _ _ _ j hN ha₂ hs₂,
    rootUpperReal_scaled _ _ _ _ i hN ha₁ hs₁,
    rootUpperReal_scaled _ _ _ _ j hN ha₂ hs₂]
  simp only [Environment.bucketExpr,Expr.max_eval,Expr.const_eval,Expr.sub_eval,Expr.eval]
  rw [← mul_min_of_nonneg _ _ (Nat.cast_nonneg (50*n)),
    ← mul_min_of_nonneg _ _ (Nat.cast_nonneg (50*n)),
    ← mul_max_of_nonneg _ _ (Nat.cast_nonneg (50*n)),
    ← mul_max_of_nonneg _ _ (Nat.cast_nonneg (50*n)),← mul_sub,
    ← mul_zero ((50*n:ℕ):ℝ),← mul_max_of_nonneg _ _ (Nat.cast_nonneg (50*n))]
  norm_num

theorem kernelExpr_eval (q e D : ℕ) (ρ : ℚ) (β : ℝ) :
    (kernelExpr q e D ρ).eval β=max 0 ((ρ:ℝ)-(D:ℝ)*β/2-profileWidth q e β) := by
  simp only [kernelExpr,Expr.max_eval,Expr.const_eval,Expr.sub_eval,widthExpr_eval,
    Expr.eval,Affine.real,Rat.cast_neg,Rat.cast_div,Rat.cast_natCast,Rat.cast_ofNat]
  congr 2 <;> ring

theorem secondExpr_eval (e : Environment) (u₁ u₂ : ℕ) (β : ℝ) :
    (e.secondExpr u₁ u₂).eval β=
      (1+(e.eps:ℝ))*(51/50)+
      (featureExpr e.q e.eps e.d₁ e.a₁ (2/25) (11/10)).eval β+
      (featureExpr e.q e.eps e.d₂ e.a₂ (8/25) (67/50)).eval β+
      (∑ i:Fin 3, ∑ j:Fin 3,
        (numericCap e.eps e.d₁ e.d₂ (2*e.a₁+i.val) (2*e.a₂+j.val) u₁ u₂:ℝ)*
          (e.bucketExpr i j).eval β)+
      ((1-u₁:ℕ):ℝ)*(kernelExpr e.q e.eps e.d₁ (11/10)).eval β+
      ((1-u₂:ℕ):ℝ)*(kernelExpr e.q e.eps e.d₂ (67/50)).eval β := by
  simp only [Environment.secondExpr,Expr.eval,Expr.const_eval,sumThreeExpr_eval]
  push_cast
  rfl

end Zeta3.Arithmetic

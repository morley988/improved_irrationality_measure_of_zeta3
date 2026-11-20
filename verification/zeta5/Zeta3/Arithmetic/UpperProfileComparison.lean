import Zeta3.Arithmetic.ProfileCells
import Zeta3.Arithmetic.NormalizerLocalBounds
import Zeta5.Arithmetic.FactorialFloorSum

/-! Actual upper-band and large-prime charges versus the finite profiles. -/

noncomputable section
namespace Zeta3.Arithmetic
open Polynomial Finset Matrix Module OddZeta.FourValue Zeta5.Construction
open Zeta5.Arithmetic Zeta3.Construction.Features ProfileCertificate

theorem cubic_factorialCharge_real_bound (N m₁ m₂ r p : ℕ) (hp : 0<p) :
    (factorialCharge N m₁ m₂ r p:ℝ)≤
      ((2*(m₁+r)/p:ℕ):ℝ)*(m₁+r)+((2*(m₂+r)/p:ℕ):ℝ)*(m₂+r)-
      (p:ℝ)*(((2*(m₁+r)/p:ℕ):ℝ)*(((2*(m₁+r)/p:ℕ):ℝ)+1)+
        ((2*(m₂+r)/p:ℕ):ℝ)*(((2*(m₂+r)/p:ℕ):ℝ)+1))/4-
      2*r*((N/p:ℕ):ℝ) := by
  have h₁ := Zeta5.Arithmetic.factorialCharge_real_bound N m₁ r p hp
  have h₂ := Zeta5.Arithmetic.factorialCharge_real_bound N m₂ r p hp
  simp only [factorialCharge,Zeta5.Arithmetic.factorialCharge,Int.cast_sub,Int.cast_mul,
    Int.cast_add,Int.cast_ofNat,Int.cast_natCast,Int.cast_sum] at h₁ h₂ ⊢
  linarith

theorem cubic_factorialCharge_le_expression (n p : ℕ) (hn : 0<n) (hp : 0<p)
    (e : Environment) (hq : (50*n)/p=e.q) (h₁ : (110*n)/p=e.d₁) (h₂ : (134*n)/p=e.d₂) :
    (factorialCharge (50*n) (4*n) (16*n) (51*n) p:ℝ)≤
      (50*(n:ℝ))*e.factorialExpr.eval ((p:ℝ)/(50*n)) := by
  have h := cubic_factorialCharge_real_bound (50*n) (4*n) (16*n) (51*n) p hp
  rw [show 2*(4*n+51*n)=110*n by omega,show 2*(16*n+51*n)=134*n by omega,h₁,h₂,hq] at h
  convert h using 1
  simp only [Environment.factorialExpr,Expr.eval,Affine.real]
  push_cast
  have hn0 : (n:ℝ)≠0 := by exact_mod_cast hn.ne'
  field_simp
  ring

theorem savingExpr_eval (s : ℚ) (β : ℝ) :
    (ProfileCertificate.savingExpr s).eval β=min (s:ℝ) (1-β)+max 0 (1+(s:ℝ)-2*β) := by
  simp only [ProfileCertificate.savingExpr,Expr.eval,Expr.max_eval,Expr.const_eval,Affine.real]
  push_cast
  congr 2 <;> ring

theorem terminalExpr_eval (β : ℝ) :
    ProfileCertificate.terminalExpr.eval β=max 0 (36/25-β) := by
  simp only [ProfileCertificate.terminalExpr,Expr.max_eval,Expr.const_eval,Expr.eval,Affine.real]
  norm_num [sub_eq_add_neg]

theorem upperWindowSaving_real_lower (N m p : ℕ) (hp : 0<p)
    (hpN : p≤N) (hN : N<2*p) :
    min (m:ℝ) ((N:ℝ)-p)+max 0 ((m:ℝ)+N-2*p)-1≤(upperWindowSaving N m p:ℝ) := by
  rw [upperWindowSaving_eq N m p hp hpN,if_pos hN]
  have hmod : N%p=N-p := by
    rw [Nat.mod_eq_sub_mod hpN,Nat.mod_eq_of_lt (by omega : N-p<p)]
  rw [hmod,Nat.cast_add,Nat.cast_min,Nat.cast_sub hpN,nat_sub_cast_real (m+(N-p)) p]
  have hml : (m:ℝ)-1≤((m-1:ℕ):ℝ) := by
    rw [nat_sub_cast_real m 1,Nat.cast_one]
    exact le_max_right (0:ℝ) ((m:ℝ)-1)
  have hmin : min (m:ℝ) ((N:ℝ)-p)-1≤min ((m-1:ℕ):ℝ) ((N:ℝ)-p) := by
    apply le_min
    · linarith [min_le_left (m:ℝ) ((N:ℝ)-p)]
    · linarith [min_le_right (m:ℝ) ((N:ℝ)-p)]
  have he : ((m+(N-p):ℕ):ℝ)-(p:ℝ)=(m:ℝ)+N-2*p := by
    rw [Nat.cast_add,Nat.cast_sub hpN]
    ring
  rw [he]
  linarith

theorem upperHighCount_eq_sub (N p : ℕ) (hp : 0<p) (hpN : p≤N) (hN : N<2*p) :
    upperHighCount N p=N-p := by
  have hq : N/p=1 := by
    have hlow : 1≤N/p := (Nat.le_div_iff_mul_le hp).mpr (by simpa using hpN)
    have hhigh : N/p<2 := (Nat.div_lt_iff_lt_mul hp).mpr hN
    omega
  simp only [upperHighCount,hq,Nat.sub_self,Nat.sub_zero]

theorem mixedTerminalSize_real_bound (n p : ℕ) :
    (mixedTerminalSize (50*n) (4*n) (16*n) (51*n) p:ℝ)≤max 0 (72*(n:ℝ)-p)+1 := by
  rw [mixedTerminalSize_concrete,Nat.cast_min]
  apply (min_le_right _ _).trans
  rw [nat_sub_cast_real]
  push_cast
  rw [←max_add_add_right]
  apply max_le_max <;> linarith

theorem savingExpr_scaled (N m p : ℕ) (hN : 0<N) (s : ℚ) (hs : (m:ℝ)=(N:ℝ)*(s:ℝ)) :
    (N:ℝ)*(ProfileCertificate.savingExpr s).eval ((p:ℝ)/N)=
      min (m:ℝ) ((N:ℝ)-p)+max 0 ((m:ℝ)+N-2*p) := by
  rw [savingExpr_eval,mul_add,mul_min_of_nonneg _ _ (Nat.cast_nonneg N),
    mul_max_of_nonneg _ _ (Nat.cast_nonneg N)]
  have hN0 : (N:ℝ)≠0 := by exact_mod_cast hN.ne'
  rw [mul_zero,←hs]
  congr 2 <;> field_simp <;> nlinarith

theorem terminalExpr_scaled (n p : ℕ) (hn : 0<n) :
    (50*(n:ℝ))*ProfileCertificate.terminalExpr.eval ((p:ℝ)/(50*n))=
      max 0 (72*(n:ℝ)-p) := by
  rw [terminalExpr_eval,mul_max_of_nonneg _ _ (by positivity),mul_zero]
  congr 1
  have hn0 : (n:ℝ)≠0 := by exact_mod_cast hn.ne'
  field_simp
  ring

theorem upperExpr_eval (e : Environment) (β : ℝ) :
    e.upperExpr.eval β=e.factorialExpr.eval β+5*(1-β)-
      (ProfileCertificate.savingExpr (2/25)).eval β-(ProfileCertificate.savingExpr (8/25)).eval β+
      min (ProfileCertificate.terminalExpr.eval β) (1/50+β) := by
  simp only [Environment.upperExpr,Expr.eval,Expr.sub_eval,Affine.real]
  norm_num
  ring

theorem upperExpr_scaled (n p : ℕ) (hn : 0<n) (e : Environment) :
    (50*(n:ℝ))*e.upperExpr.eval ((p:ℝ)/(50*n))=
      (50*(n:ℝ))*e.factorialExpr.eval ((p:ℝ)/(50*n))+5*(50*(n:ℝ)-p)-
        (50*(n:ℝ))*(ProfileCertificate.savingExpr (2/25)).eval ((p:ℝ)/(50*n))-
        (50*(n:ℝ))*(ProfileCertificate.savingExpr (8/25)).eval ((p:ℝ)/(50*n))+
        min (max 0 (72*(n:ℝ)-p)) ((n:ℝ)+p) := by
  rw [upperExpr_eval]
  simp only [mul_add,mul_sub]
  rw [mul_min_of_nonneg _ _ (by positivity : (0:ℝ)≤50*n),terminalExpr_scaled n p hn]
  have hn0 : (n:ℝ)≠0 := by exact_mod_cast hn.ne'
  have hright : (50*(n:ℝ))*(1/50+(p:ℝ)/(50*n))=(n:ℝ)+p := by field_simp
  have hhigh : (50*(n:ℝ))*(5*(1-(p:ℝ)/(50*n)))=5*(50*(n:ℝ)-p) := by field_simp
  rw [hright]
  linear_combination hhigh

theorem largeCharge_le_expression (n p : ℕ) (hn : 0<n) (hp : 0<p)
    (e : Environment) (hq : (50*n)/p=e.q) (h₁ : (110*n)/p=e.d₁) (h₂ : (134*n)/p=e.d₂) :
    (largeCharge n p:ℝ)≤(50*(n:ℝ))*e.largeExpr.eval ((p:ℝ)/(50*n))+1 := by
  have hf := cubic_factorialCharge_le_expression n p hn hp e hq h₁ h₂
  have ht := mixedTerminalSize_real_bound n p
  simp only [Environment.largeExpr,Expr.eval,mul_add]
  rw [terminalExpr_scaled n p hn]
  simp only [largeCharge,Int.cast_add,Int.cast_natCast]
  linarith only [hf,ht]

theorem upperCharge_le_expression (n p : ℕ) (hn : 0<n) (hp : 0<p)
    (hpN : p≤50*n) (hN : 50*n<2*p)
    (e : Environment) (hq : (50*n)/p=e.q) (h₁ : (110*n)/p=e.d₁) (h₂ : (134*n)/p=e.d₂) :
    (upperCharge n p:ℝ)≤(50*(n:ℝ))*e.upperExpr.eval ((p:ℝ)/(50*n))+3 := by
  have hf := cubic_factorialCharge_le_expression n p hn hp e hq h₁ h₂
  have hs₁ := upperWindowSaving_real_lower (50*n) (4*n) p hp hpN hN
  have hs₂ := upperWindowSaving_real_lower (50*n) (16*n) p hp hpN hN
  have he₁ := savingExpr_scaled (50*n) (4*n) p (by omega) (2/25) (by push_cast;norm_num;ring)
  have he₂ := savingExpr_scaled (50*n) (16*n) p (by omega) (8/25) (by push_cast;norm_num;ring)
  push_cast at hs₁ hs₂ he₁ he₂
  have hhigh := upperHighCount_eq_sub (50*n) p hp hpN hN
  have hhr : (upperHighCount (50*n) p:ℝ)=50*(n:ℝ)-p := by
    rw [hhigh,Nat.cast_sub hpN]
    push_cast
    rfl
  have hr : ((51*n-upperHighCount (50*n) p:ℕ):ℝ)=(n:ℝ)+p := by
    have hh : upperHighCount (50*n) p≤51*n := by rw [hhigh];omega
    rw [Nat.cast_sub hh,hhr]
    push_cast
    ring
  have hterm : ((min (mixedTerminalSize (50*n) (4*n) (16*n) (51*n) p)
      (51*n-upperHighCount (50*n) p):ℕ):ℝ)≤min (max 0 (72*(n:ℝ)-p)) ((n:ℝ)+p)+1 := by
    rw [Nat.cast_min,hr,←min_add_add_right]
    exact min_le_min (mixedTerminalSize_real_bound n p) (by linarith)
  rw [upperExpr_scaled n p hn e]
  simp only [upperCharge,Int.cast_add,Int.cast_sub,Int.cast_mul,Int.cast_ofNat,Int.cast_natCast,hhr]
  linarith only [hf,hs₁,hs₂,he₁,he₂,hterm]

end Zeta3.Arithmetic

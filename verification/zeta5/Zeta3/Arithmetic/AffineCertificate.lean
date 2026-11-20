import Zeta5.Reuse.PrimePiecewise
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

/-! A finite rational checker for piecewise affine arithmetic profiles.
Successful endpoint comparisons prove the selected branch throughout the
whole cell, so external evidence never includes an all-real inequality. -/
noncomputable section
namespace Zeta3.Arithmetic.ProfileCertificate

structure Affine where
  intercept : ℚ
  slope : ℚ
  deriving DecidableEq, Repr

def Affine.eval (a : Affine) (x : ℚ) : ℚ := a.intercept+a.slope*x
noncomputable def Affine.real (a : Affine) (x : ℝ) : ℝ := a.intercept+a.slope*x

def Affine.add (a b : Affine) : Affine := ⟨a.intercept+b.intercept,a.slope+b.slope⟩
def Affine.neg (a : Affine) : Affine := ⟨-a.intercept,-a.slope⟩
def Affine.scale (s : ℚ) (a : Affine) : Affine := ⟨s*a.intercept,s*a.slope⟩

@[simp] theorem Affine.add_real (a b : Affine) (x : ℝ) :
    (a.add b).real x = a.real x+b.real x := by simp [add,real]; ring
@[simp] theorem Affine.neg_real (a : Affine) (x : ℝ) :
    a.neg.real x = -a.real x := by simp [neg,real]; ring
@[simp] theorem Affine.scale_real (s : ℚ) (a : Affine) (x : ℝ) :
    (a.scale s).real x = (s:ℝ)*a.real x := by simp [scale,real]; ring

def Affine.below (a b : Affine) (l r : ℚ) : Prop := a.eval l≤b.eval l ∧ a.eval r≤b.eval r
instance (a b : Affine) (l r : ℚ) : Decidable (a.below b l r) := inferInstanceAs (Decidable (_∧_))

theorem Affine.below_real {a b : Affine} {l r : ℚ} (h : a.below b l r)
    {x : ℝ} (hl : (l:ℝ)≤x) (hr : x≤(r:ℝ)) : a.real x≤b.real x := by
  have h₁ : a.real (l:ℝ)≤b.real (l:ℝ) := by
    have hh := h.1
    unfold eval at hh
    unfold real
    exact_mod_cast hh
  have h₂ : a.real (r:ℝ)≤b.real (r:ℝ) := by
    have hh := h.2
    unfold eval at hh
    unfold real
    exact_mod_cast hh
  unfold real at *
  by_cases hs : (a.slope:ℝ)≤b.slope
  · have hm := mul_le_mul_of_nonneg_right hl (sub_nonneg.mpr hs)
    nlinarith
  · have hm := mul_le_mul_of_nonneg_right hr (sub_nonneg.mpr (le_of_not_ge hs))
    nlinarith

inductive Expr where
  | affine (a : Affine)
  | add (a b : Expr)
  | neg (a : Expr)
  | scale (s : ℚ) (a : Expr)
  | min (a b : Expr)
  deriving DecidableEq, Repr

def Expr.max (a b : Expr) : Expr := .neg (.min (.neg a) (.neg b))
def Expr.sub (a b : Expr) : Expr := .add a (.neg b)
def Expr.const (a : ℚ) : Expr := .affine ⟨a,0⟩
def Expr.var : Expr := .affine ⟨0,1⟩

noncomputable def Expr.eval (x : ℝ) : Expr → ℝ
  | .affine a => a.real x
  | .add a b => a.eval x+b.eval x
  | .neg a => -a.eval x
  | .scale s a => (s:ℝ)*a.eval x
  | .min a b => Min.min (a.eval x) (b.eval x)

@[simp] theorem Expr.max_eval (a b : Expr) (x : ℝ) : (a.max b).eval x=Max.max (a.eval x) (b.eval x) := by
  simp only [Expr.max,Expr.eval]
  by_cases h : a.eval x≤b.eval x
  · rw [min_eq_right (neg_le_neg h),neg_neg,max_eq_right h]
  · rw [min_eq_left (neg_le_neg (le_of_not_ge h)),neg_neg,max_eq_left (le_of_not_ge h)]
@[simp] theorem Expr.sub_eval (a b : Expr) (x : ℝ) : (a.sub b).eval x=a.eval x-b.eval x := rfl
@[simp] theorem Expr.const_eval (a : ℚ) (x : ℝ) : (Expr.const a).eval x=(a:ℝ) := by simp [const,eval,Affine.real]
@[simp] theorem Expr.variable_eval (x : ℝ) : Expr.var.eval x=x := by simp [Expr.var,eval,Affine.real]

def Expr.normalize (l r : ℚ) : Expr → Option Affine
  | .affine a => some a
  | .add a b => match a.normalize l r, b.normalize l r with
      | some u, some v => some (u.add v)
      | _, _ => none
  | .neg a => match a.normalize l r with
      | some u => some u.neg
      | none => none
  | .scale s a => match a.normalize l r with
      | some u => some (u.scale s)
      | none => none
  | .min a b => match a.normalize l r, b.normalize l r with
      | some u, some v => if u.below v l r then some u
          else if v.below u l r then some v else none
      | _, _ => none

theorem Expr.normalize_sound (e : Expr) {l r : ℚ} {a : Affine}
    (h : e.normalize l r=some a) {x : ℝ} (hl : (l:ℝ)≤x) (hr : x≤(r:ℝ)) :
    e.eval x=a.real x := by
  induction e generalizing a with
  | affine u =>
    have he : u=a := Option.some.inj h
    subst a
    rfl
  | add u v ihu ihv =>
    cases hu : u.normalize l r with
    | none => simp [normalize,hu] at h
    | some U =>
      cases hv : v.normalize l r with
      | none => simp [normalize,hu,hv] at h
      | some V =>
        simp only [normalize,hu,hv,Option.bind_some,Option.some.injEq] at h
        subst a
        simp only [eval,ihu hu,ihv hv,Affine.add_real]
  | neg u ihu =>
    cases hu : u.normalize l r with
    | none => simp [normalize,hu] at h
    | some U =>
      simp only [normalize,hu,Option.bind_some,Option.some.injEq] at h
      subst a
      simp only [eval,ihu hu,Affine.neg_real]
  | scale s u ihu =>
    cases hu : u.normalize l r with
    | none => simp [normalize,hu] at h
    | some U =>
      simp only [normalize,hu,Option.bind_some,Option.some.injEq] at h
      subst a
      simp only [eval,ihu hu,Affine.scale_real]
  | min u v ihu ihv =>
    cases hu : u.normalize l r with
    | none => simp [normalize,hu] at h
    | some U =>
      cases hv : v.normalize l r with
      | none => simp [normalize,hu,hv] at h
      | some V =>
        simp only [normalize,hu,hv,Option.bind_some] at h
        by_cases hUV : U.below V l r
        · simp only [if_pos hUV,Option.some.injEq] at h
          subst a
          simp only [eval,ihu hu,ihv hv,min_eq_left (Affine.below_real hUV hl hr)]
        · by_cases hVU : V.below U l r
          · simp only [if_neg hUV,if_pos hVU,Option.some.injEq] at h
            subst a
            simp only [eval,ihu hu,ihv hv,min_eq_right (Affine.below_real hVU hl hr)]
          · simp [hUV,hVU] at h

end Zeta3.Arithmetic.ProfileCertificate

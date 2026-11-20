import Zeta3.Arithmetic.ContinuousProfiles

/-! Finite rational cells for the cubic arithmetic profile. Floor bands,
branch choices and endpoint affine comparisons are all finite data. -/
noncomputable section
namespace Zeta3.Arithmetic.ProfileCertificate
open Zeta3.Arithmetic

def widthExpr (q e : ℕ) : Expr := .affine ⟨1,-((q:ℚ)+(e:ℚ)/2)⟩
def remainderExpr (a : ℕ) (s : ℚ) : Expr := .affine ⟨s,-(a:ℚ)⟩
def prefixExpr (a : ℕ) (s : ℚ) (x : Expr) : Expr :=
  .add (.add (.scale (2*a) x) (.min x (remainderExpr a s)))
    (Expr.max (.const 0) ((x.add (remainderExpr a s)).sub .var))
def rootCountExpr (q e a : ℕ) (s : ℚ) : Expr :=
  if e=0 then prefixExpr a s (widthExpr q e)
  else (prefixExpr a s (.affine ⟨0,1/2⟩)).sub
    (prefixExpr a s ((Expr.affine ⟨0,1/2⟩).sub (widthExpr q e)))
def featureExpr (q e D a : ℕ) (s ρ : ℚ) : Expr :=
  .add ((Expr.scale D (widthExpr q e)).sub (rootCountExpr q e a s))
    (.min (.affine ⟨ρ,-(D:ℚ)/2⟩) (widthExpr q e))

@[simp] theorem widthExpr_eval (q e : ℕ) (β : ℝ) :
    (widthExpr q e).eval β=profileWidth q e β := by
  simp [widthExpr,Expr.eval,Affine.real,profileWidth]
  ring
@[simp] theorem remainderExpr_eval (a : ℕ) (s : ℚ) (β : ℝ) :
    (remainderExpr a s).eval β=(s:ℝ)-(a:ℝ)*β := by
  simp [remainderExpr,Expr.eval,Affine.real]
  ring

theorem prefixExpr_eval (a : ℕ) (s : ℚ) (x : Expr) (β : ℝ) :
    (prefixExpr a s x).eval β=rootPrefixProfile a ((s:ℝ)-(a:ℝ)*β) (x.eval β) β := by
  simp only [prefixExpr,Expr.eval,Expr.max_eval,Expr.const_eval,Expr.sub_eval,
    Expr.variable_eval,remainderExpr_eval,rootPrefixProfile]
  push_cast
  rfl

theorem rootCountExpr_eval (q e a : ℕ) (s : ℚ) (β : ℝ) :
    (rootCountExpr q e a s).eval β=profileRootCount q e a s β := by
  unfold rootCountExpr profileRootCount
  split_ifs
  · rw [prefixExpr_eval,widthExpr_eval]
  · rw [Expr.sub_eval,prefixExpr_eval,prefixExpr_eval,Expr.sub_eval,widthExpr_eval]
    simp only [Expr.eval,Affine.real,Rat.cast_zero,Rat.cast_div,Rat.cast_one,Rat.cast_ofNat,zero_add]
    congr 2 <;> ring

theorem featureExpr_eval (q e D a : ℕ) (s ρ : ℚ) (β : ℝ) :
    (featureExpr q e D a s ρ).eval β=featureShape q e D a s ρ β := by
  simp only [featureExpr,Expr.eval,Expr.sub_eval,widthExpr_eval,rootCountExpr_eval,featureShape,
    Affine.real,Rat.cast_neg,Rat.cast_div,Rat.cast_natCast,Rat.cast_ofNat]
  congr 2 <;> ring

structure Environment where
  q : ℕ
  epsilon : Bool
  d₁ : ℕ
  d₂ : ℕ
  a₁ : ℕ
  a₂ : ℕ
  deriving DecidableEq, Repr

def Environment.eps (e : Environment) : ℕ := if e.epsilon then 1 else 0

def Environment.firstExpr (e : Environment) : Expr :=
  .add (.const ((2+e.eps)*(51/50)))
    (.min (featureExpr e.q e.eps e.d₁ e.a₁ (2/25) (11/10))
      (featureExpr e.q e.eps e.d₂ e.a₂ (8/25) (67/50)))

def Environment.factorialExpr (e : Environment) : Expr :=
  .affine ⟨(e.d₁:ℚ)*(11/10)+(e.d₂:ℚ)*(67/50)-2*(51/50)*e.q,
    -((e.d₁:ℚ)*(e.d₁+1)+(e.d₂:ℚ)*(e.d₂+1))/4⟩

def terminalExpr : Expr := Expr.max (.const 0) (.affine ⟨36/25,-1⟩)
def savingExpr (s : ℚ) : Expr :=
  .add (.min (.const s) (.affine ⟨1,-1⟩)) (Expr.max (.const 0) (.affine ⟨1+s,-2⟩))

def Environment.upperExpr (e : Environment) : Expr :=
  .add (((e.factorialExpr.add (.affine ⟨5,-5⟩)).sub (savingExpr (2/25))).sub (savingExpr (8/25)))
    (.min terminalExpr (.affine ⟨1/50,1⟩))

def Environment.largeExpr (e : Environment) : Expr := e.factorialExpr.add terminalExpr

inductive Regime where
  | middle
  | upper
  | large
  deriving DecidableEq, Repr

def Environment.expr (e : Environment) : Regime → Expr
  | .middle => e.firstExpr
  | .upper => .min e.firstExpr e.upperExpr
  | .large => e.largeExpr

def FloorBand (lo hi value : ℚ) (q : ℕ) : Prop := (q:ℚ)*hi≤value ∧ value≤(q+1)*lo
instance (lo hi value : ℚ) (q : ℕ) : Decidable (FloorBand lo hi value q) := inferInstanceAs (Decidable (_∧_))

theorem FloorBand.floor {lo hi value : ℚ} {q : ℕ}
    (h : FloorBand lo hi value q) (hlo : 0<lo) {β : ℝ}
    (hl : (lo:ℝ)<β) (hr : β<(hi:ℝ)) : ⌊(value:ℝ)/β⌋₊=q := by
  have hβ : 0<β := lt_trans (by exact_mod_cast hlo) hl
  have hqhi : (q:ℝ)*(hi:ℝ)≤(value:ℝ) := by exact_mod_cast h.1
  have hqlo : (value:ℝ)≤((q:ℝ)+1)*(lo:ℝ) := by exact_mod_cast h.2
  have hle : (q:ℝ)≤(value:ℝ)/β := (le_div_iff₀ hβ).mpr
    ((mul_le_mul_of_nonneg_left hr.le (Nat.cast_nonneg _)).trans hqhi)
  apply (Nat.floor_eq_iff ((Nat.cast_nonneg q).trans hle)).mpr
  exact ⟨hle, (div_lt_iff₀ hβ).mpr (hqlo.trans_lt (mul_lt_mul_of_pos_left hl (by positivity)))⟩

structure Cell where
  lo : ℚ
  hi : ℚ
  environment : Environment
  regime : Regime
  affine : Affine
  deriving DecidableEq, Repr

def Cell.Valid (c : Cell) : Prop :=
  0<c.lo ∧ c.lo<c.hi ∧
  FloorBand c.lo c.hi 1 c.environment.q ∧
  FloorBand c.lo c.hi (11/5) c.environment.d₁ ∧
  FloorBand c.lo c.hi (67/25) c.environment.d₂ ∧
  FloorBand c.lo c.hi (2/25) c.environment.a₁ ∧
  FloorBand c.lo c.hi (8/25) c.environment.a₂ ∧
  (if c.environment.epsilon then (2*(c.environment.q:ℚ)+1)*c.hi≤2
    else 2≤(2*(c.environment.q:ℚ)+1)*c.lo) ∧
  (match c.regime with
    | .middle => c.hi≤1
    | .upper => 16/25≤c.lo ∧ c.hi≤1
    | .large => 1≤c.lo) ∧
  (c.environment.expr c.regime).normalize c.lo c.hi=some c.affine

instance (c : Cell) : Decidable c.Valid := by
  unfold Cell.Valid
  cases c.regime <;> dsimp <;> infer_instance

def Cell.toPiece (c : Cell) : Zeta5.Reuse.PrimePiecewise.AffinePiece :=
  ⟨c.lo,c.hi,c.affine.intercept,c.affine.slope⟩

theorem Cell.toPiece_valid {c : Cell} (h : c.Valid) : c.toPiece.Valid := by
  change 0<(c.lo:ℝ) ∧ (c.lo:ℝ)≤(c.hi:ℝ)
  constructor
  · exact_mod_cast h.1
  · exact_mod_cast h.2.1.le

theorem Cell.expression_affine {c : Cell} (h : c.Valid) {β : ℝ}
    (hl : (c.lo:ℝ)<β) (hr : β<(c.hi:ℝ)) :
    (c.environment.expr c.regime).eval β=c.affine.real β := by
  rcases h with ⟨_,_,_,_,_,_,_,_,_,hnorm⟩
  exact Expr.normalize_sound _ hnorm hl.le hr.le

end Zeta3.Arithmetic.ProfileCertificate

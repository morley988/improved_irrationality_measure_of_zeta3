import Zeta3.Arithmetic.SecondNumeric
import Zeta3.Arithmetic.CellParameters

/-! Finite expression tree for the complete second-layer arithmetic
profile. Its only decisions are natural-number parity and rational affine
comparisons on a finite list of cells. -/
noncomputable section
namespace Zeta3.Arithmetic.ProfileCertificate
open Zeta3.Arithmetic

def sumThreeExpr (f : Fin 3 → Expr) : Expr := (f 0).add ((f 1).add (f 2))

theorem sumThreeExpr_eval (f : Fin 3 → Expr) (β : ℝ) :
    (sumThreeExpr f).eval β=∑ i:Fin 3,(f i).eval β := by
  simp [sumThreeExpr,Expr.eval,Fin.sum_univ_succ]

def rootLowerExpr (a : ℕ) (s : ℚ) (j : Fin 3) : Expr :=
  if j.val=0 then remainderExpr a s else if j.val=1 then .const 0
  else Expr.var.sub (remainderExpr a s)
def rootUpperExpr (a : ℕ) (s : ℚ) (j : Fin 3) : Expr :=
  if j.val=1 then .min (remainderExpr a s) (Expr.var.sub (remainderExpr a s))
  else .affine ⟨0,1/2⟩

def Environment.nonmaximalLowerExpr (e : Environment) : Expr :=
  if e.eps=0 then widthExpr e.q e.eps else .const 0
def Environment.nonmaximalUpperExpr (e : Environment) : Expr :=
  if e.eps=0 then .affine ⟨0,1/2⟩ else (Expr.affine ⟨0,1/2⟩).sub (widthExpr e.q e.eps)

def Environment.bucketExpr (e : Environment) (i j : Fin 3) : Expr :=
  Expr.max (.const 0)
    ((Expr.min e.nonmaximalUpperExpr
      (.min (rootUpperExpr e.a₁ (2/25) i) (rootUpperExpr e.a₂ (8/25) j))).sub
    (Expr.max e.nonmaximalLowerExpr
      (Expr.max (rootLowerExpr e.a₁ (2/25) i) (rootLowerExpr e.a₂ (8/25) j))))

def kernelExpr (q e D : ℕ) (ρ : ℚ) : Expr :=
  Expr.max (.const 0) ((Expr.affine ⟨ρ,-(D:ℚ)/2⟩).sub (widthExpr q e))

def Environment.secondExpr (e : Environment) (u₁ u₂ : ℕ) : Expr :=
  (((((Expr.const ((1+e.eps)*(51/50))).add
    (featureExpr e.q e.eps e.d₁ e.a₁ (2/25) (11/10))).add
    (featureExpr e.q e.eps e.d₂ e.a₂ (8/25) (67/50))).add
    (sumThreeExpr (fun i => sumThreeExpr (fun j =>
      .scale (numericCap e.eps e.d₁ e.d₂ (2*e.a₁+i.val) (2*e.a₂+j.val) u₁ u₂)
        (e.bucketExpr i j))))).add
    (.scale ((1-u₁:ℕ):ℚ) (kernelExpr e.q e.eps e.d₁ (11/10)))).add
    (.scale ((1-u₂:ℕ):ℚ) (kernelExpr e.q e.eps e.d₂ (67/50)))

def Environment.fullMiddleExpr (e : Environment) : Expr :=
  .min e.firstExpr
    (.min (.min (e.secondExpr 0 0) (e.secondExpr 0 1))
      (.min (e.secondExpr 1 0) (e.secondExpr 1 1)))

def Environment.fullExpr (e : Environment) : Regime → Expr
  | .middle => e.fullMiddleExpr
  | .upper => .min e.fullMiddleExpr e.upperExpr
  | .large => e.largeExpr

def Cell.FullValid (c : Cell) : Prop :=
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
  (c.environment.fullExpr c.regime).normalize c.lo c.hi=some c.affine

instance (c : Cell) : Decidable c.FullValid := by
  unfold Cell.FullValid
  cases c.regime <;> dsimp <;> infer_instance

theorem Cell.full_toPiece_valid {c : Cell} (h : c.FullValid) : c.toPiece.Valid := by
  change 0<(c.lo:ℝ) ∧ (c.lo:ℝ)≤(c.hi:ℝ)
  constructor
  · exact_mod_cast h.1
  · exact_mod_cast h.2.1.le

theorem Cell.full_expression_affine {c : Cell} (h : c.FullValid) {β : ℝ}
    (hl : (c.lo:ℝ)<β) (hr : β<(c.hi:ℝ)) :
    (c.environment.fullExpr c.regime).eval β=c.affine.real β := by
  rcases h with ⟨_,_,_,_,_,_,_,_,_,hnorm⟩
  exact Expr.normalize_sound _ hnorm hl.le hr.le

end Zeta3.Arithmetic.ProfileCertificate

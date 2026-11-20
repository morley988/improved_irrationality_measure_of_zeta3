import Zeta3.Arithmetic.ProfileCells
import Zeta3.Arithmetic.PrimeStripAssembly

/-!
# Finite rational coverage and area certificates

Only rational cell endpoints and coefficients occur in the certificate.
Its soundness theorem supplies the real-cell coverage and finite area
needed by the already-proved prime-sum limit. It makes no assumption about
the actual valuations or their asymptotic behavior.
-/

noncomputable section
namespace Zeta3.Arithmetic.ProfileCertificate
open Zeta5.Reuse.PrimePiecewise

def RationalCellsFit (start : ℚ) : List Cell → ℚ → Prop
  | [], finish => start=finish
  | c::cs, finish => c.lo=start ∧ c.lo≤c.hi ∧ RationalCellsFit c.hi cs finish

instance (start finish : ℚ) (cells : List Cell) : Decidable (RationalCellsFit start cells finish) := by
  induction cells generalizing start with
  | nil => exact inferInstanceAs (Decidable (start=finish))
  | cons c cs ih =>
    haveI := ih c.hi
    exact inferInstanceAs (Decidable (c.lo=start ∧ c.lo≤c.hi ∧ RationalCellsFit c.hi cs finish))

theorem RationalCellsFit.toReal {start finish : ℚ} {cells : List Cell}
    (h : RationalCellsFit start cells finish) :
    CellsFit (start:ℝ) (cells.map Cell.toPiece) (finish:ℝ) := by
  induction cells generalizing start with
  | nil =>
    change start=finish at h
    change (start:ℝ)=(finish:ℝ)
    exact_mod_cast h
  | cons c cs ih =>
    rcases h with ⟨hl,hh,ht⟩
    change (c.lo:ℝ)=(start:ℝ) ∧ (c.lo:ℝ)≤(c.hi:ℝ) ∧
      CellsFit (c.hi:ℝ) (cs.map Cell.toPiece) (finish:ℝ)
    exact ⟨by exact_mod_cast hl,by exact_mod_cast hh,ih ht⟩

def Cell.rationalArea (c : Cell) : ℚ :=
  c.affine.intercept*(c.hi-c.lo)+c.affine.slope*(c.hi^2-c.lo^2)/2

def finiteRationalArea (cells : List Cell) : ℚ := (cells.map Cell.rationalArea).sum

theorem Cell.area_toPiece (c : Cell) : c.toPiece.area=(c.rationalArea:ℝ) := by
  simp only [AffinePiece.area,Cell.toPiece,Cell.rationalArea]
  push_cast
  rfl

theorem finiteArea_toPieces (cells : List Cell) :
    finiteArea (cells.map Cell.toPiece)=(finiteRationalArea cells:ℝ) := by
  induction cells with
  | nil => simp [finiteArea,finiteRationalArea]
  | cons c cs ih =>
    simp only [finiteArea,finiteRationalArea,List.map_cons,List.sum_cons,Rat.cast_add] at ih ⊢
    rw [Cell.area_toPiece,ih]

def CoverageCertificate (cells : List Cell) (upper : ℚ) : Prop :=
  RationalCellsFit (1/500) cells (67/25) ∧ (51/6250:ℚ)+finiteRationalArea cells≤upper

instance (cells : List Cell) (upper : ℚ) : Decidable (CoverageCertificate cells upper) :=
  inferInstanceAs (Decidable (_∧_))

theorem CoverageCertificate.cellsFit {cells : List Cell} {upper : ℚ}
    (h : CoverageCertificate cells upper) :
    CellsFit (1/500) (cells.map Cell.toPiece) (67/25) := by
  simpa only [Rat.cast_div,Rat.cast_one,Rat.cast_ofNat] using h.1.toReal

theorem CoverageCertificate.valid {cells : List Cell} {upper : ℚ}
    (h : CoverageCertificate cells upper) :
    ∀ c∈cells.map Cell.toPiece,c.Valid := h.cellsFit.valid (by norm_num)

theorem CoverageCertificate.area_bound {cells : List Cell} {upper : ℚ}
    (h : CoverageCertificate cells upper) :
    (51/6250:ℝ)+finiteArea (cells.map Cell.toPiece)≤(upper:ℝ) := by
  rw [finiteArea_toPieces]
  have hh := (Rat.cast_le (K:=ℝ)).mpr h.2
  simpa only [Rat.cast_add,Rat.cast_div,Rat.cast_ofNat] using hh

end Zeta3.Arithmetic.ProfileCertificate

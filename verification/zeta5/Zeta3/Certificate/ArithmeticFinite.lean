import Zeta3.Arithmetic.FullCellsData
import Zeta3.Arithmetic.CellCoverage

/-!
# The exact finite arithmetic check

The check below is a closed Boolean computation over rational numbers and
natural numbers. Its soundness is proved here. A runtime evaluation of the
Boolean is external evidence in the hybrid stage; it is not silently
treated as a kernel proof. No actual valuation or limiting statement is a
field of this certificate.
-/

namespace Zeta3.Certificate
open Zeta3.Arithmetic.ProfileCertificate

def arithmeticFiniteCheck : Bool :=
  decide (CoverageCertificate fullCells fullArithmeticUpper) &&
    fullCells.all (fun c => decide c.FullValid)

structure ArithmeticFiniteEvidence : Prop where
  cells_valid : ∀ c∈fullCells,c.FullValid
  coverage : CoverageCertificate fullCells fullArithmeticUpper

theorem arithmeticFiniteCheck_sound (h : arithmeticFiniteCheck=true) : ArithmeticFiniteEvidence := by
  change (decide (CoverageCertificate fullCells fullArithmeticUpper) &&
    fullCells.all (fun c => decide c.FullValid))=true at h
  obtain ⟨hc,hv⟩ := Bool.and_eq_true_iff.mp h
  refine ⟨?_,of_decide_eq_true hc⟩
  intro c hmem
  exact of_decide_eq_true ((List.all_eq_true.mp hv) c hmem)

end Zeta3.Certificate

import Zeta3.Certificate.ArithmeticFinite

/-!
Exact runtime evaluation of the actual Lean finite-cell predicates.
Success is external numerical evidence, not a kernel certificate.
-/

open Zeta3.Arithmetic.ProfileCertificate

def main : IO Unit := do
  let cover := decide (RationalCellsFit (1/500) fullCells (67/25))
  unless cover do
    throw (IO.userError "FAIL: the actual Lean cells do not cover the required interval")
  let area := decide ((51/6250:ℚ)+finiteRationalArea fullCells≤fullArithmeticUpper)
  unless area do
    throw (IO.userError "FAIL: the actual Lean rational profile area exceeds its target")
  let valid := fullCells.all (fun c => decide c.FullValid)
  unless valid do
    throw (IO.userError "FAIL: an actual Lean cell fails its finite guards or affine normalization")
  IO.println s!"PASS: {fullCells.length} cells; exact Lean runtime coverage, area, floor guards, parity choices, and affine branches."
  IO.println "Trust boundary: this execution is external numerical evidence, not a Lean kernel proof of arithmeticFiniteCheck = true."

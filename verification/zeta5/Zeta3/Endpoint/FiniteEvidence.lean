import Zeta3.Arithmetic.FullProfileComparison
import Zeta3.Certificate.ArithmeticFinite
import Zeta3.Endpoint.ArithmeticCellRate
import Zeta3.Endpoint.RiemannZetaBound

/-!
# The complete mathematical implication from finite numerical evidence

All mathematical construction, rank, valuation, asymptotic, and transfer
arguments are discharged here. The two inputs consist only of seven fixed
finite real-expression inequalities and the exact finite rational profile
checks. Optional trusted connectors are imported only by the hybrid module.
-/

noncomputable section
namespace Zeta3.Endpoint
open Filter Zeta3.Arithmetic Zeta3.Arithmetic.ProfileCertificate
open scoped Topology

theorem actualArithmeticRate_of_finiteEvidence (h : Certificate.ArithmeticFiniteEvidence) :
    ActualArithmeticRate := by
  apply actualArithmeticRate_of_finite_cells fullCells fullArithmeticUpper h.coverage
    (by norm_num [fullArithmeticUpper,Parameters.arithmeticUpper]) 20000 (by norm_num) 2
  filter_upwards [smallPrimeCutoff_eventually_lt_middle,eventually_gt_atTop (0:ℕ)] with n hcut hn
  intro c hc p hp hl hr hstrip
  letI : Fact p.Prime := ⟨hp⟩
  have hc' : c.toPiece∈fullCells.map Cell.toPiece := List.mem_map.mpr ⟨c,hc,rfl⟩
  have hlo := (h.coverage.cellsFit.bounds c.toPiece hc').1
  have hβ : (1/500:ℝ)<(p:ℝ)/(50*n) := by
    have hh : (1/500:ℝ)<(p:ℝ)/((50*n:ℕ):ℝ) := hlo.trans_lt hl
    simpa only [Nat.cast_mul,Nat.cast_ofNat] using hh
  obtain ⟨hp5,hstrong⟩ := prime_strong_of_fixed_cutoff hn hcut.le hβ
  exact windowNormalizer_fullCell_uniform n hn (by omega) hstrong c (h.cells_valid c hc)
    hl hr hstrip hβ

theorem riemannZeta_three_exponent_le_of_finiteEvidence
    (hanalytic : Certificate.FiniteNumericalEvidence) (harithmetic : Certificate.ArithmeticFiniteEvidence) :
    Zeta3.Transfer.HasApproximationExponentLE (riemannZeta 3).re Parameters.target :=
  riemannZeta_three_exponent_le_of_arithmetic_rate hanalytic
    (actualArithmeticRate_of_finiteEvidence harithmetic)

theorem riemannZeta_three_irrational_of_finiteEvidence
    (hanalytic : Certificate.FiniteNumericalEvidence) (harithmetic : Certificate.ArithmeticFiniteEvidence) :
    Irrational (riemannZeta 3).re :=
  (riemannZeta_three_exponent_le_of_finiteEvidence hanalytic harithmetic).irrational

theorem riemannZeta_three_rational_separation_of_finiteEvidence
    (hanalytic : Certificate.FiniteNumericalEvidence) (harithmetic : Certificate.ArithmeticFiniteEvidence) :
    ∀ ν : ℝ, Parameters.target<ν → ∃ Q : ℕ, ∀ q : ℕ, Q≤q → ∀ p : ℤ,
      (q:ℝ)^(-ν)≤|(riemannZeta 3).re-(p:ℝ)/(q:ℝ)| := by
  intro ν hν
  exact eventually_atTop.mp
    (riemannZeta_three_exponent_le_of_finiteEvidence hanalytic harithmetic ν hν)

end Zeta3.Endpoint

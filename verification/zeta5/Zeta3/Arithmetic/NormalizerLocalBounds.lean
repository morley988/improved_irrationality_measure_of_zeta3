import Zeta3.Arithmetic.LocalDeterminant
import Zeta3.Arithmetic.SmallPrimeEntries
import Zeta3.Arithmetic.LargePrimes
import Zeta3.Analysis.CubicPositivity
import Zeta5.Arithmetic.NormalizerBounds

/-! The concrete primitive normalizer inherits the proved cubic local
bounds, including signed charges. Nonvanishing is discharged by the
actual physical positive Gram matrix at ζ(3). -/
noncomputable section
namespace Zeta3.Arithmetic
open Polynomial OddZeta.FourValue Zeta3.Construction
open Zeta5.Arithmetic Zeta5.Endpoint
variable {p : ℕ} [Fact p.Prime]

theorem windowDeterminant_ne_zero (n : ℕ) : windowDeterminant n ≠ 0 := by
  intro hzero
  have hmap := windowIntegerPolynomial_map n
  rw [hzero, mul_zero] at hmap
  apply Zeta3.Analysis.PhysicalMeasure.windowIntegerPolynomial_ne_zero n
  exact (Polynomial.map_eq_zero_iff (Int.cast_injective :
    Function.Injective (algebraMap ℤ ℚ))).mp hmap

def stageRankCost (n p : ℕ) : ℕ :=
  (2 + 2 * ((50 * n) % p) / p) * (51 * n) +
    min (51 * n) (((110 * n - 2) / p + 1) * (maximalReflectedClasses (50 * n) p).card)

theorem stageRankCost_le_four_dimension (n : ℕ) : stageRankCost n p ≤ 4 * (51 * n) := by
  have heps : 2 * ((50 * n) % p) / p ≤ 1 := by
    rw [reflected_epsilon (50 * n) p (Fact.out : p.Prime).pos]
    split_ifs <;> omega
  have hmin : min (51 * n) (((110 * n - 2) / p + 1) *
      (maximalReflectedClasses (50 * n) p).card) ≤ 51 * n := min_le_left _ _
  unfold stageRankCost
  nlinarith

theorem windowDeterminant_stageRankCost (n : ℕ) (hp : 2 < p)
    (hsmall : 268 * n + 4 < p ^ 2) :
    PolynomialPadicLower p (-(stageRankCost n p : ℤ)) (windowDeterminant n) := by
  have h := windowDeterminant_local_restriction_bound (p := p) n hp hsmall
  unfold stageRankCost
  rw [maximalReflectedClasses_card (50 * n) p
    ((Fact.out : p.Prime).mod_two_eq_one_iff_ne_two.mpr (by omega))]
  convert h using 1
  push_cast
  ring

theorem windowNormalizer_rankCost_bound (n : ℕ) (hp : 2 < p)
    (hsmall : 268 * n + 4 < p ^ 2) :
    padicValRat p (windowNormalizer n) ≤ (stageRankCost n p : ℤ) := by
  have h := primitiveNormalizer_padicVal_le (windowDeterminant n)
    (windowDeterminant_ne_zero n) p (-(stageRankCost n p : ℤ))
    (windowDeterminant_stageRankCost n hp hsmall)
  simpa only [windowNormalizer, neg_neg] using h

theorem windowNormalizer_goodPrime_bound (n : ℕ) (hp : 2 < p)
    (hsmall : 268 * n + 4 < p ^ 2) :
    padicValRat p (windowNormalizer n) ≤ (204 * n : ℕ) := by
  have h := windowNormalizer_rankCost_bound (p := p) n hp hsmall
  have hcost : (stageRankCost n p : ℤ) ≤ (204 * n : ℕ) := by
    exact_mod_cast (by simpa only [show 4 * (51 * n) = 204 * n by omega] using
      stageRankCost_le_four_dimension (p := p) n)
  exact h.trans hcost

theorem windowNormalizer_nonpos_above_window (n : ℕ) (hn : 0 < n) (hp : 134 * n < p) :
    padicValRat p (windowNormalizer n) ≤ 0 := by
  have h := primitiveNormalizer_padicVal_le (windowDeterminant n)
    (windowDeterminant_ne_zero n) p 0 (windowDeterminant_integral_above_window (p := p) n hn hp)
  simpa only [windowNormalizer, neg_zero] using h

def smallPrimeEntryCost (n p : ℕ) : ℕ :=
  (51 * n) * (9 * Nat.log p (268 * n + 4) + padicValNat p 96)

theorem windowNormalizer_smallPrime_bound (n : ℕ) :
    padicValRat p (windowNormalizer n) ≤ (smallPrimeEntryCost n p : ℤ) := by
  have h := primitiveNormalizer_padicVal_le (windowDeterminant n)
    (windowDeterminant_ne_zero n) p _ (windowDeterminant_smallPrime_padicLower (p := p) n)
  change padicValRat p (primitiveNormalizer (windowDeterminant n)) ≤ _
  convert h using 1
  simp only [smallPrimeEntryCost, Nat.cast_mul, Nat.cast_add, Nat.cast_ofNat]
  ring

def upperCharge (n p : ℕ) : ℤ :=
  factorialCharge (50 * n) (4 * n) (16 * n) (51 * n) p +
    5 * (upperHighCount (50 * n) p : ℤ) - upperWindowSaving (50 * n) (4 * n) p -
      upperWindowSaving (50 * n) (16 * n) p +
    (min (mixedTerminalSize (50 * n) (4 * n) (16 * n) (51 * n) p)
      (51 * n - upperHighCount (50 * n) p) : ℕ)

theorem windowNormalizer_upperCharge_bound (n : ℕ) (hn : 0 < n) (hp : 2 < p)
    (hmp : 32 * n < p) (hpN : p ≤ 50 * n) (hN : 50 * n < 3 * p)
    (hlarge : 134 * n < p ^ 2) :
    padicValRat p (windowNormalizer n) ≤ upperCharge n p := by
  have hF : PolynomialPadicLower p (-upperCharge n p) (windowDeterminant n) := by
    have h := windowDeterminant_upperBand_bound (p := p) n hn hp hmp hpN hN hlarge
    convert h using 1
    unfold upperCharge
    ring
  have h := primitiveNormalizer_padicVal_le (windowDeterminant n)
    (windowDeterminant_ne_zero n) p _ hF
  simpa only [windowNormalizer, neg_neg] using h

def largeCharge (n p : ℕ) : ℤ :=
  factorialCharge (50 * n) (4 * n) (16 * n) (51 * n) p +
    mixedTerminalSize (50 * n) (4 * n) (16 * n) (51 * n) p

theorem windowNormalizer_largeCharge_bound (n : ℕ) (hn : 0 < n) (hNp : 50 * n < p) :
    padicValRat p (windowNormalizer n) ≤ largeCharge n p := by
  have h := primitiveNormalizer_padicVal_le (windowDeterminant n)
    (windowDeterminant_ne_zero n) p _ (windowDeterminant_largePrime_bound (p := p) n hn hNp)
  change padicValRat p (primitiveNormalizer (windowDeterminant n)) ≤ _
  unfold largeCharge
  linarith

end Zeta3.Arithmetic

import Zeta3.Arithmetic.SmallPrimeSum
import Zeta5.Reuse.PrimeIntervals

/-! The actual cubic normalizer's signed rational product formula is
split into the negligible small-prime prefix, the 4r tail, and the finite
prime profile interval [N/500, 134n]. -/
noncomputable section
namespace Zeta3.Arithmetic
open Polynomial Finset OddZeta.FourValue Zeta3.Construction Zeta5.Endpoint
open Zeta5.Arithmetic Zeta5.Reuse.PrimePiecewise Filter
open scoped Topology Chebyshev

theorem smallPrimeSet_eq_primeIoc (Y : ℕ) :
    smallPrimeSet Y = (Ioc 0 Y).filter Nat.Prime := by
  ext p
  simp only [smallPrimeSet, mem_filter, mem_Icc, mem_Ioc]
  constructor <;> rintro ⟨⟨h1, h2⟩, hp⟩ <;> exact ⟨⟨by omega, h2⟩, hp⟩

theorem windowNormalizer_log_le_primeWeightedSum (n : ℕ) (hn : 0 < n) :
    Real.log (windowNormalizer n : ℝ) ≤
      primeWeightedSum (fun p => (padicValRat p (windowNormalizer n) : ℝ)) 0 (134 * n) := by
  have hq := (windowNormalizer_pos n).ne'
  have h := finite_prime_upper (windowNormalizer n) hq (smallPrimeSet (134 * n))
    (fun p => (padicValRat p (windowNormalizer n) : ℝ))
    (fun p hp => (mem_smallPrimeSet.mp hp).1) (fun _ _ => le_rfl) (by
      intro p hp hpS
      letI : Fact p.Prime := ⟨hp⟩
      have hlarge : 134 * n < p := by
        by_contra hle
        exact hpS (mem_smallPrimeSet.mpr ⟨hp, by omega⟩)
      exact windowNormalizer_nonpos_above_window n hn hlarge)
  have hpos : (0 : ℝ) < (windowNormalizer n : ℝ) := by exact_mod_cast windowNormalizer_pos n
  simpa only [abs_of_pos hpos, smallPrimeSet_eq_primeIoc, primeWeightedSum] using h

theorem windowNormalizer_smallPrimeWeightedSum_le (n : ℕ) :
    primeWeightedSum (fun p => (padicValRat p (windowNormalizer n) : ℝ)) 0 (smallPrimeCutoff n) ≤
      smallPrimeError n := by
  simpa only [primeWeightedSum, ← smallPrimeSet_eq_primeIoc] using smallPrime_normalizer_sum_le n

theorem primeLog_Ioc_le_theta (a b : ℕ) :
    (∑ p ∈ (Ioc a b).filter Nat.Prime, Real.log (p : ℝ)) ≤ θ (b : ℝ) := by
  rw [Chebyshev.theta, Nat.floor_natCast]
  apply sum_le_sum_of_subset_of_nonneg
  · intro p hp
    obtain ⟨hpI, hpprime⟩ := mem_filter.mp hp
    obtain ⟨hpa, hpb⟩ := mem_Ioc.mp hpI
    exact mem_filter.mpr ⟨mem_Ioc.mpr ⟨by omega, hpb⟩, hpprime⟩
  · intro p hp hnot
    exact Real.log_natCast_nonneg p

theorem windowNormalizer_goodPrefix_le (n b : ℕ) :
    primeWeightedSum (fun p => (padicValRat p (windowNormalizer n) : ℝ)) (smallPrimeCutoff n) b ≤
      (204 * n : ℕ) * θ (b : ℝ) := by
  unfold primeWeightedSum
  calc
    _ ≤ ∑ p ∈ (Ioc (smallPrimeCutoff n) b).filter Nat.Prime,
        ((204 * n : ℕ) : ℝ) * Real.log p := by
      apply sum_le_sum
      intro p hp
      obtain ⟨hpI, hpprime⟩ := mem_filter.mp hp
      letI : Fact p.Prime := ⟨hpprime⟩
      obtain ⟨hp5, hpsq⟩ := prime_above_smallPrimeCutoff_good (mem_Ioc.mp hpI).1
      have hval : (padicValRat p (windowNormalizer n) : ℝ) ≤ ((204 * n : ℕ) : ℝ) := by
        exact_mod_cast windowNormalizer_goodPrime_bound (p := p) n (by omega) hpsq
      exact mul_le_mul_of_nonneg_right
        hval (Real.log_natCast_nonneg p)
    _ = ((204 * n : ℕ) : ℝ) * ∑ p ∈ (Ioc (smallPrimeCutoff n) b).filter Nat.Prime, Real.log p := by
      rw [mul_sum]
    _ ≤ ((204 * n : ℕ) : ℝ) * θ (b : ℝ) :=
      mul_le_mul_of_nonneg_left (primeLog_Ioc_le_theta _ _) (Nat.cast_nonneg _)

theorem theta_nat_div_eq (N d : ℕ) :
    θ (((N / d : ℕ) : ℝ)) = θ ((N : ℝ) / d) := by
  unfold Chebyshev.theta
  rw [Nat.floor_natCast, Nat.floor_div_natCast, Nat.floor_natCast]

theorem windowNormalizer_prefix_le (n : ℕ)
    (hcut : smallPrimeCutoff n ≤ (50 * n) / 500) :
    primeWeightedSum (fun p => (padicValRat p (windowNormalizer n) : ℝ)) 0 ((50 * n) / 500) ≤
      smallPrimeError n + ((204 * n : ℕ) : ℝ) * θ (((50 * n : ℕ) : ℝ) / 500) := by
  rw [← primeWeightedSum_add _ (Nat.zero_le (smallPrimeCutoff n)) hcut]
  have h := add_le_add (windowNormalizer_smallPrimeWeightedSum_le n)
    (windowNormalizer_goodPrefix_le n ((50 * n) / 500))
  simpa only [theta_nat_div_eq, Nat.cast_ofNat] using h

theorem windowNormalizer_log_le_tail_and_primeSum (n : ℕ) (hn : 0 < n)
    (hcut : smallPrimeCutoff n ≤ (50 * n) / 500) :
    Real.log (windowNormalizer n : ℝ) ≤
      smallPrimeError n + ((204 * n : ℕ) : ℝ) * θ (((50 * n : ℕ) : ℝ) / 500) +
        primeWeightedSum (fun p => (padicValRat p (windowNormalizer n) : ℝ)) ((50 * n) / 500) (134 * n) := by
  have h := windowNormalizer_log_le_primeWeightedSum n hn
  have hcutN : (50 * n) / 500 ≤ 134 * n := (Nat.div_le_self _ _).trans (by omega)
  rw [← primeWeightedSum_add _ (Nat.zero_le ((50 * n) / 500)) hcutN] at h
  exact h.trans (add_le_add (windowNormalizer_prefix_le n hcut) le_rfl)

theorem windowNormalizer_log_le_tail_and_primeSum_eventually :
    ∀ᶠ n : ℕ in atTop, Real.log (windowNormalizer n : ℝ) ≤
      smallPrimeError n + ((204 * n : ℕ) : ℝ) * θ (((50 * n : ℕ) : ℝ) / 500) +
        primeWeightedSum (fun p => (padicValRat p (windowNormalizer n) : ℝ)) ((50 * n) / 500) (134 * n) := by
  filter_upwards [eventually_ge_atTop 100000000] with n hn
  exact windowNormalizer_log_le_tail_and_primeSum n (by omega) (smallPrimeCutoff_lt_middle_of_large hn).le

end Zeta3.Arithmetic

import Zeta3.Arithmetic.StieltjesReflection
import Zeta5.Arithmetic.LocalFunctional

/-! Exact extraction of the multiples of p from cubic harmonic sums.
The error is divisible by p^3, with no degree or size hypothesis. -/
noncomputable section
namespace Zeta3.Arithmetic
open Polynomial Finset OddZeta.FourValue Zeta5.Arithmetic Zeta3.Construction
variable {p : ℕ} [Fact p.Prime]

theorem harmonicThree_prime_reduction (n : ℕ) :
    PadicLower p 3 ((p : ℚ) ^ 3 * harmonicThree n - harmonicThree (n / p)) := by
  have hp : 0 < p := (Fact.out : p.Prime).pos
  have hp0 : (p : ℚ) ≠ 0 := by exact_mod_cast hp.ne'
  induction n with
  | zero => simpa [harmonicThree] using (PadicLower.zero (p := p) 3)
  | succ n ih =>
    rw [harmonicThree_succ]
    by_cases hd : p ∣ n + 1
    · rw [Nat.succ_div_of_dvd hd, harmonicThree_succ]
      have hmul : p * (n / p + 1) = n + 1 := by
        rw [← Nat.succ_div_of_dvd hd]
        exact Nat.mul_div_cancel' hd
      have hmulQ : (p : ℚ) * ((n / p + 1 : ℕ) : ℚ) = ((n + 1 : ℕ) : ℚ) := by exact_mod_cast hmul
      have he : (p : ℚ) ^ 3 * (harmonicThree n + 1 / ((n + 1 : ℕ) : ℚ) ^ 3) -
          (harmonicThree (n / p) + 1 / ((n / p + 1 : ℕ) : ℚ) ^ 3) =
          (p : ℚ) ^ 3 * harmonicThree n - harmonicThree (n / p) := by
        rw [← hmulQ, mul_pow]
        field_simp
        <;> ring
      rw [he]
      exact ih
    · rw [Nat.succ_div_of_not_dvd hd]
      have hu : PadicLower p 0 (1 / ((n + 1 : ℕ) : ℚ) ^ 3) := by
        have hz : ¬(p : ℤ) ∣ ((n + 1 : ℕ) : ℤ) := by exact_mod_cast hd
        simpa only [Int.cast_natCast, inv_pow, one_div] using
          padicIntegral_pow (inverse_int_integral_of_not_dvd _ hz) 3
      have ht := (prime_power_padicLower (p := p) 3).mul hu
      have h := ih.add (by simpa using ht)
      convert h using 1
      push_cast
      field_simp
      <;> ring

theorem stieltjesConstant_prime_reduction {i : ℕ} (hp : 2 < p) (hpi : ¬p ∣ i) :
    PadicLower p 3 ((p : ℚ) ^ 3 * stieltjesConstant i +
      (i : ℚ) ^ 2 * harmonicThree ((i - 1) / p)) := by
  have hiint : PadicLower p 0 ((i : ℚ) ^ 2) := padicIntegral_pow (padicLower_nat i) 2
  have hH := hiint.mul (harmonicThree_prime_reduction (p := p) (i - 1))
  have hiinv : PadicLower p 0 ((i : ℚ)⁻¹) := by
    have hz : ¬(p : ℤ) ∣ (i : ℤ) := by exact_mod_cast hpi
    simpa only [Int.cast_natCast] using inverse_int_integral_of_not_dvd (p := p) _ hz
  have hhalf := half_integral (p := p) hp
  have hrec : PadicLower p 0 (1 / (2 * (i : ℚ))) := by
    simpa only [one_div, mul_inv_rev, zero_add] using hiinv.mul hhalf
  have htail : PadicLower p 3 ((p : ℚ) ^ 3 * (1 / (2 * (i : ℚ)) + 1 / 2)) := by
    simpa only [Nat.cast_ofNat, add_zero] using
      (prime_power_padicLower (p := p) 3).mul (hrec.add hhalf)
  have h := hH.neg.add htail.neg
  convert h using 1
  · norm_num
  · unfold stieltjesConstant
    ring

end Zeta3.Arithmetic

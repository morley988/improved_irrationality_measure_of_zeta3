import Zeta3.Arithmetic.NormalizerPrimeTail
import Zeta3.Arithmetic.SmallPrimeError
import Zeta3.Analysis.AnalyticError
import Zeta5.Reuse.PrimePiecewise

/-!
# The cubic arithmetic majorant and its proved quadratic rate

This module proves the prime-number-theorem and small-prime assembly for the
actual normalizer.  The only remaining input is the pointwise arithmetic
work's summed majorization by the actual finite affine profile, with its
finite area bound.  No asymptotic assertion is entrusted to a certificate.
-/

noncomputable section
namespace Zeta3.Analysis
open Filter Zeta3.Construction Zeta5.Reuse Zeta5.Reuse.PrimePiecewise
open scoped Topology Chebyshev

def arithmeticTailMajorant (n : ℕ) : ℝ := (204*(n:ℝ))*θ ((50*(n:ℝ))/500)

def arithmeticMajorant (cells : List AffinePiece) (K L : ℝ) (n : ℕ) : ℝ :=
  Zeta3.Arithmetic.smallPrimeError n+arithmeticTailMajorant n+
    primeProfileMajorant cells K L (67/25) (50*n)

theorem windowIndex_tendsto : Tendsto (fun n : ℕ => 50*n) atTop atTop := by
  apply tendsto_atTop.2
  intro b
  exact (eventually_ge_atTop b).mono (fun n hn => by omega)

theorem arithmeticTailMajorant_limit :
    Tendsto (fun n : ℕ => arithmeticTailMajorant n/windowScale n)
      atTop (𝓝 (51/6250:ℝ)) := by
  have h := (ThetaAsymptotic.scaled_limit θ PrimeNumberTheorem.theta_ratio_limit
    (50/500) (by norm_num)).comp
      (tendsto_natCast_atTop_atTop : Tendsto (fun n : ℕ => (n:ℝ)) atTop atTop)
  have hm := h.const_mul (204/2500:ℝ)
  have hv : (204/2500:ℝ)*(50/500)=51/6250 := by norm_num
  rw [hv] at hm
  apply hm.congr'
  filter_upwards [eventually_gt_atTop (0:ℕ)] with n hn
  have hn0 : (n:ℝ)≠0 := by exact_mod_cast hn.ne'
  unfold arithmeticTailMajorant windowScale
  dsimp only [Function.comp_apply]
  rw [show (50/500:ℝ)*(n:ℝ)=50*(n:ℝ)/500 by ring]
  field_simp <;> ring

theorem windowPrimeProfileMajorant_limit (cells : List AffinePiece)
    (hcells : ∀ c∈cells,c.Valid) (K L : ℝ) :
    Tendsto (fun n : ℕ => primeProfileMajorant cells K L (67/25) (50*n)/windowScale n)
      atTop (𝓝 (finiteArea cells)) := by
  have h := (primeProfileMajorant_limit cells hcells K L (67/25) (by norm_num)).comp windowIndex_tendsto
  convert h using 1
  ext n
  simp only [Function.comp_apply,Nat.cast_mul,Nat.cast_ofNat,windowScale]

theorem arithmeticMajorant_limit (cells : List AffinePiece)
    (hcells : ∀ c∈cells,c.Valid) (K L : ℝ) :
    Tendsto (fun n : ℕ => arithmeticMajorant cells K L n/windowScale n)
      atTop (𝓝 ((51/6250:ℝ)+finiteArea cells)) := by
  have hs : Tendsto (fun n => Zeta3.Arithmetic.smallPrimeError n/windowScale n) atTop (𝓝 0) :=
    Zeta3.Arithmetic.smallPrimeError_over_windowScale_limit
  have h := (hs.add arithmeticTailMajorant_limit).add (windowPrimeProfileMajorant_limit cells hcells K L)
  simpa only [arithmeticMajorant,add_div,zero_add] using h

theorem windowNormalizer_le_arithmeticMajorant (cells : List AffinePiece) (K L : ℝ)
    (hprime : ∀ᶠ n : ℕ in atTop,
      primeWeightedSum (fun p => (padicValRat p (windowNormalizer n):ℝ))
        ((50*n)/500) (134*n)≤primeProfileMajorant cells K L (67/25) (50*n)) :
    ∀ᶠ n : ℕ in atTop, Real.log (windowNormalizer n:ℝ)≤arithmeticMajorant cells K L n := by
  filter_upwards [Zeta3.Arithmetic.windowNormalizer_log_le_tail_and_primeSum_eventually,hprime] with n hn hp
  apply hn.trans
  unfold arithmeticMajorant arithmeticTailMajorant
  push_cast
  linarith

theorem exists_arithmetic_rate_error_of_prime_profile (cells : List AffinePiece)
    (hcells : ∀ c∈cells,c.Valid) (K L C_ar : ℝ)
    (harea : (51/6250:ℝ)+finiteArea cells≤C_ar)
    (hprime : ∀ᶠ n : ℕ in atTop,
      primeWeightedSum (fun p => (padicValRat p (windowNormalizer n):ℝ))
        ((50*n)/500) (134*n)≤primeProfileMajorant cells K L (67/25) (50*n)) :
    ∃ E : ℕ→ℝ, Tendsto (fun n => E n/windowScale n) atTop (𝓝 0) ∧
      (∀ᶠ n in atTop, Real.log (windowNormalizer n:ℝ)≤C_ar*windowScale n+E n) := by
  let c := (51/6250:ℝ)+finiteArea cells
  refine ⟨fun n => arithmeticMajorant cells K L n-c*windowScale n,?_,?_⟩
  · have h := (arithmeticMajorant_limit cells hcells K L).sub_const c
    simp only [c,sub_self] at h
    apply h.congr'
    filter_upwards [eventually_gt_atTop (0:ℕ)] with n hn
    have hn0 : (n:ℝ)≠0 := by exact_mod_cast hn.ne'
    unfold windowScale
    field_simp <;> ring
  · filter_upwards [windowNormalizer_le_arithmeticMajorant cells K L hprime] with n hn
    have hh := mul_le_mul_of_nonneg_right harea (show 0≤windowScale n by exact sq_nonneg _)
    dsimp only [c]
    linarith

end Zeta3.Analysis

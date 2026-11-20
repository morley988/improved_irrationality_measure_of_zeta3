import Zeta3.Arithmetic.PrimeStripAssembly
import Zeta3.Arithmetic.FeatureRankEnvelope

/-! Exact floor stability away from the right end of a finite prime cell. -/

noncomputable section
namespace Zeta3.Arithmetic
open Zeta3.Construction.Features Zeta5.Arithmetic

theorem prime_above_smallPrimeCutoff_strong {n p : ℕ} (hp : smallPrimeCutoff n<p) :
    5<p ∧ 536*n+100<p^2 := by
  have h₁ := Nat.lt_succ_sqrt' n
  have h₂ := smallPrimeCutoff_ge n
  constructor
  · omega
  · unfold smallPrimeCutoff at hp
    have hk : 0≤Nat.sqrt n := Nat.zero_le _
    nlinarith

theorem prime_strong_of_fixed_cutoff {n p : ℕ} (hn : 0<n)
    (hcut : smallPrimeCutoff n≤(50*n)/500)
    (hβ : (1/500:ℝ)<(p:ℝ)/(50*n)) : 5<p ∧ 536*n+100<p^2 := by
  have hN : (0:ℝ)<50*n := by positivity
  have hi := (lt_div_iff₀ hN).mp hβ
  have hNat : 50*n<500*p := by
    exact_mod_cast (show 50*(n:ℝ)<500*p by nlinarith)
  have hp : (50*n)/500<p :=
    (Nat.div_lt_iff_lt_mul (by norm_num : 0<500)).mpr (by omega)
  exact prime_above_smallPrimeCutoff_strong (hcut.trans_lt hp)

theorem restrictionDepth_eq_full_of_right_strip {m r p d N : ℕ} (hp : 0<p)
    (hi : ℝ) (hfull : 2*(m+r)/p=d)
    (hband : (d:ℝ)*hi*(N:ℝ)≤((2*(m+r):ℕ):ℝ))
    (hstrip : (p:ℝ)+2<hi*(N:ℝ)) :
    restrictionDepth m r p=d := by
  have hu : restrictionDepth m r p≤d := by
    rw [←hfull]
    exact restrictionDepth_le_full m r p
  by_cases hd : d=0
  · omega
  · have hdR : (1:ℝ)≤d := by exact_mod_cast (show 1≤d by omega)
    have hm := mul_lt_mul_of_pos_left hstrip (show (0:ℝ)<d by positivity)
    have hdp : d*p+2≤2*(m+r) := by
      exact_mod_cast (show (d:ℝ)*p+2≤((2*(m+r):ℕ):ℝ) by nlinarith)
    have hl : d≤(2*(m+r)-2)/p :=
      (Nat.le_div_iff_mul_le hp).mpr (by omega)
    change (2*(m+r)-2)/p=d
    change (2*(m+r)-2)/p≤d at hu
    omega

end Zeta3.Arithmetic

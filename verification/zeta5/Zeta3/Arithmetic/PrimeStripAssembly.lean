import Zeta3.Arithmetic.PrimeAssembly
import Zeta3.Arithmetic.PrimeRowStrip

/-! # Actual cubic prime-profile assembly allowing fixed-width floor boundaries -/

noncomputable section
namespace Zeta3.Arithmetic
open Zeta3.Construction Zeta5.Reuse.PrimePiecewise Filter
open scoped Topology

def stripEndpointErrorCoefficient (cells : List AffinePiece) (width : ℕ) : ℝ :=
  (cells.map (fun c => rightStripPenalty c (102/25) width)).sum

theorem CellsFit.cubicPrimeWeightedSum {cells : List AffinePiece}
    (hfit : CellsFit (1/500) cells (67/25)) (f : ℕ→ℝ) (n : ℕ) :
    (cells.map (fun c : AffinePiece =>
      Zeta5.Reuse.PrimePiecewise.primeWeightedSum f ⌊c.lo*((50*n:ℕ):ℝ)⌋₊ ⌊c.hi*((50*n:ℕ):ℝ)⌋₊)).sum=
      Zeta5.Reuse.PrimePiecewise.primeWeightedSum f ((50*n)/500) (134*n) := by
  rw [hfit.primeWeightedSum]
  have hlo : ⌊(1/500:ℝ)*((50*n:ℕ):ℝ)⌋₊=(50*n)/500 := by
    rw [show (1/500:ℝ)*((50*n:ℕ):ℝ)=((50*n:ℕ):ℝ)/500 by ring]
    simpa only [Nat.cast_ofNat] using
      (show ⌊((50*n:ℕ):ℝ)/(500:ℕ)⌋₊=(50*n)/500 by rw [Nat.floor_div_natCast,Nat.floor_natCast])
  have hhi : ⌊(67/25:ℝ)*((50*n:ℕ):ℝ)⌋₊=134*n := by
    rw [show (67/25:ℝ)*((50*n:ℕ):ℝ)=((134*n:ℕ):ℝ) by push_cast;ring,Nat.floor_natCast]
  rw [hlo,hhi]

theorem windowNormalizer_finiteStripProfile_bound (cells : List AffinePiece)
    (hfit : CellsFit (1/500) cells (67/25)) (K : ℝ) (hK : 0≤K) (width : ℕ)
    (n : ℕ) (hn : 0<n) (hcut : smallPrimeCutoff n≤(50*n)/500)
    (hregular : ∀ c∈cells,∀ p : ℕ,p.Prime → c.lo<(p:ℝ)/((50*n:ℕ):ℝ) →
      (p:ℝ)/((50*n:ℕ):ℝ)<c.hi → (p:ℝ)+width<c.hi*((50*n:ℕ):ℝ) →
      (padicValRat p (windowNormalizer n):ℝ)≤((50*n:ℕ):ℝ)*
        (c.intercept+c.slope*((p:ℝ)/((50*n:ℕ):ℝ)))+K) :
    primeWeightedSum (fun p => (padicValRat p (windowNormalizer n):ℝ)) ((50*n)/500) (134*n)≤
      primeProfileMajorant cells (primeErrorCoefficient cells K) (stripEndpointErrorCoefficient cells width)
        (67/25) (50*n) := by
  have h : (cells.map (fun c : AffinePiece =>
      primeWeightedSum (fun p => (padicValRat p (windowNormalizer n):ℝ))
        ⌊c.lo*((50*n:ℕ):ℝ)⌋₊ ⌊c.hi*((50*n:ℕ):ℝ)⌋₊)).sum≤
      primeProfileMajorant cells (primeErrorCoefficient cells K) (stripEndpointErrorCoefficient cells width)
        (67/25) (50*n) := by
    apply sum_prime_row_strip_bounds cells (50*n) (67/25) (102/25) K width
    intro c hc
    apply prime_row_strip_charge_le c (hfit.valid (by norm_num) c hc)
      (50*n) (by omega) (67/25) (102/25) K width (hfit.bounds c hc).2.2
      (by have hnR : (1:ℝ)≤n := by exact_mod_cast hn
          push_cast;nlinarith) (by norm_num) hK
    · exact hregular c hc
    · intro p hp hl _
      exact cells_uniform_bound cells hfit c hc hn hcut hp hl
  rwa [hfit.cubicPrimeWeightedSum] at h

theorem windowNormalizer_finiteStripProfile_bound_eventually (cells : List AffinePiece)
    (hfit : CellsFit (1/500) cells (67/25)) (K : ℝ) (hK : 0≤K) (width : ℕ)
    (hregular : ∀ᶠ n : ℕ in atTop,∀ c∈cells,∀ p : ℕ,p.Prime →
      c.lo<(p:ℝ)/((50*n:ℕ):ℝ) → (p:ℝ)/((50*n:ℕ):ℝ)<c.hi →
      (p:ℝ)+width<c.hi*((50*n:ℕ):ℝ) →
      (padicValRat p (windowNormalizer n):ℝ)≤((50*n:ℕ):ℝ)*
        (c.intercept+c.slope*((p:ℝ)/((50*n:ℕ):ℝ)))+K) :
    ∀ᶠ n : ℕ in atTop,
      primeWeightedSum (fun p => (padicValRat p (windowNormalizer n):ℝ)) ((50*n)/500) (134*n)≤
        primeProfileMajorant cells (primeErrorCoefficient cells K) (stripEndpointErrorCoefficient cells width)
          (67/25) (50*n) := by
  filter_upwards [hregular,smallPrimeCutoff_eventually_lt_middle,eventually_gt_atTop (0:ℕ)] with n hn hc hn0
  exact windowNormalizer_finiteStripProfile_bound cells hfit K hK width n hn0 hc.le hn

end Zeta3.Arithmetic

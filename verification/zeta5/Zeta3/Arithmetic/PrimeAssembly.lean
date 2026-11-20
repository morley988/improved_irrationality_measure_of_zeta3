import Zeta3.Arithmetic.NormalizerPrimeTail
import Zeta5.Arithmetic.PrimeRowBound

/-!
# Exact finite-cell assembly of the actual cubic prime charge

Finite adjacent cells telescope exactly, including their right endpoints.
The open-cell arithmetic bounds carry a uniform O(1) error. At each right
endpoint the proved actual good-prime bound supplies an O(N log N) charge.
-/

noncomputable section
namespace Zeta3.Arithmetic
open Zeta3.Construction Zeta5.Reuse.PrimePiecewise Filter
open scoped Topology Chebyshev

def CellsFit (start : ℝ) : List AffinePiece → ℝ → Prop
  | [], finish => start=finish
  | c::cs, finish => c.lo=start ∧ c.lo≤c.hi ∧ CellsFit c.hi cs finish

theorem CellsFit.start_le_finish {cells : List AffinePiece} {start finish : ℝ}
    (h : CellsFit start cells finish) : start≤finish := by
  induction cells generalizing start with
  | nil => exact le_of_eq h
  | cons c cs ih =>
    rcases h with ⟨hc,hch,hrest⟩
    exact hc ▸ (hch.trans (ih hrest))

theorem CellsFit.bounds {cells : List AffinePiece} {start finish : ℝ}
    (h : CellsFit start cells finish) :
    ∀ c∈cells,start≤c.lo ∧ c.lo≤c.hi ∧ c.hi≤finish := by
  induction cells generalizing start with
  | nil => simp
  | cons c cs ih =>
    rcases h with ⟨hc,hch,hrest⟩
    intro d hd
    rcases List.mem_cons.mp hd with rfl|hd
    · exact ⟨le_of_eq hc.symm,hch,hrest.start_le_finish⟩
    · have ht := ih hrest d hd
      exact ⟨(show start≤c.hi by rw [←hc];exact hch).trans ht.1,ht.2⟩

theorem CellsFit.valid {cells : List AffinePiece} {start finish : ℝ}
    (h : CellsFit start cells finish) (hstart : 0<start) : ∀ c∈cells,c.Valid := by
  intro c hc
  have hb := h.bounds c hc
  exact ⟨hstart.trans_le hb.1,hb.2.1⟩

theorem CellsFit.primeWeightedSum {cells : List AffinePiece} {start finish : ℝ}
    (h : CellsFit start cells finish) (f : ℕ→ℝ) (N : ℕ) :
    (cells.map (fun c : AffinePiece =>
      primeWeightedSum f ⌊c.lo*(N:ℝ)⌋₊ ⌊c.hi*(N:ℝ)⌋₊)).sum=
        primeWeightedSum f ⌊start*(N:ℝ)⌋₊ ⌊finish*(N:ℝ)⌋₊ := by
  induction cells generalizing start with
  | nil =>
    change start=finish at h
    simp only [List.map_nil,List.sum_nil,h,primeWeightedSum_self]
  | cons c cs ih =>
    rcases h with ⟨hc,hch,hrest⟩
    rw [List.map_cons,List.sum_cons,ih hrest]
    rw [primeWeightedSum_floor_add f hch hrest.start_le_finish N,hc]

theorem prime_good_of_fixed_cutoff {n p : ℕ} (hn : 0<n)
    (hcut : smallPrimeCutoff n≤(50*n)/500)
    (hβ : (1/500:ℝ)<(p:ℝ)/(50*n)) : 5<p ∧ 268*n+4<p^2 := by
  have hN : (0:ℝ)<50*n := by positivity
  have hi := (lt_div_iff₀ hN).mp hβ
  have hNat : 50*n<500*p := by
    exact_mod_cast (show 50*(n:ℝ)<500*p by nlinarith)
  have hp : (50*n)/500<p :=
    (Nat.div_lt_iff_lt_mul (by norm_num : 0<500)).mpr (by omega)
  exact prime_above_smallPrimeCutoff_good (hcut.trans_lt hp)

def primeErrorCoefficient (cells : List AffinePiece) (K : ℝ) : ℝ := K*cells.length
def endpointErrorCoefficient (cells : List AffinePiece) : ℝ :=
  (cells.map (fun c => Zeta5.Arithmetic.rightEndpointPenalty c (102/25))).sum

theorem cells_uniform_bound {n p : ℕ} (cells : List AffinePiece)
    (hfit : CellsFit (1/500) cells (67/25)) (c : AffinePiece) (hc : c∈cells)
    (hn : 0<n) (hcut : smallPrimeCutoff n≤(50*n)/500)
    (hp : p.Prime) (hl : c.lo<(p:ℝ)/((50*n:ℕ):ℝ)) :
    (padicValRat p (windowNormalizer n):ℝ)≤(102/25:ℝ)*((50*n:ℕ):ℝ) := by
  letI : Fact p.Prime := ⟨hp⟩
  have hβ : (1/500:ℝ)<(p:ℝ)/(50*n) := by
    simpa only [Nat.cast_mul,Nat.cast_ofNat] using (hfit.bounds c hc).1.trans_lt hl
  obtain ⟨hp5,hpsq⟩ := prime_good_of_fixed_cutoff hn hcut hβ
  have hv : (padicValRat p (windowNormalizer n):ℝ)≤((204*n:ℕ):ℝ) := by
    exact_mod_cast windowNormalizer_goodPrime_bound (p:=p) n (by omega) hpsq
  convert hv using 1 <;> push_cast <;> ring

theorem cells_charge_bound (cells : List AffinePiece)
    (hfit : CellsFit (1/500) cells (67/25)) (K : ℝ) (hK : 0≤K)
    (n : ℕ) (hn : 0<n) (hcut : smallPrimeCutoff n≤(50*n)/500)
    (hregular : ∀ c∈cells,∀ p : ℕ,p.Prime → c.lo<(p:ℝ)/((50*n:ℕ):ℝ) →
      (p:ℝ)/((50*n:ℕ):ℝ)<c.hi →
      (padicValRat p (windowNormalizer n):ℝ)≤((50*n:ℕ):ℝ)*
        (c.intercept+c.slope*((p:ℝ)/((50*n:ℕ):ℝ)))+K) :
    (cells.map (fun c : AffinePiece =>
      primeWeightedSum (fun p => (padicValRat p (windowNormalizer n):ℝ))
        ⌊c.lo*((50*n:ℕ):ℝ)⌋₊ ⌊c.hi*((50*n:ℕ):ℝ)⌋₊)).sum≤
      primeProfileMajorant cells (primeErrorCoefficient cells K) (endpointErrorCoefficient cells)
        (67/25) (50*n) := by
  apply Zeta5.Arithmetic.sum_prime_row_bounds cells (50*n) (67/25) (102/25) K
  intro c hc
  apply Zeta5.Arithmetic.prime_row_charge_le c (hfit.valid (by norm_num) c hc)
    (50*n) (by omega) (67/25) (102/25) K (hfit.bounds c hc).2.2
    (by have hnR : (1:ℝ)≤n := by exact_mod_cast hn
        push_cast; nlinarith) (by norm_num) hK
  · exact hregular c hc
  · intro p hp hl _
    exact cells_uniform_bound cells hfit c hc hn hcut hp hl

theorem windowNormalizer_finiteProfile_bound (cells : List AffinePiece)
    (hfit : CellsFit (1/500) cells (67/25)) (K : ℝ) (hK : 0≤K)
    (n : ℕ) (hn : 0<n) (hcut : smallPrimeCutoff n≤(50*n)/500)
    (hregular : ∀ c∈cells,∀ p : ℕ,p.Prime → c.lo<(p:ℝ)/((50*n:ℕ):ℝ) →
      (p:ℝ)/((50*n:ℕ):ℝ)<c.hi →
      (padicValRat p (windowNormalizer n):ℝ)≤((50*n:ℕ):ℝ)*
        (c.intercept+c.slope*((p:ℝ)/((50*n:ℕ):ℝ)))+K) :
    primeWeightedSum (fun p => (padicValRat p (windowNormalizer n):ℝ)) ((50*n)/500) (134*n)≤
      primeProfileMajorant cells (primeErrorCoefficient cells K) (endpointErrorCoefficient cells)
        (67/25) (50*n) := by
  have h := cells_charge_bound cells hfit K hK n hn hcut hregular
  rw [hfit.primeWeightedSum] at h
  have hlo : ⌊(1/500:ℝ)*((50*n:ℕ):ℝ)⌋₊=(50*n)/500 := by
    rw [show (1/500:ℝ)*((50*n:ℕ):ℝ)=((50*n:ℕ):ℝ)/500 by ring]
    simpa only [Nat.cast_ofNat] using
      (show ⌊((50*n:ℕ):ℝ)/(500:ℕ)⌋₊=(50*n)/500 by rw [Nat.floor_div_natCast,Nat.floor_natCast])
  have hhi : ⌊(67/25:ℝ)*((50*n:ℕ):ℝ)⌋₊=134*n := by
    rw [show (67/25:ℝ)*((50*n:ℕ):ℝ)=((134*n:ℕ):ℝ) by push_cast;ring,Nat.floor_natCast]
  simpa only [hlo,hhi] using h

theorem windowNormalizer_finiteProfile_bound_eventually (cells : List AffinePiece)
    (hfit : CellsFit (1/500) cells (67/25)) (K : ℝ) (hK : 0≤K)
    (hregular : ∀ᶠ n : ℕ in atTop,∀ c∈cells,∀ p : ℕ,p.Prime →
      c.lo<(p:ℝ)/((50*n:ℕ):ℝ) → (p:ℝ)/((50*n:ℕ):ℝ)<c.hi →
      (padicValRat p (windowNormalizer n):ℝ)≤((50*n:ℕ):ℝ)*
        (c.intercept+c.slope*((p:ℝ)/((50*n:ℕ):ℝ)))+K) :
    ∀ᶠ n : ℕ in atTop,
      primeWeightedSum (fun p => (padicValRat p (windowNormalizer n):ℝ)) ((50*n)/500) (134*n)≤
        primeProfileMajorant cells (primeErrorCoefficient cells K) (endpointErrorCoefficient cells)
          (67/25) (50*n) := by
  filter_upwards [hregular,smallPrimeCutoff_eventually_lt_middle,eventually_gt_atTop (0:ℕ)] with n hn hc hn0
  exact windowNormalizer_finiteProfile_bound cells hfit K hK n hn0 hc.le hn

end Zeta3.Arithmetic

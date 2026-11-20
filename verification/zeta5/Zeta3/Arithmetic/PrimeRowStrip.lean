import Zeta5.Arithmetic.PrimeRowBound

/-!
# Fixed-width right strips in affine prime cells

The regular arithmetic estimate may exclude a fixed number of integer
positions immediately below a cell's right endpoint.  The actual uniform
prime bound pays for those positions with an explicit O(N log N) term.
-/

noncomputable section
namespace Zeta3.Arithmetic
open Finset Zeta5.Reuse.PrimePiecewise
open scoped Chebyshev

def rightStripPenalty (c : AffinePiece) (U : ℝ) (width : ℕ) : ℝ :=
  ((width:ℝ)+1)*(U+|c.intercept+c.slope*c.hi|+(width:ℝ)*|c.slope|)

theorem prime_row_strip_charge_le (c : AffinePiece) (hc : c.Valid)
    (N : ℕ) (hN : 0<N) (C U K : ℝ) (width : ℕ)
    (hC : c.hi≤C) (hCN : 1≤C*N) (hU : 0≤U) (hK : 0≤K)
    (f : ℕ→ℝ)
    (hregular : ∀ p : ℕ,p.Prime → c.lo<(p:ℝ)/N → (p:ℝ)/N<c.hi →
      (p:ℝ)+width<c.hi*N → f p≤N*(c.intercept+c.slope*((p:ℝ)/N))+K)
    (huniform : ∀ p : ℕ,p.Prime → c.lo<(p:ℝ)/N → (p:ℝ)/N≤c.hi → f p≤U*N) :
    primeWeightedSum f ⌊c.lo*N⌋₊ ⌊c.hi*N⌋₊≤
      c.primeMass N+K*θ (C*N)+rightStripPenalty c U width*N*Real.log (C*N) := by
  let S := (Ioc ⌊c.lo*N⌋₊ ⌊c.hi*N⌋₊).filter Nat.Prime
  let B := S.filter (fun p : ℕ => c.hi*N≤(p:ℝ)+width)
  let L := U+|c.intercept+c.slope*c.hi|+(width:ℝ)*|c.slope|
  have hNR : (0:ℝ)<N := by exact_mod_cast hN
  have hN1 : (1:ℝ)≤N := by exact_mod_cast hN
  have hw : (0:ℝ)≤width := Nat.cast_nonneg _
  have hL : 0≤L := by dsimp [L];positivity
  have hlog : 0≤Real.log (C*N) := Real.log_nonneg hCN
  have hmem (p : ℕ) (hp : p∈S) : p.Prime ∧ c.lo<(p:ℝ)/N ∧ (p:ℝ)/N≤c.hi := by
    obtain ⟨hpr,hl,hr⟩ :=
      (Zeta5.Reuse.PrimeAffine.prime_interval_membership c.lo c.hi hc.1.le hc.2 N p).mp hp
    exact ⟨hpr,(lt_div_iff₀ hNR).mpr hl,(div_le_iff₀ hNR).mpr hr⟩
  have hpCN (p : ℕ) (hp : p∈S) : (p:ℝ)≤C*N :=
    ((div_le_iff₀ hNR).mp (hmem p hp).2.2).trans
      (mul_le_mul_of_nonneg_right hC hNR.le)
  have htheta : (∑ p∈S,Real.log p)≤θ (C*N) := by
    rw [Chebyshev.theta_eq_sum_Icc]
    apply sum_le_sum_of_subset_of_nonneg
    · intro p hp
      exact mem_filter.mpr ⟨mem_Icc.mpr ⟨Nat.zero_le _,
        (Nat.le_floor_iff (by linarith : 0≤C*N)).mpr (hpCN p hp)⟩,(hmem p hp).1⟩
    · intro p _ _
      exact Real.log_natCast_nonneg p
  have hBsub : B⊆Icc (⌊c.hi*N⌋₊-width) ⌊c.hi*N⌋₊ := by
    intro p hp
    obtain ⟨hpS,hnear⟩ := mem_filter.mp hp
    have hup := (mem_Ioc.mp (mem_filter.mp hpS).1).2
    have hfloor := Nat.floor_le (mul_nonneg (hc.1.le.trans hc.2) hNR.le)
    have hlo : ⌊c.hi*N⌋₊≤p+width := by
      exact_mod_cast hfloor.trans hnear
    exact mem_Icc.mpr ⟨by omega,hup⟩
  have hBcard : B.card≤width+1 := by
    apply (card_le_card hBsub).trans
    rw [Nat.card_Icc]
    omega
  have hBsum : (∑ p∈B,Real.log p)≤((width:ℝ)+1)*Real.log (C*N) := by
    calc
      _ ≤ ∑ _p∈B,Real.log (C*N) := by
        apply sum_le_sum
        intro p hp
        have hpS := (mem_filter.mp hp).1
        exact Real.log_le_log (by exact_mod_cast (hmem p hpS).1.pos) (hpCN p hpS)
      _ = (B.card:ℝ)*Real.log (C*N) := by simp
      _ ≤ ((width:ℝ)+1)*Real.log (C*N) :=
        mul_le_mul_of_nonneg_right (by exact_mod_cast hBcard) hlog
  have hpoint (p : ℕ) (hp : p∈S) :
      f p*Real.log p≤(N*(c.intercept+c.slope*((p:ℝ)/N))+K)*Real.log p+
        if c.hi*N≤(p:ℝ)+width then L*N*Real.log p else 0 := by
    obtain ⟨hpr,hl,hr⟩ := hmem p hp
    have hplog := Real.log_natCast_nonneg p
    by_cases hnear : c.hi*N≤(p:ℝ)+width
    · rw [if_pos hnear]
      have hleft : c.hi-width≤(p:ℝ)/N := by
        apply (le_div_iff₀ hNR).mpr
        nlinarith [mul_le_mul_of_nonneg_left hN1 hw]
      have hdist : |(p:ℝ)/N-c.hi|≤width := by
        rw [abs_le]
        constructor <;> linarith
      have habs : |c.intercept+c.slope*((p:ℝ)/N)|≤
          |c.intercept+c.slope*c.hi|+(width:ℝ)*|c.slope| := by
        calc
          _ = |(c.intercept+c.slope*c.hi)+c.slope*((p:ℝ)/N-c.hi)| := by congr 1;ring
          _ ≤ |c.intercept+c.slope*c.hi|+|c.slope*((p:ℝ)/N-c.hi)| := abs_add_le _ _
          _ ≤ |c.intercept+c.slope*c.hi|+(width:ℝ)*|c.slope| := by
            rw [abs_mul]
            have hh := mul_le_mul_of_nonneg_left hdist (abs_nonneg c.slope)
            nlinarith
      have hlow : -(|c.intercept+c.slope*c.hi|+(width:ℝ)*|c.slope|)≤
          c.intercept+c.slope*((p:ℝ)/N) := by
        have hh := neg_abs_le (c.intercept+c.slope*((p:ℝ)/N))
        linarith
      have hscaled := mul_le_mul_of_nonneg_left hlow hNR.le
      have hf := huniform p hpr hl hr
      have hh : f p≤N*(c.intercept+c.slope*((p:ℝ)/N))+K+L*N := by
        dsimp [L]
        nlinarith
      have hm := mul_le_mul_of_nonneg_right hh hplog
      nlinarith
    · rw [if_neg hnear,add_zero]
      have hclear : (p:ℝ)+width<c.hi*N := lt_of_not_ge hnear
      have hlt : (p:ℝ)/N<c.hi := (div_lt_iff₀ hNR).mpr (by linarith)
      exact mul_le_mul_of_nonneg_right (hregular p hpr hl hlt hclear) hplog
  have hsum := sum_le_sum hpoint
  have heq : (∑ p∈S,((N*(c.intercept+c.slope*((p:ℝ)/N))+K)*Real.log p+
      if c.hi*N≤(p:ℝ)+width then L*N*Real.log p else 0))=
      c.primeMass N+K*(∑ p∈S,Real.log p)+L*N*(∑ p∈B,Real.log p) := by
    rw [sum_add_distrib,←sum_filter]
    simp only [AffinePiece.primeMass,add_mul,sum_add_distrib,mul_assoc,←mul_sum]
    rfl
  rw [heq] at hsum
  have hb := hsum.trans (add_le_add
    (add_le_add le_rfl (mul_le_mul_of_nonneg_left htheta hK))
    (mul_le_mul_of_nonneg_left hBsum (mul_nonneg hL hNR.le)))
  convert hb using 1 <;> first | rfl | (dsimp [rightStripPenalty,L];ring)

theorem sum_prime_row_strip_bounds (cells : List AffinePiece) (N : ℕ) (C U K : ℝ)
    (width : ℕ) (f : ℕ→ℝ)
    (hrow : ∀ c∈cells,
      primeWeightedSum f ⌊c.lo*N⌋₊ ⌊c.hi*N⌋₊≤
        c.primeMass N+K*θ (C*N)+rightStripPenalty c U width*N*Real.log (C*N)) :
    (cells.map (fun c : AffinePiece => primeWeightedSum f ⌊c.lo*(N:ℝ)⌋₊ ⌊c.hi*(N:ℝ)⌋₊)).sum≤
      primeProfileMajorant cells (K*cells.length)
        (cells.map (fun c => rightStripPenalty c U width)).sum C N := by
  induction cells with
  | nil => simp [primeProfileMajorant,finitePrimeMass]
  | cons c cs ih =>
    have hh := hrow c (by simp)
    have ht := ih (fun d hd => hrow d (by simp [hd]))
    have h := add_le_add hh ht
    convert h using 1 <;> first | rfl |
      (simp only [List.map_cons,List.sum_cons,primeProfileMajorant,finitePrimeMass,List.length_cons,
        Nat.cast_add,Nat.cast_one];ring)

end Zeta3.Arithmetic

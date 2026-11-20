import Zeta3.Construction.FeatureRank
import Mathlib.Algebra.CharP.Basic

/-! The characteristic and distinct evaluation nodes of the actual local
residue field. No identification of that field with an oracle is used. -/

noncomputable section
namespace Zeta3.Construction.Features
open Polynomial Matrix Zeta5.Arithmetic OddZeta.FourValue
variable {p : ℕ} [Fact p.Prime]

theorem padicLower_nat_one_iff (n : ℕ) :
    PadicLower p 1 (n : ℚ) ↔ p ∣ n := by
  constructor
  · intro h
    by_cases hn : n = 0
    · simp [hn]
    · have hv := h.of_ne_zero (by exact_mod_cast hn : (n : ℚ) ≠ 0)
      rw [padicValRat.of_nat] at hv
      exact dvd_of_one_le_padicValNat (by exact_mod_cast hv)
  · exact padicLower_nat_of_dvd n

/-- A named characteristic theorem, so clients may choose a local instance. -/
theorem residueField_charP : CharP (PadicResidueField p) p := by
  constructor
  intro n
  have he : (n : PadicResidueField p) = padicReduction p (n : padicIntegralSubring p) :=
    (map_natCast (padicReduction p) n).symm
  rw [he, padicReduction_eq_zero]
  exact padicLower_nat_one_iff n

theorem residue_natCast_ne_zero {n : ℕ} (hn : ¬p ∣ n) :
    (n : PadicResidueField p) ≠ 0 := by
  letI := residueField_charP (p := p)
  exact fun h => hn ((CharP.cast_eq_zero_iff (PadicResidueField p) p n).mp h)

theorem residue_natCast_injective_half {c d : ℕ} (hc : 0 < c) (hd : 0 < d)
    (hcp : 2 * c < p) (hdp : 2 * d < p)
    (h : (c : PadicResidueField p)^2 = (d : PadicResidueField p)^2) : c = d := by
  letI := residueField_charP (p := p)
  rcases (sq_eq_sq_iff_eq_or_eq_neg).mp h with h | h
  · exact CharP.natCast_injOn_Iio (PadicResidueField p) p
      (show c < p by omega) (show d < p by omega) h
  · have hz : ((c+d : ℕ) : PadicResidueField p) = 0 := by
      push_cast
      rw [h, neg_add_cancel]
    have hdvd := (CharP.cast_eq_zero_iff (PadicResidueField p) p (c+d)).mp hz
    have hle := Nat.le_of_dvd (by omega : 0 < c+d) hdvd
    omega

theorem residue_square_injective (s : Finset ℕ)
    (hs : ∀ c ∈ s, 0 < c ∧ 2*c < p) :
    Function.Injective (fun c : s => (c.val : PadicResidueField p)^2) := by
  intro c d h
  apply Subtype.ext
  exact residue_natCast_injective_half (hs c c.property).1 (hs d d.property).1
    (hs c c.property).2 (hs d d.property).2 h

end Zeta3.Construction.Features

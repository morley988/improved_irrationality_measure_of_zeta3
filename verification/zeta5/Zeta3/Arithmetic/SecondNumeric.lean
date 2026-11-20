import Zeta3.Arithmetic.ProfileCells

/-! The finite parity-sensitive dimension cap in the second layer. -/
namespace Zeta3.Arithmetic

def numericCap (e D₁ D₂ k₁ k₂ u₁ u₂ : ℕ) : ℕ :=
  let n₁ := D₁+u₁-k₁
  let n₂ := D₂+u₂-k₂
  if e=0 ∧ Even k₁ ∧ Even k₂ then
    min ((n₁+1)/2) (n₂/2)+min (n₁/2) ((n₂+1)/2)
  else min n₁ n₂

theorem numericCap_le_left (e D₁ D₂ k₁ k₂ u₁ u₂ : ℕ) :
    numericCap e D₁ D₂ k₁ k₂ u₁ u₂ ≤ D₁+u₁-k₁ := by
  unfold numericCap
  dsimp only
  split_ifs
  · have h₁ := min_le_left ((D₁+u₁-k₁+1)/2) ((D₂+u₂-k₂)/2)
    have h₂ := min_le_left ((D₁+u₁-k₁)/2) ((D₂+u₂-k₂+1)/2)
    omega
  · exact min_le_left _ _

theorem numericCap_le_right (e D₁ D₂ k₁ k₂ u₁ u₂ : ℕ) :
    numericCap e D₁ D₂ k₁ k₂ u₁ u₂ ≤ D₂+u₂-k₂ := by
  unfold numericCap
  dsimp only
  split_ifs
  · have h₁ := min_le_right ((D₁+u₁-k₁+1)/2) ((D₂+u₂-k₂)/2)
    have h₂ := min_le_right ((D₁+u₁-k₁)/2) ((D₂+u₂-k₂+1)/2)
    omega
  · exact min_le_right _ _

end Zeta3.Arithmetic

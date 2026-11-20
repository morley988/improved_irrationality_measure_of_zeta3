import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Quotient.Basic
import Mathlib.Analysis.InnerProductSpace.Spectrum
import Mathlib.Analysis.Matrix.Spectrum

/-!
# A finite-dimensional minimax estimate from codimension

The elementary dimension argument is proved first in diagonal coordinates.
It requires no optimization theorem: a subspace of codimension at most k
meets the first k+1 coordinate directions in a nonzero vector.
-/

noncomputable section
namespace Zeta3.Analysis
open Module
open scoped BigOperators

def prefixExtend (m r : ℕ) : (Fin m → ℝ) →ₗ[ℝ] (Fin r → ℝ) where
  toFun x i := if h : i.val < m then x ⟨i.val,h⟩ else 0
  map_add' x y := by ext i; by_cases hi : i.val<m <;> simp [hi]
  map_smul' c x := by ext i; by_cases hi : i.val<m <;> simp [hi]

theorem prefixExtend_injective {m r : ℕ} (hmr : m ≤ r) : Function.Injective (prefixExtend m r) := by
  intro x y h
  ext i
  have he := congrFun h (⟨i.val,lt_of_lt_of_le i.isLt hmr⟩ : Fin r)
  simpa only [prefixExtend, LinearMap.coe_mk, AddHom.coe_mk, dif_pos i.isLt] using he

theorem exists_nonzero_supported_prefix {r k : ℕ} (hk : k < r)
    (S : Submodule ℝ (Fin r → ℝ)) (hcodim : finrank ℝ ((Fin r → ℝ) ⧸ S) ≤ k) :
    ∃ x : Fin r → ℝ, x ∈ S ∧ x ≠ 0 ∧ ∀ i : Fin r, k < i.val → x i=0 := by
  let f := S.mkQ.comp (prefixExtend (k+1) r)
  have hdim : finrank ℝ ((Fin r → ℝ) ⧸ S) < finrank ℝ (Fin (k+1) → ℝ) := by
    simpa only [Module.finrank_pi, Module.finrank_self, Fintype.card_fin, mul_one] using
      lt_of_le_of_lt hcodim (Nat.lt_succ_self k)
  obtain ⟨y,hy,hy0⟩ := (LinearMap.ker f).ne_bot_iff.mp (LinearMap.ker_ne_bot_of_finrank_lt hdim)
  refine ⟨prefixExtend (k+1) r y, ?_, ?_, ?_⟩
  · have hh : S.mkQ (prefixExtend (k+1) r y)=0 := hy
    have hm : prefixExtend (k+1) r y ∈ LinearMap.ker S.mkQ := hh
    simpa only [Submodule.ker_mkQ] using hm
  · intro hzero
    apply hy0
    apply prefixExtend_injective (Nat.succ_le_of_lt hk)
    simpa only [map_zero] using hzero
  · intro i hi
    simp only [prefixExtend, LinearMap.coe_mk, AddHom.coe_mk, dif_neg (by omega : ¬i.val<k+1)]

theorem sum_sq_pos_of_ne_zero {r : ℕ} (x : Fin r → ℝ) (hx : x ≠ 0) :
    0 < ∑ i, (x i)^2 := by
  have hex : ∃ i, x i ≠ 0 := by
    by_contra! h
    exact hx (funext h)
  obtain ⟨i,hi⟩ := hex
  exact Finset.sum_pos' (fun j _ => sq_nonneg _) ⟨i,Finset.mem_univ _,sq_pos_of_ne_zero hi⟩

/-- The kth descending diagonal value is bounded by any Rayleigh bound on
a subspace of codimension at most k. -/
theorem diagonal_eigenvalue_le_of_codimension {r : ℕ} (values : Fin r → ℝ)
    (hvalues : Antitone values) (k : Fin r) (S : Submodule ℝ (Fin r → ℝ))
    (hcodim : finrank ℝ ((Fin r → ℝ) ⧸ S) ≤ k.val) (R : ℝ)
    (hRayleigh : ∀ x ∈ S, ∑ i, values i*(x i)^2 ≤ R*∑ i, (x i)^2) :
    values k ≤ R := by
  obtain ⟨x,hxS,hx0,hxsupp⟩ := exists_nonzero_supported_prefix k.isLt S hcodim
  have hnorm := sum_sq_pos_of_ne_zero x hx0
  have hupper := hRayleigh x hxS
  have hlower : values k*(∑ i, (x i)^2) ≤ ∑ i, values i*(x i)^2 := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro i _
    by_cases hik : i.val ≤ k.val
    · exact mul_le_mul_of_nonneg_right (hvalues hik) (sq_nonneg _)
    · rw [hxsupp i (lt_of_not_ge hik)]
      simp
  exact (mul_le_mul_iff_of_pos_right hnorm).mp (hlower.trans hupper)

end Zeta3.Analysis

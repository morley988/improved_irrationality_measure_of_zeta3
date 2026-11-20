import Zeta3.Analysis.WindowGramBound
import Zeta3.Analysis.PhysicalProfileGrid
import Zeta3.Analysis.AnalyticError
import Zeta3.Certificate.Analytic

/-!
# The actual cubic determinant's analytic decay rate

The physical density, Stieltjes identity, positivity, asymmetric basis change,
trial polynomial norms, factorial cancellation, and profile integration are
proved for the concrete determinant. The only external premise in the
certified version is the finite analytic-sum bound from Certificate.Analytic.
-/

noncomputable section
namespace Zeta3.Analysis
open Real Set Filter Polynomial
open scoped Topology BigOperators

def analyticEndpointDrop : ℝ :=
  physicalSaving (2 / 25) (8 / 25) (by norm_num) (by norm_num) (51 / 50) -
    physicalSaving (2 / 25) (8 / 25) (by norm_num) (by norm_num) 0

theorem exists_windowValue_log_bound : ∃ C : ℝ, ∀ n : ℕ, 0 < n →
    Real.log (windowValue n) ≤
      -Zeta3.Certificate.analyticIntegral * windowScale n + analyticError C analyticEndpointDrop n := by
  obtain ⟨K, hK, hnorm⟩ := exists_uniform_windowSquaredNorm_bound
    (2 / 25) (8 / 25) (by norm_num) (by norm_num) (by norm_num) (51 / 50) (by norm_num)
  refine ⟨Real.log K, ?_⟩
  intro n hn
  have hN : 0 < 50 * n := by omega
  have hNr : (0 : ℝ) < (50 * n : ℕ) := by exact_mod_cast hN
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hms₁ : ((4 * n : ℕ) : ℝ) / (50 * n : ℕ) = (2 / 25 : ℝ) := by
    push_cast
    field_simp
    ring
  have hms₂ : ((16 * n : ℕ) : ℝ) / (50 * n : ℕ) = (8 / 25 : ℝ) := by
    push_cast
    field_simp
    ring
  have hrδ : ((51 * n : ℕ) : ℝ) / (50 * n : ℕ) = (51 / 50 : ℝ) := by
    push_cast
    field_simp
  have hkδ (k : Fin (51 * n)) : (k.val : ℝ) / (50 * n : ℕ) ≤ (51 / 50 : ℝ) := by
    rw [← hrδ]
    apply div_le_div_of_nonneg_right _ hNr.le
    exact_mod_cast k.isLt.le
  have hpExists (k : Fin (51 * n)) := hnorm (50 * n) (4 * n) (16 * n) k.val hN hms₁ hms₂ (hkδ k)
  choose p hpm hpd hpbound using hpExists
  have hdet := windowValue_le_trial_norms n p hpm hpd
  have hprod :
      (∏ k : Fin (51 * n), gramNormFactor (50 * n) (4 * n) (16 * n) k.val *
        windowSquaredNorm (50 * n) (4 * n) (16 * n) (p k)) ≤
      ∏ k : Fin (51 * n), rowNormUpper K (2 / 25) (8 / 25) (by norm_num) (by norm_num)
        (50 * n) (4 * n) (16 * n) k.val := by
    apply Finset.prod_le_prod
    · intro k _
      exact mul_nonneg (gramNormFactor_pos _ _ _ _).le
        (windowSquaredNorm_pos_of_monic _ _ _ (hpm k)).le
    · intro k _
      exact mul_le_mul_of_nonneg_left (hpbound k) (gramNormFactor_pos _ _ _ _).le
  have hbound := hdet.trans (mul_le_mul_of_nonneg_left hprod (by positivity))
  have hlog := Real.log_le_log (windowValue_pos n) hbound
  have hrows (k : Fin (51 * n)) := log_rowNormUpper_le_profile hK
    (by norm_num : (0 : ℝ) < 2 / 25) (by norm_num : (0 : ℝ) < 8 / 25) hN hms₁ hms₂ k.val
  have hupperPos (k : Fin (51 * n)) :
      0 < rowNormUpper K (2 / 25) (8 / 25) (by norm_num) (by norm_num)
        (50 * n) (4 * n) (16 * n) k.val :=
    rowNormUpper_pos hK (by norm_num) (by norm_num) hN (4 * n) (16 * n) k.val
  rw [Real.log_mul (by positivity) (Finset.prod_ne_zero_iff.mpr (fun k _ => (hupperPos k).ne')),
    Real.log_prod (fun k _ => (hupperPos k).ne')] at hlog
  have hsum := Finset.sum_le_sum (fun k (_ : k ∈ (Finset.univ : Finset (Fin (51 * n)))) => hrows k)
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hsum
  have hgrid := physicalSaving_grid_lower (2 / 25) (8 / 25)
    (by norm_num) (by norm_num) (by norm_num) hNr (51 * n)
  rw [hrδ] at hgrid
  rw [← Fin.sum_univ_eq_sum_range] at hgrid
  have hscaled := mul_le_mul_of_nonneg_left hgrid hNr.le
  have hmain : Zeta3.Certificate.analyticIntegral * windowScale n =
      ((50 * n : ℕ) : ℝ) ^ 2 *
        (∫ v in (0 : ℝ)..(51 / 50 : ℝ), physicalSaving (2 / 25) (8 / 25)
          (by norm_num) (by norm_num) v) := by
    simp only [Zeta3.Certificate.analyticIntegral, Zeta3.Certificate.saving,
      Zeta3.Parameters.s₁, Zeta3.Parameters.s₂, Zeta3.Parameters.δ,
      windowScale, Nat.cast_mul, Nat.cast_ofNat]
    ring
  rw [neg_mul, hmain]
  unfold analyticError analyticEndpointDrop
  push_cast at hlog hsum hscaled ⊢
  nlinarith

theorem exists_analytic_rate_error : ∃ E : ℕ → ℝ,
    Tendsto (fun n => E n / windowScale n) atTop (𝓝 0) ∧
      (∀ᶠ n in atTop, Real.log (windowValue n) ≤
        -Zeta3.Certificate.analyticIntegral * windowScale n + E n) := by
  obtain ⟨C, hC⟩ := exists_windowValue_log_bound
  refine ⟨analyticError C analyticEndpointDrop, analyticError_over_windowScale_limit C analyticEndpointDrop, ?_⟩
  filter_upwards [eventually_gt_atTop (0 : ℕ)] with n hn
  exact hC n hn

theorem exists_certified_analytic_rate_error (hfinite : Zeta3.Certificate.AnalyticFiniteEvidence) :
    ∃ E : ℕ → ℝ, Tendsto (fun n => E n / windowScale n) atTop (𝓝 0) ∧
      (∀ᶠ n in atTop, Real.log (windowValue n) ≤
        -Zeta3.Parameters.analyticLower * windowScale n + E n) := by
  obtain ⟨E, hE, hbound⟩ := exists_analytic_rate_error
  refine ⟨E, hE, ?_⟩
  filter_upwards [hbound] with n hn
  apply hn.trans
  have h := mul_le_mul_of_nonneg_right (Zeta3.Certificate.analyticLower_le_integral hfinite)
    (sq_nonneg (50 * (n : ℝ)))
  unfold windowScale at *
  linarith

end Zeta3.Analysis

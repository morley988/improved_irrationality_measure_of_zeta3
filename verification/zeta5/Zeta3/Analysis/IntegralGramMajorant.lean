import Zeta3.Analysis.DeterminantMajorant
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp

/-!
# Complex bilinear integral forms and their positive norm majorant

The phase of a contour density has modulus at most one. Cauchy--Schwarz
bounds its bilinear matrix entries by the positive squared norms. Combined
with the factorial-loss determinant lemma, this is the analytic form of the
response majorant, without an assumed determinant-of-integrals identity.
-/

noncomputable section
namespace Zeta3.Analysis
open MeasureTheory
open scoped BigOperators

variable {α : Type*} [MeasurableSpace α] {μ : Measure α}

theorem norm_integral_phase_mul_le {phase f g : α → ℂ}
    (hphase : AEStronglyMeasurable phase μ) (hphaseBound : ∀ᵐ x ∂μ, ‖phase x‖ ≤ 1)
    (hf : MemLp f 2 μ) (hg : MemLp g 2 μ) :
    ‖∫ x, phase x * f x * g x ∂μ‖ ≤
      Real.sqrt (∫ x, ‖f x‖ ^ 2 ∂μ) * Real.sqrt (∫ x, ‖g x‖ ^ 2 ∂μ) := by
  have hprod : Integrable (fun x => ‖f x‖ * ‖g x‖) μ := by
    exact memLp_one_iff_integrable.mp (hg.norm.mul' hf.norm)
  have hbound : ∀ᵐ x ∂μ, ‖phase x * f x * g x‖ ≤ ‖f x‖ * ‖g x‖ := by
    filter_upwards [hphaseBound] with x hx
    simp only [norm_mul]
    have h := mul_le_mul_of_nonneg_right hx (mul_nonneg (norm_nonneg (f x)) (norm_nonneg (g x)))
    nlinarith
  have hint : Integrable (fun x => phase x * f x * g x) μ :=
    hprod.mono' ((hphase.mul hf.1).mul hg.1) hbound
  have hholder : (∫ x, ‖f x‖ * ‖g x‖ ∂μ) ≤
      Real.sqrt (∫ x, ‖f x‖ ^ 2 ∂μ) * Real.sqrt (∫ x, ‖g x‖ ^ 2 ∂μ) := by
    have hpq : (2 : ℝ).HolderConjugate 2 := by norm_num [Real.holderConjugate_iff]
    have h := integral_mul_norm_le_Lp_mul_Lq hpq (by simpa using hf) (by simpa using hg)
    simpa only [Real.rpow_two, ← Real.sqrt_eq_rpow] using h
  exact (norm_integral_le_integral_norm _).trans ((integral_mono_ae hint.norm hprod hbound).trans hholder)

def phaseBilinearMatrix {ι : Type*} (μ : Measure α) (phase : α → ℂ) (f : ι → α → ℂ) :
    Matrix ι ι ℂ := fun i j => ∫ x, phase x * f i x * f j x ∂μ

def integralSquaredNorm {ι : Type*} (μ : Measure α) (f : ι → α → ℂ) (i : ι) : ℝ :=
  ∫ x, ‖f i x‖ ^ 2 ∂μ

theorem integralSquaredNorm_nonneg {ι : Type*} (μ : Measure α) (f : ι → α → ℂ) (i : ι) :
    0 ≤ integralSquaredNorm μ f i := integral_nonneg (fun x => sq_nonneg _)

theorem phaseBilinearMatrix_response_majorant {ι : Type*} [Fintype ι] [DecidableEq ι]
    (phase : α → ℂ) (f : ι → α → ℂ)
    (hphase : AEStronglyMeasurable phase μ) (hphaseBound : ∀ᵐ x ∂μ, ‖phase x‖ ≤ 1)
    (hf : ∀ i, MemLp (f i) 2 μ) (h : ℂ) :
    ‖(1 + h • phaseBilinearMatrix μ phase f).det‖ ≤
      (Nat.factorial (Fintype.card ι) : ℝ) *
        ∏ i, (1 + ‖h‖ * integralSquaredNorm μ f i) := by
  exact determinant_response_majorant _ _ (integralSquaredNorm_nonneg μ f)
    (fun i j => norm_integral_phase_mul_le hphase hphaseBound (hf i) (hf j)) h

end Zeta3.Analysis

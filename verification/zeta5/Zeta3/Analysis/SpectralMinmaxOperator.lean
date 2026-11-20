import Zeta3.Analysis.SpectralMinmax

/-! # The intrinsic symmetric-operator form of the codimension bound -/

noncomputable section
namespace Zeta3.Analysis
open Module
open scoped BigOperators

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

theorem symmetric_eigenvalue_le_of_codimension (T : E →ₗ[ℝ] E) (hT : T.IsSymmetric)
    {r : ℕ} (hr : finrank ℝ E=r) (k : Fin r) (S : Submodule ℝ E)
    (hcodim : finrank ℝ (E ⧸ S) ≤ k.val) (R : ℝ)
    (hRayleigh : ∀ x ∈ S, inner ℝ (T x) x ≤ R*inner ℝ x x) :
    hT.eigenvalues hr k ≤ R := by
  let b := hT.eigenvectorBasis hr
  let e : E ≃ₗ[ℝ] (Fin r → ℝ) :=
    b.repr.toLinearEquiv.trans (WithLp.linearEquiv 2 ℝ (Fin r → ℝ))
  let S' := S.map e.toLinearMap
  have he (x : E) (i : Fin r) : e x i = b.repr x i := rfl
  have hcoord (x : E) (i : Fin r) : e (T x) i = hT.eigenvalues hr i * e x i := by
    exact hT.eigenvectorBasis_apply_self_apply hr x i
  have hinner (x y : E) : inner ℝ x y = ∑ i, e x i*e y i := by
    rw [← b.repr.inner_map_map x y, PiLp.inner_apply]
    apply Finset.sum_congr rfl
    intro i _
    simp only [he, RCLike.inner_apply, starRingEnd_apply, star_trivial]
    ring
  have hdim : finrank ℝ ((Fin r → ℝ) ⧸ S') ≤ k.val := by
    have h₁ := S.finrank_quotient_add_finrank
    have h₂ := S'.finrank_quotient_add_finrank
    have hm := e.finrank_map_eq S
    change finrank ℝ S' = finrank ℝ S at hm
    rw [hr] at h₁
    simp only [Module.finrank_pi, Fintype.card_fin] at h₂
    omega
  apply diagonal_eigenvalue_le_of_codimension (hT.eigenvalues hr) (hT.eigenvalues_antitone hr) k S' hdim R
  intro x hx
  obtain ⟨y,hy,rfl⟩ := Submodule.mem_map.mp hx
  have h := hRayleigh y hy
  rw [hinner (T y) y, hinner y y] at h
  simp only [hcoord] at h
  change (∑ i, hT.eigenvalues hr i*(e y i)^2) ≤ R*∑ i, (e y i)^2
  simpa only [pow_two, mul_assoc] using h

end Zeta3.Analysis

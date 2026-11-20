import Zeta3.Analysis.AngularNormLower
import Zeta3.Analysis.PhysicalComplexComparison
import Zeta3.Analysis.ContourRational
import Zeta3.Analysis.AngularQuantile

/-!
# The angular trial polynomial estimate

The actual angular factor gains a fixed power on the physical axis, which
cancels the same power in its contour modulus. The proved physical norm
comparison and angular quantile bound then combine with the contour deficit.
-/

noncomputable section
namespace Zeta3.Analysis
open MeasureTheory Set Polynomial
open scoped BigOperators

private theorem exponential_factor_bound {a x y g G C K N L F U R : ℝ}
    (ha : 0 ≤ a) (hy : 0 ≤ y) (hg : 0 ≤ g) (hG : 0 ≤ G)
    (hC : 0 ≤ C) (hK : 0 ≤ K) (hN : 0 ≤ N)
    (hx : x ≤ C*Real.exp (N*F)) (hpoly : y ≤ K*g*Real.exp (N*U))
    (hnorm : a*g ≤ G) (hexponent : L+F+U ≤ R) :
    Real.exp (N*L)*a*x*y ≤ C*K*G*Real.exp (N*R) := by
  have hxy := mul_le_mul hx hpoly hy (mul_nonneg hC (Real.exp_nonneg _))
  have hm := mul_le_mul_of_nonneg_left hxy (mul_nonneg (Real.exp_nonneg (N*L)) ha)
  have he : Real.exp (N*L)*a*(C*Real.exp (N*F)*(K*g*Real.exp (N*U))) =
      C*K*(a*g)*Real.exp (N*(L+F+U)) := by
    rw [show N*(L+F+U)=N*L+N*F+N*U by ring, Real.exp_add, Real.exp_add]
    ring
  have hleft : Real.exp (N*L)*a*(x*y)=Real.exp (N*L)*a*x*y := by ring
  rw [he,hleft] at hm
  apply hm.trans
  apply mul_le_mul
  · exact mul_le_mul_of_nonneg_left hnorm (mul_nonneg hC hK)
  · exact Real.exp_le_exp.2 (mul_le_mul_of_nonneg_left hexponent hN)
  · exact Real.exp_nonneg _
  · positivity

/-- A pointwise trial estimate for the genuine physical norm. The two
remaining input inequalities are the already formalized quantile and
potential estimates, so this theorem introduces no external analytic axiom. -/
theorem angular_trial_weighted_contour_bound {j m : ℕ}
    (c : ℝ) (weights poles : Fin j → ℝ) (h : Fin m → ℝ) (hh : ∀ i, h i ∈ Icc 0 1)
    (p : ℝ[X]) (n N m₁ m₂ massIndex : ℕ) (δ b R u F Γ : ℝ)
    (hd : p.natDegree ≤ n) (hdegree : p.natDegree < massIndex)
    (hN : 0 < N) (hm₁ : 0 < m₁) (hm₂ : 0 < m₂)
    (hδ : 0 ≤ δ) (hn : (n:ℝ) ≤ δ*(N:ℝ)) (hb : 0 ≤ b) (hBR : b^2 ≤ R)
    (hBN : 1/(N:ℝ)^2 ≤ b^2) (hu : 0 < u)
    (hmass : (N:ℝ)*physicalMass ((m₁:ℝ)/N) ((m₂:ℝ)/N) b = massIndex)
    (z : ℂ) (hz : Complex.normSq z=u^4)
    (hquantile : (∏ i, (2*|contourAngularCoordinate u z-h i|)^2) ≤
      angularQuantileConstant c weights poles*(N:ℝ)^16*
        Real.exp ((N:ℝ)*(angularField c weights poles (contourAngularCoordinate u z)+F)))
    (hpotential : rationalContourPotential ((m₁:ℝ)/N) ((m₂:ℝ)/N) z+
      2*complexLogPotential
        (physicalSquaredMeasure ((m₁:ℝ)/N) ((m₂:ℝ)/N) (by positivity) (by positivity) b) z-
      physicalEquilibriumAtEndpoint ((m₁:ℝ)/N) ((m₂:ℝ)/N) (by positivity) (by positivity) b ≤
      Γ-angularField c weights poles (contourAngularCoordinate u z)) :
    Real.exp ((N:ℝ)*rationalContourPotential ((m₁:ℝ)/N) ((m₂:ℝ)/N) z)*
      ‖(angularZeroProduct (u^2) h*p).eval₂ Complex.ofRealHom z‖^2 ≤
      angularQuantileConstant c weights poles*
      physicalNormComparisonConstant δ
        (physicalDensityCompactConstant ((m₁:ℝ)/N) ((m₂:ℝ)/N) R)*(N:ℝ)^36*
      normalizedPhysicalNorm N m₁ m₂ (angularZeroProduct (u^2) h*p)*
        Real.exp ((N:ℝ)*(Γ+F)) := by
  have hNr : (0:ℝ)<N := by exact_mod_cast hN
  have hR : 0 < R := lt_of_lt_of_le (lt_of_lt_of_le (by positivity) hBN) hBR
  have hκ := physicalDensityCompactConstant_pos ((m₁:ℝ)/N) ((m₂:ℝ)/N) R hR
  have hK := physicalNormComparisonConstant_pos δ _ hδ hκ
  have hp := actual_physical_complex_norm_bound p n N m₁ m₂ massIndex δ b R
    hd hdegree hN hm₁ hm₂ hδ hn hb hBR hBN hmass z
  have hnorm := angularZeroProduct_normalized_norm_lower (u^2) h (sq_nonneg u)
    (fun i => (hh i).2) N m₁ m₂ hN p
  have hprod : ‖(angularZeroProduct (u^2) h).eval₂ Complex.ofRealHom z‖^2 =
      (u^2)^(4*m)*(∏ i, (2*|contourAngularCoordinate u z-h i|)^2) := by
    rw [← Complex.normSq_eq_norm_sq]
    simpa only [contourAngularCoordinate, ← pow_mul, show 2*2=4 by norm_num] using
      angularZeroProduct_normSq_normalized (u^2) h z (pow_ne_zero _ hu.ne')
        (by simpa only [← pow_mul] using hz)
  have hmain := exponential_factor_bound
    (a := (u^2)^(4*m)) (x := ∏ i, (2*|contourAngularCoordinate u z-h i|)^2)
    (y := ‖p.eval₂ Complex.ofRealHom z‖^2)
    (g := normalizedPhysicalNorm N m₁ m₂ p)
    (G := normalizedPhysicalNorm N m₁ m₂ (angularZeroProduct (u^2) h*p))
    (C := angularQuantileConstant c weights poles*(N:ℝ)^16)
    (K := physicalNormComparisonConstant δ
      (physicalDensityCompactConstant ((m₁:ℝ)/N) ((m₂:ℝ)/N) R)*(N:ℝ)^20)
    (N := N) (L := rationalContourPotential ((m₁:ℝ)/N) ((m₂:ℝ)/N) z)
    (F := angularField c weights poles (contourAngularCoordinate u z)+F)
    (U := 2*complexLogPotential
      (physicalSquaredMeasure ((m₁:ℝ)/N) ((m₂:ℝ)/N) (by positivity) (by positivity) b) z-
      physicalEquilibriumAtEndpoint ((m₁:ℝ)/N) ((m₂:ℝ)/N) (by positivity) (by positivity) b)
    (R := Γ+F)
    (by positivity) (sq_nonneg _) (normalizedPhysicalNorm_nonneg N m₁ m₂ hN p)
    (normalizedPhysicalNorm_nonneg N m₁ m₂ hN _) (by positivity [angularQuantileConstant_pos c weights poles])
    (by positivity) hNr.le hquantile hp hnorm (by linarith)
  rw [Polynomial.eval₂_mul, norm_mul, mul_pow, hprod]
  convert hmain using 1 <;> ring

end Zeta3.Analysis

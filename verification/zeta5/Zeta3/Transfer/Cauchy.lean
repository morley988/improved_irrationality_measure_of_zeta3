import Zeta3.Transfer.Approximation
import Mathlib.Analysis.Complex.Liouville
import Mathlib.Analysis.Calculus.Deriv.Polynomial
import Mathlib.Algebra.Polynomial.Eval.SMul

/-!
# Cauchy estimates supply the local integer-polynomial jet bounds

This module connects a bound for the actual polynomial on a complex disk
to the generic Diophantine transfer theorem. It uses Mathlib's proved
Cauchy derivative estimate; that analytic theorem is not a numerical
certificate assumption.
-/

noncomputable section
namespace Zeta3.Transfer
open Filter Polynomial Metric
open scoped Topology

theorem hasseDeriv_map_int_complex (P : ℤ[X]) (m : ℕ) :
    (hasseDeriv m P).map (Int.castRingHom ℂ) =
      hasseDeriv m (P.map (Int.castRingHom ℂ)) := by
  ext k
  simp [hasseDeriv_coeff]

theorem eval_int_complex_ofReal (P : ℤ[X]) (x : ℝ) :
    P.eval₂ (Int.castRingHom ℂ) (x : ℂ) =
      ((P.eval₂ (Int.castRingHom ℝ) x : ℝ) : ℂ) := by
  induction P using Polynomial.induction_on' with
  | add P Q hP hQ => simp [hP, hQ]
  | monomial n z => simp

theorem polynomial_iteratedDeriv (P : ℂ[X]) (m : ℕ) :
    iteratedDeriv m (fun z : ℂ => P.eval z) =
      fun z => ((Polynomial.derivative : ℂ[X] → ℂ[X])^[m] P).eval z := by
  induction m with
  | zero => simp
  | succ m hm =>
    rw [iteratedDeriv_succ, hm, Function.iterate_succ_apply']
    funext z
    exact Polynomial.deriv _

theorem polynomial_iteratedDeriv_eq_factorial_hasse (P : ℂ[X]) (m : ℕ) (z : ℂ) :
    iteratedDeriv m (fun z : ℂ => P.eval z) z =
      (m.factorial : ℂ) * (hasseDeriv m P).eval z := by
  rw [polynomial_iteratedDeriv]
  have hpoly : m.factorial • hasseDeriv m P =
      (Polynomial.derivative : ℂ[X] → ℂ[X])^[m] P := by
    simpa only [LinearMap.smul_apply] using
      congrFun (Polynomial.factorial_smul_hasseDeriv (R := ℂ) (k := m)) P
  rw [← hpoly]
  simp only [nsmul_eq_mul, Polynomial.eval_mul, Polynomial.eval_natCast]

/-- The factorial cancels exactly when Cauchy's estimate is expressed using
Hasse derivatives. -/
theorem norm_hasse_eval_le_of_sphere_bound (P : ℂ[X]) (x : ℂ) (m : ℕ)
    {r C : ℝ} (hr : 0 < r)
    (hbound : ∀ z ∈ sphere x r, ‖P.eval z‖ ≤ C) :
    ‖(hasseDeriv m P).eval x‖ ≤ C / r ^ m := by
  have h := Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le m hr
    P.differentiable.diffContOnCl hbound
  rw [polynomial_iteratedDeriv_eq_factorial_hasse, norm_mul] at h
  simp only [Complex.norm_natCast] at h
  have hfac : (0 : ℝ) < m.factorial := by exact_mod_cast Nat.factorial_pos m
  apply (mul_le_mul_iff_right₀ hfac).mp
  simpa only [mul_div_assoc] using h

/-- A disk bound centered at the target controls jets at every nearby real
point. The factor two in the original disk radius is the triangle inequality
needed to move the Cauchy circle to that nearby point. -/
theorem abs_int_hasse_eval_le_of_disk_bound (P : ℤ[X]) (ξ x : ℝ) (m : ℕ)
    {r C : ℝ} (hr : 0 < r) (hx : |x - ξ| ≤ r)
    (hbound : ∀ z : ℂ, ‖z - (ξ : ℂ)‖ ≤ 2 * r →
      ‖P.eval₂ (Int.castRingHom ℂ) z‖ ≤ C) :
    |(hasseDeriv m P).eval₂ (Int.castRingHom ℝ) x| ≤ C / r ^ m := by
  have hsphere : ∀ z ∈ sphere (x : ℂ) r,
      ‖(P.map (Int.castRingHom ℂ)).eval z‖ ≤ C := by
    intro z hz
    rw [Polynomial.eval_map]
    apply hbound
    have hz' : ‖z - (x : ℂ)‖ = r := by simpa only [mem_sphere, dist_eq_norm] using hz
    have hx' : ‖(x : ℂ) - (ξ : ℂ)‖ ≤ r := by
      simpa only [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs] using hx
    calc
      ‖z - (ξ : ℂ)‖ ≤ ‖z - (x : ℂ)‖ + ‖(x : ℂ) - (ξ : ℂ)‖ := norm_sub_le_norm_sub_add_norm_sub _ _ _
      _ ≤ 2 * r := by rw [hz']; linarith
  have h := norm_hasse_eval_le_of_sphere_bound (P.map (Int.castRingHom ℂ))
    (x : ℂ) m hr hsphere
  rw [← hasseDeriv_map_int_complex, Polynomial.eval_map, eval_int_complex_ofReal,
    Complex.norm_real, Real.norm_eq_abs] at h
  exact h

/-- The actual complex local polynomial bound needed by the transfer. -/
def LocalPolynomialDecay (ξ : ℝ) (P : ℕ → ℤ[X]) (a κ : ℝ)
    (error : ℕ → ℝ) : Prop :=
  ∀ᶠ n : ℕ in atTop, ∀ z : ℂ,
    ‖z - (ξ : ℂ)‖ ≤ 2 * Real.exp (-a * (n : ℝ)) →
      ‖(P n).eval₂ (Int.castRingHom ℂ) z‖ ≤
        Real.exp (-κ * (n : ℝ) ^ 2 + error n)

theorem LocalPolynomialDecay.localJetDecay {ξ : ℝ} {P : ℕ → ℤ[X]}
    {a κ : ℝ} {error : ℕ → ℝ} (h : LocalPolynomialDecay ξ P a κ error)
    (ha : 0 ≤ a) (B : ℕ) : LocalJetDecay ξ P B a κ error := by
  filter_upwards [h] with n hn
  intro x hx m hm
  have hj := abs_int_hasse_eval_le_of_disk_bound (P n) ξ x m
    (Real.exp_pos _) hx hn
  calc
    |(hasseDeriv m (P n)).eval₂ (Int.castRingHom ℝ) x| ≤
        Real.exp (-κ * (n : ℝ) ^ 2 + error n) / Real.exp (-a * (n : ℝ)) ^ m := hj
    _ = Real.exp (-κ * (n : ℝ) ^ 2 + error n + a * (m : ℝ) * (n : ℝ)) := by
      rw [← Real.exp_nat_mul, ← Real.exp_sub]
      congr 1
      ring
    _ ≤ Real.exp (-κ * (n : ℝ) ^ 2 + error n + a * (B : ℝ) * (n : ℝ)) := by
      apply Real.exp_le_exp.mpr
      have hmR : (m : ℝ) ≤ B := by exact_mod_cast hm
      have han : 0 ≤ a * (n : ℝ) := mul_nonneg ha (Nat.cast_nonneg _)
      nlinarith

/-- Abstract bounded-multiplicity transfer, with the analytic hypothesis
expressed as a local bound on the actual complex polynomial. -/
theorem approximation_exponent_le_of_local_polynomial_decay
    (ξ : ℝ) (P : ℕ → ℤ[X]) (B : ℕ) (degreeRate D a κ : ℝ) (error : ℕ → ℝ)
    (hdegreeRate : 0 < degreeRate) (ha : 0 < a) (hκ : 0 < κ)
    (hdegree : ∀ᶠ n : ℕ in atTop, ((P n).natDegree : ℝ) ≤ degreeRate * (n : ℝ) + D)
    (hjets : HasBoundedRationalJets P B)
    (herror : Tendsto (fun n : ℕ => error n / (n : ℝ) ^ 2) atTop (𝓝 0))
    (hdecay : LocalPolynomialDecay ξ P a κ error) :
    HasApproximationExponentLE ξ (degreeRate * a / κ) :=
  approximation_exponent_le_of_local_jets ξ P B degreeRate D a κ error hdegreeRate ha hκ
    hdegree hjets herror (hdecay.localJetDecay ha.le B)

end Zeta3.Transfer

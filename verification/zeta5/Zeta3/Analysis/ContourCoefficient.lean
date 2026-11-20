import Zeta3.Analysis.ContourProduct
import Zeta3.Construction.Functional
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Calculus.Deriv.Polynomial

/-!
# The actual cubic coefficient is a contour integral

The coefficient of the candidate zeta value is the finite residue sum in the
original construction.  Polynomial division, exact partial fractions and
Cauchy's formula identify it with the contour integral.  The identity is
valid for arbitrary complex polynomial numerators before specializing to the
rational determinant entries.
-/

noncomputable section
open Set MeasureTheory Polynomial Metric
open scoped BigOperators
namespace Zeta3.Analysis

theorem circle_integral_nodal_fraction {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (v : ι → ℂ) (hv : Set.InjOn v s) (P : ℂ[X])
    (c : ℂ) (R : ℝ) (hR : 0 ≤ R) (hvR : ∀ i ∈ s, v i ∈ ball c R) :
    (∮ z in C(c,R), z*P.eval z/(Lagrange.nodal s v).eval z)=
      (2*Real.pi*Complex.I)*
        (∑ i ∈ s, v i*(P.eval (v i)/(Lagrange.nodal s v).derivative.eval (v i))) := by
  let D := Lagrange.nodal s v
  let a := fun i => P.eval (v i)/D.derivative.eval (v i)
  let Q := P/D
  let f := fun i z => (z-v i)⁻¹*(a i*z)
  have hne (z:ℂ) (hz:z∈sphere c R) (i:ι) (hi:i∈s) : z≠v i := by
    intro he
    have hlt := mem_ball.mp (hvR i hi)
    have heq := mem_sphere.mp hz
    rw [he] at heq
    linarith
  have hci (i:ι) (hi:i∈s) : CircleIntegrable (f i) c R := by
    apply ContinuousOn.circleIntegrable hR
    apply ContinuousOn.mul
    · exact (continuousOn_id.sub continuousOn_const).inv₀
        (fun z hz => sub_ne_zero.mpr (hne z hz i hi))
    · fun_prop
  have hsumci : CircleIntegrable (fun z => ∑ i ∈ s,f i z) c R := by
    have he : (fun z => ∑ i ∈ s,f i z)=(∑ i ∈ s,f i) := by
      funext z
      simp
    rw [he]
    exact CircleIntegrable.sum s hci
  have hqdiff : Differentiable ℂ (fun z => z*Q.eval z) := differentiable_id.mul Q.differentiable
  have hqci : CircleIntegrable (fun z => z*Q.eval z) c R :=
    hqdiff.continuous.continuousOn.circleIntegrable hR
  have hqzero : (∮ z in C(c,R), z*Q.eval z)=0 := hqdiff.diffContOnCl.circleIntegral_eq_zero hR
  have hfc (i:ι) (hi:i∈s) : (∮ z in C(c,R),f i z)=(2*Real.pi*Complex.I)*(a i*v i) := by
    have h := ((differentiable_const (a i)).mul differentiable_id).diffContOnCl.circleIntegral_sub_inv_smul
      (f := fun z:ℂ => a i*z) (hvR i hi)
    simpa only [smul_eq_mul,f] using h
  have he : (∮ z in C(c,R),z*P.eval z/D.eval z)=
      ∮ z in C(c,R),z*Q.eval z+∑ i ∈ s,f i z := by
    apply circleIntegral.integral_congr hR
    intro z hz
    dsimp only
    have hp := Zeta5.Construction.partialFraction_evaluation s v hv P z (hne z hz)
    change P.eval z/D.eval z=Q.eval z+∑ i ∈ s,a i/(z-v i) at hp
    rw [show z*P.eval z/D.eval z=z*(P.eval z/D.eval z) by ring,hp,mul_add,Finset.mul_sum]
    congr 1
    apply Finset.sum_congr rfl
    intro i hi
    dsimp [f]
    simp only [div_eq_mul_inv]
    ring
  rw [he,circleIntegral.integral_add hqci hsumci,hqzero,zero_add,circleIntegral.integral_fun_sum hci]
  calc
    (∑ i ∈ s, ∮ z in C(c,R),f i z) = ∑ i ∈ s,(2*Real.pi*Complex.I)*(a i*v i) :=
      Finset.sum_congr rfl hfc
    _ = _ := by
      rw [← Finset.mul_sum]
      congr 1
      apply Finset.sum_congr rfl
      intro i hi
      dsimp [a,D]
      ring

def complexSquarePole (i : ℕ) : ℂ := ((Zeta5.Construction.pole (i+1):ℚ):ℂ)

def complexDenominator (N : ℕ) : ℂ[X] :=
  (Zeta5.Construction.denominator N).map (Rat.castHom ℂ)

def complexNumeratorLinear (N : ℕ) (P : ℂ[X]) : ℂ :=
  ∑ i ∈ Finset.range N,
    (P.eval (complexSquarePole i)/(complexDenominator N).derivative.eval (complexSquarePole i))*
      ((i+1:ℕ):ℂ)^2

theorem complexSquarePole_injective : Function.Injective complexSquarePole := by
  intro i j hij
  apply Zeta5.Construction.squarePole_injective
  exact Rat.cast_injective hij

theorem complexDenominator_eq_nodal (N : ℕ) :
    complexDenominator N=Lagrange.nodal (Finset.range N) complexSquarePole := by
  rw [complexDenominator,Zeta5.Construction.denominator_eq_nodal]
  simp only [Lagrange.nodal,Polynomial.map_prod,Polynomial.map_sub,Polynomial.map_X,Polynomial.map_C,
    complexSquarePole,Rat.coe_castHom]

theorem complexSquarePole_norm (i:ℕ) : ‖complexSquarePole i‖=((i+1:ℕ):ℝ)^2 := by
  simp only [complexSquarePole,Zeta5.Construction.pole,Rat.cast_neg,Rat.cast_pow,Rat.cast_natCast,
    norm_neg,norm_pow,norm_natCast]

theorem complexSquarePole_mem_ball {N i : ℕ} {R : ℝ} (hR : (N:ℝ)^2<R) (hi:i<N) :
    complexSquarePole i∈ball (0:ℂ) R := by
  rw [mem_ball_zero_iff,complexSquarePole_norm]
  have hle : ((i+1:ℕ):ℝ)≤N := by exact_mod_cast hi
  exact (pow_le_pow_left₀ (by positivity) hle 2).trans_lt hR

theorem complexNumeratorLinear_map (N : ℕ) (P : ℚ[X]) :
    complexNumeratorLinear N (P.map (Rat.castHom ℂ))=(Zeta3.Construction.numeratorLinear N P:ℂ) := by
  unfold complexNumeratorLinear Zeta3.Construction.numeratorLinear
  push_cast
  apply Finset.sum_congr rfl
  intro i hi
  simp only [complexDenominator,Polynomial.derivative_map,complexSquarePole,
    ← Rat.coe_castHom (α:=ℂ),eval_map_apply]

theorem complexNumeratorLinear_eq_circleIntegral (N : ℕ) (P : ℂ[X])
    (R : ℝ) (hR : (N:ℝ)^2<R) :
    complexNumeratorLinear N P=-(2*Real.pi*Complex.I)⁻¹*
      (∮ z in C(0,R),z*P.eval z/(complexDenominator N).eval z) := by
  have hR0 : 0 ≤ R := (sq_nonneg (N:ℝ)).trans hR.le
  have h := circle_integral_nodal_fraction (Finset.range N) complexSquarePole
    complexSquarePole_injective.injOn P 0 R hR0
    (fun i hi => complexSquarePole_mem_ball hR (Finset.mem_range.mp hi))
  rw [← complexDenominator_eq_nodal] at h
  have hs : (∑ i ∈ Finset.range N,
      complexSquarePole i*(P.eval (complexSquarePole i)/(complexDenominator N).derivative.eval (complexSquarePole i)))=
      -complexNumeratorLinear N P := by
    unfold complexNumeratorLinear
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro i hi
    simp only [complexSquarePole,Zeta5.Construction.pole,Rat.cast_neg,Rat.cast_pow,Rat.cast_natCast]
    ring
  rw [h,hs]
  have hc : (2*Real.pi*Complex.I:ℂ)≠0 := by
    apply mul_ne_zero
    · apply mul_ne_zero (by norm_num)
      exact Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
    · exact Complex.I_ne_zero
  field_simp

/-- The original rational coefficient, without any replacement by an abstract functional. -/
theorem numeratorLinear_eq_circleIntegral (N : ℕ) (P : ℚ[X])
    (R : ℝ) (hR : (N:ℝ)^2<R) :
    (Zeta3.Construction.numeratorLinear N P:ℂ)=-(2*Real.pi*Complex.I)⁻¹*
      (∮ z in C(0,R),z*P.eval₂ (Rat.castHom ℂ) z/
        (Zeta5.Construction.denominator N).eval₂ (Rat.castHom ℂ) z) := by
  rw [← complexNumeratorLinear_map]
  simpa only [complexDenominator,eval_map] using
    complexNumeratorLinear_eq_circleIntegral N (P.map (Rat.castHom ℂ)) R hR

/-- Exact radial scaling, with its Jacobian, at a circle centered at zero. -/
theorem circleIntegral_scale_zero (f : ℂ → ℂ) (a R : ℝ) :
    (∮ z in C(0,a*R),f z)=(a:ℂ)*(∮ z in C(0,R),f ((a:ℂ)*z)) := by
  unfold circleIntegral
  rw [← intervalIntegral.integral_const_mul]
  apply intervalIntegral.integral_congr
  intro t ht
  simp only [deriv_circleMap,smul_eq_mul,circleMap,zero_add]
  push_cast
  ring

theorem complexNumeratorLinear_eq_scaled_circleIntegral (N : ℕ) (P : ℂ[X])
    (u : ℝ) (hN : 0 < N) (hu : 1 < u) :
    complexNumeratorLinear N P=-(N:ℂ)^4*(2*Real.pi*Complex.I)⁻¹*
      (∮ z in C(0,u^2),z*P.eval ((N:ℂ)^2*z)/(complexDenominator N).eval ((N:ℂ)^2*z)) := by
  have hNr : (0:ℝ)<N := by exact_mod_cast hN
  have hu2 : 1<u^2 := by nlinarith
  have hR : (N:ℝ)^2<(N:ℝ)^2*u^2 := by
    nlinarith [mul_pos (sq_pos_of_pos hNr) (sub_pos.mpr hu2)]
  rw [complexNumeratorLinear_eq_circleIntegral N P ((N:ℝ)^2*u^2) hR,
    circleIntegral_scale_zero (fun z => z*P.eval z/(complexDenominator N).eval z) ((N:ℝ)^2) (u^2)]
  push_cast
  have he : (∮ z in C(0,u^2),(N:ℂ)^2*z*P.eval ((N:ℂ)^2*z)/(complexDenominator N).eval ((N:ℂ)^2*z))=
      (N:ℂ)^2*(∮ z in C(0,u^2),z*P.eval ((N:ℂ)^2*z)/(complexDenominator N).eval ((N:ℂ)^2*z)) := by
    rw [← circleIntegral.integral_const_mul]
    congr 1
    funext z
    ring
  rw [he]
  ring

end Zeta3.Analysis

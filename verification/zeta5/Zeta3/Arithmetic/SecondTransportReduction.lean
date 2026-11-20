import Zeta3.Arithmetic.SecondTransportLift
import Zeta3.Arithmetic.SecondTransportPencil
import Zeta3.Construction.SecondReduction
import Zeta3.Construction.SecondPairing

/-!
# Exact reduction of the actual divided double-kernel pairing

The local feature polynomials are lifted coefficientwise with bounded degree.
The proved cubic residue assembly then identifies the divided constant
coefficient with the actual residue bilinear form used by the rank bound.
-/

noncomputable section
namespace Zeta3.Arithmetic
open Polynomial Matrix Finset Module Zeta5.Arithmetic Zeta5.Construction
open Zeta3.Construction.Features OddZeta.FourValue
open scoped BigOperators
variable {p : ℕ} [Fact p.Prime]

theorem padicReduction_eq_of_sub_lower {a b : ℚ}
    (ha : PadicLower p 0 a) (hb : PadicLower p 0 b) (hab : PadicLower p 1 (a-b)) :
    padicReduction p ⟨a,ha⟩=padicReduction p ⟨b,hb⟩ := by
  apply sub_eq_zero.mp
  rw [←map_sub]
  exact (padicReduction_eq_zero _).mpr hab

theorem secondFeatureSum_eq_subtype (N p : ℕ) [Fact p.Prime] (F : ℕ→ℚ[X]) :
    secondFeatureSum N p F=∑c : nonmaximalReflectedClasses N p,
      secondLocalMultiplier N p c.val*physicalLocalCubicFunctional N p c.val (F c.val) := by
  rw [Finset.sum_coe_sort (nonmaximalReflectedClasses N p)
    (fun c => secondLocalMultiplier N p c*physicalLocalCubicFunctional N p c (F c))]
  simp only [secondFeatureSum,nonmaximalReflectedClasses,Finset.sdiff_eq_filter,
    Finset.sum_filter,ite_not]

theorem secondFeatureSum_integral (N d : ℕ) (hp : 2<p) (hN : 2*N<p^2) (hd : d<p)
    (F : ℕ→ℚ[X]) (hF : ∀c,PolynomialPadicLower p 0 (F c))
    (hFd : ∀c,(F c).natDegree≤d) : PadicLower p 0 (secondFeatureSum N p F) := by
  rw [secondFeatureSum_eq_subtype]
  apply padicLower_sum
  intro c hc
  have hc' := nonmaximalReflectedClasses_half N p c.property
  simpa only [zero_add] using
    (secondLocalMultiplier_integral (by omega : N<p^2)).mul
      (physicalLocalCubicFunctional_integral hp hc'.1 hc'.2 hN (hF c.val) (by
        have := hFd c.val
        omega))

theorem secondFeatureSum_residue (N d : ℕ) (hp : 2<p) (hN : 2*N<p^2) (hd : d<p)
    (F : ℕ→ℚ[X]) (hF : ∀c,PolynomialPadicLower p 0 (F c))
    (hFd : ∀c,(F c).natDegree≤d) (hSum : PadicLower p 0 (secondFeatureSum N p F)) :
    padicReduction p ⟨secondFeatureSum N p F,hSum⟩=
      ∑c : nonmaximalReflectedClasses N p,
        padicReduction p ⟨secondLocalMultiplier N p c.val,
          secondLocalMultiplier_integral (by omega : N<p^2)⟩*
        residuePhysicalFunctional N c.val d hp
          (nonmaximalReflectedClasses_half N p c.property).1
          (nonmaximalReflectedClasses_half N p c.property).2 hN (by omega)
          (reducePolynomial (F c.val) (hF c.val)) := by
  let a (c : nonmaximalReflectedClasses N p) : padicIntegralSubring p :=
    ⟨secondLocalMultiplier N p c.val,secondLocalMultiplier_integral (by omega : N<p^2)⟩
  let b (c : nonmaximalReflectedClasses N p) : padicIntegralSubring p :=
    ⟨physicalLocalCubicFunctional N p c.val (F c.val),
      physicalLocalCubicFunctional_integral hp
        (nonmaximalReflectedClasses_half N p c.property).1
        (nonmaximalReflectedClasses_half N p c.property).2 hN (hF c.val)
        (by have := hFd c.val;omega)⟩
  have he : (⟨secondFeatureSum N p F,hSum⟩ : padicIntegralSubring p)=∑c,a c*b c := by
    apply Subtype.ext
    change secondFeatureSum N p F=(padicIntegralSubring p).subtype (∑c,a c*b c)
    rw [map_sum]
    simp only [map_mul]
    change secondFeatureSum N p F=∑c : nonmaximalReflectedClasses N p,
      secondLocalMultiplier N p c.val*physicalLocalCubicFunctional N p c.val (F c.val)
    exact secondFeatureSum_eq_subtype N p F
  rw [he,map_sum]
  apply Finset.sum_congr rfl
  intro c hc
  rw [map_mul,residuePhysicalFunctional_reduce _ _ _ _ _ _ _ _ _ _ (hFd c.val)]

theorem second_transport_strong_conditions (M p : ℕ) (h : 8*M+100<p^2) :
    4*M+3<p^2 ∧ (4*M+3)/p+3≤p := by
  have hp : 10<p := by nlinarith
  have hp0 : 0<p := by omega
  have hsq : 6*p≤p^2 := by nlinarith
  have hsum : 4*M+3+3*p≤p^2 := by nlinarith
  refine ⟨by omega,?_⟩
  have hdiv := Nat.div_mul_le_self (4*M+3) p
  nlinarith

theorem secondResidueBilinear_apply_actual (N m₁ m₂ r : ℕ) (hp : 2<p)
    (h₁ : 2*(m₁+r)-2<p^2) (h₂ : 2*(m₂+r)-2<p^2)
    (hN : 2*N<p^2) (hD : restrictionDepth m₁ r p+restrictionDepth m₂ r p<p)
    (x : (reducedRestrictionMatrix N m₁ r (by omega : p≠2) h₁).mulVecLin.ker)
    (y : (reducedRestrictionMatrix N m₂ r (by omega : p≠2) h₂).mulVecLin.ker) :
    secondResidueBilinear N m₁ m₂ r hp h₁ h₂ hN hD x y=
      ∑c : nonmaximalReflectedClasses N p,
        padicReduction p ⟨secondLocalMultiplier N p c.val,
          secondLocalMultiplier_integral (by omega : N<p^2)⟩*
        residuePhysicalFunctional N c.val (restrictionDepth m₁ r p+restrictionDepth m₂ r p) hp
          (nonmaximalReflectedClasses_half N p c.property).1
          (nonmaximalReflectedClasses_half N p c.property).2 hN (by omega)
          (residueWindowLocal m₁ r (by omega) h₁ x.val c.val*
            residueWindowLocal m₂ r (by omega) h₂ y.val c.val) := by
  simp [secondResidueBilinear,secondResidueFullBilinear,residueLocalBilinear,
    polynomialProductFunctional,residueWindowLocalMap,LinearMap.coe_mk,AddHom.coe_mk]
  rfl

/-- The actual second residue identity on the two maximal-restriction kernels. -/
theorem normalizedCentralWindow_second_residue (N m₁ m₂ r : ℕ) (hp : 2<p)
    (hNmax : N≤max (m₁+r) (m₂+r))
    (hstrong : 8*max (m₁+r) (m₂+r)+100<p^2)
    (h₁ : 2*(m₁+r)-2<p^2) (h₂ : 2*(m₂+r)-2<p^2)
    (hN : 2*N<p^2) (hD : restrictionDepth m₁ r p+restrictionDepth m₂ r p<p)
    (x y : Fin r→padicIntegralSubring p)
    (hx : (reducedRestrictionMatrix N m₁ r (by omega : p≠2) h₁).mulVecLin
      (localReducedVector x)=0)
    (hy : (reducedRestrictionMatrix N m₂ r (by omega : p≠2) h₂).mulVecLin
      (localReducedVector y)=0)
    (hv : PadicLower p 0 ((p:ℚ)^(2+2*(N%p)/p)*
      (normalizedCentralFunctional N
        (centralWindowPolynomial m₁ r (fun i => (x i:ℚ))*
          centralWindowPolynomial m₂ r (fun i => (y i:ℚ)))).coeff 0)) :
    padicReduction p ⟨(p:ℚ)^(2+2*(N%p)/p)*
      (normalizedCentralFunctional N
        (centralWindowPolynomial m₁ r (fun i => (x i:ℚ))*
          centralWindowPolynomial m₂ r (fun i => (y i:ℚ)))).coeff 0,hv⟩=
      secondResidueBilinear N m₁ m₂ r hp h₁ h₂ hN hD
        ⟨localReducedVector x,hx⟩ ⟨localReducedVector y,hy⟩ := by
  classical
  let M := max (m₁+r) (m₂+r)
  let d := restrictionDepth m₁ r p+restrictionDepth m₂ r p
  let g := centralWindowPolynomial m₁ r (fun i => (x i:ℚ))*
    centralWindowPolynomial m₂ r (fun i => (y i:ℚ))
  let Q (c : ℕ) := residueWindowLocal m₁ r (by omega : p≠2) h₁ (localReducedVector x) c*
    residueWindowLocal m₂ r (by omega : p≠2) h₂ (localReducedVector y) c
  have hQ (c : ℕ) : (Q c).natDegree≤d := by
    exact natDegree_mul_le.trans (Nat.add_le_add
      (residueWindowLocal_natDegree_le m₁ r (by omega) h₁ _ c)
      (residueWindowLocal_natDegree_le m₂ r (by omega) h₂ _ c))
  choose F hF hFd hFred using fun c : ℕ => exists_local_polynomial_lift (Q c) d (hQ c)
  have hg : SquareValuedLower p 0 g :=
    (centralWindowPolynomial_squareValued (by omega : p≠2) m₁ r
      (fun i => (x i:ℚ)) (fun i => (x i).property)).mul
      (centralWindowPolynomial_squareValued (by omega : p≠2) m₂ r
        (fun i => (y i:ℚ)) (fun i => (y i).property))
  have hgdeg : g.natDegree≤2*M := by
    have hdeg := natDegree_mul_le (p:=centralWindowPolynomial m₁ r (fun i => (x i:ℚ)))
      (q:=centralWindowPolynomial m₂ r (fun i => (y i:ℚ)))
    have hdx := centralWindowPolynomial_natDegree_le m₁ r (fun i => (x i:ℚ))
    have hdy := centralWindowPolynomial_natDegree_le m₂ r (fun i => (y i:ℚ))
    have hm₁ := le_max_left (m₁+r) (m₂+r)
    have hm₂ := le_max_right (m₁+r) (m₂+r)
    dsimp only [g]
    change _≤2*max (m₁+r) (m₂+r)
    omega
  have hgmax : max g.natDegree N≤2*M := by
    apply max_le hgdeg
    change N≤2*max (m₁+r) (m₂+r)
    omega
  have hsmallg : 2*max g.natDegree N<p^2 := by
    change 8*M+100<p^2 at hstrong
    omega
  have hglocal (c : ℕ) : PolynomialPadicLower p 0 (g.comp ((localAffine p c)^2)) := by
    dsimp only [g]
    rw [mul_comp]
    simpa only [zero_add] using
      (centralWindow_local_integral m₁ r (by omega : p≠2) h₁ x c).mul
        (centralWindow_local_integral m₂ r (by omega : p≠2) h₂ y c)
  have hgred (c : ℕ) : reducePolynomial (g.comp ((localAffine p c)^2)) (hglocal c)=Q c := by
    have he : g.comp ((localAffine p c)^2)=
        (centralWindowPolynomial m₁ r (fun i => (x i:ℚ))).comp ((localAffine p c)^2)*
        (centralWindowPolynomial m₂ r (fun i => (y i:ℚ))).comp ((localAffine p c)^2) := mul_comp _ _ _
    have hxI := centralWindow_local_integral m₁ r (by omega : p≠2) h₁ x c
    have hyI := centralWindow_local_integral m₂ r (by omega : p≠2) h₂ y c
    rw [reducePolynomial_congr he _ (by simpa only [zero_add] using hxI.mul hyI),
      reducePolynomial_mul _ _ hxI hyI,
      residueWindowLocal_reduction,residueWindowLocal_reduction]
    rfl
  have hGF (c : ℕ) : PolynomialPadicLower p 1 (g.comp ((localAffine p c)^2)-F c) :=
    (reducePolynomial_eq_iff _ _ (hglocal c) (hF c)).mp ((hgred c).trans (hFred c).symm)
  have hkernel (c : ℕ) (hc : c∈maximalReflectedClasses N p) :
      PolynomialPadicLower p 2 (g.comp ((localAffine p c)^2)) := by
    have hxc := centralRestrictionMatrix_kernel N m₁ r (by omega : p≠2) h₁
      (fun i => (x i:ℚ)) (fun i => (x i).property)
      (reducedRestriction_kernel_padic N m₁ r (by omega : p≠2) h₁ x hx) c hc
    have hyc := centralRestrictionMatrix_kernel N m₂ r (by omega : p≠2) h₂
      (fun i => (y i:ℚ)) (fun i => (y i).property)
      (reducedRestriction_kernel_padic N m₂ r (by omega : p≠2) h₂ y hy) c hc
    simpa [g,mul_comp] using hxc.mul hyc
  have hL : (scaledQuotientNumerator N p g).natDegree≤4*M+3 := by
    apply (natDegree_C_mul_le _ _).trans
    apply (normalizedCentralQuotient_momentNumerator_natDegree_le N g).trans
    omega
  have hguard := second_transport_strong_conditions M p hstrong
  have hcong := normalizedCentralFunctional_second_feature_reduction (L₀:=4*M+3)
    F hp hg hsmallg hkernel (fun c _ => hglocal c) (fun c _ _ => hF c)
    (fun c _ _ => hGF c) (by
      intro c hc hn
      have hdF := hFd c
      change d<p at hD
      omega) hL hguard.1 hguard.2
  have hSum := secondFeatureSum_integral N d hp hN hD F hF hFd
  calc
    _=padicReduction p ⟨secondFeatureSum N p F,hSum⟩ :=
      padicReduction_eq_of_sub_lower hv hSum hcong
    _=_ := by
      rw [secondFeatureSum_residue N d hp hN hD F hF hFd hSum,
        secondResidueBilinear_apply_actual]
      apply Finset.sum_congr rfl
      intro c hc
      rw [hFred c.val]

end Zeta3.Arithmetic

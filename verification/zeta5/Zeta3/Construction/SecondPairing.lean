import Zeta3.Construction.SecondFunctional
import Zeta3.Construction.SecondLinear

/-! The actual reduced second form on the two maximal-restriction kernels. -/
noncomputable section
namespace Zeta3.Construction.Features
open Polynomial Finset Module Zeta5.Arithmetic Zeta3.Arithmetic OddZeta.FourValue
variable {p : ℕ} [Fact p.Prime]

def residueWindowLocalMap (m r : ℕ) (hp2 : p≠2) (hsmall : 2*(m+r)-2<p^2) (c : ℤ) :
    (Fin r→PadicResidueField p) →ₗ[PadicResidueField p] (PadicResidueField p)[X] where
  toFun x := residueWindowLocal m r hp2 hsmall x c
  map_add' x y := by
    simp only [residueWindowLocal,Pi.add_apply,map_add,add_mul,sum_add_distrib]
  map_smul' a x := by
    simp only [residueWindowLocal,Pi.smul_apply,smul_eq_mul,map_mul,mul_assoc,
      ← mul_sum,smul_eq_C_mul,RingHom.id_apply]

@[simp] theorem residueWindowLocalMap_apply (m r : ℕ) (hp2 : p≠2)
    (hsmall : 2*(m+r)-2<p^2) (c : ℤ) (x : Fin r→PadicResidueField p) :
    residueWindowLocalMap m r hp2 hsmall c x=residueWindowLocal m r hp2 hsmall x c := rfl

def polynomialProductFunctional {F : Type*} [Field F] (L : F[X] →ₗ[F] F) :
    F[X] →ₗ[F] F[X] →ₗ[F] F where
  toFun P :=
    { toFun Q := L (P*Q)
      map_add' Q R := by rw [mul_add,map_add]
      map_smul' a Q := by rw [mul_smul_comm,map_smul];rfl }
  map_add' P Q := by
    apply LinearMap.ext
    intro R
    change L ((P+Q)*R)=L (P*R)+L (Q*R)
    rw [add_mul,map_add]
  map_smul' a P := by
    apply LinearMap.ext
    intro Q
    change L ((a • P)*Q)=a • L (P*Q)
    rw [smul_mul_assoc,map_smul]

@[simp] theorem polynomialProductFunctional_apply {F : Type*} [Field F]
    (L : F[X] →ₗ[F] F) (P Q : F[X]) : polynomialProductFunctional L P Q=L (P*Q) := rfl

def residueLocalBilinear (N m₁ m₂ r c : ℕ) (hp : 2<p)
    (h₁ : 2*(m₁+r)-2<p^2) (h₂ : 2*(m₂+r)-2<p^2)
    (hN : 2*N<p^2) (hc : 0<c) (hcp : 2*c<p)
    (hD : restrictionDepth m₁ r p+restrictionDepth m₂ r p<p) :
    (Fin r→PadicResidueField p) →ₗ[PadicResidueField p]
      Module.Dual (PadicResidueField p) (Fin r→PadicResidueField p) :=
  ((polynomialProductFunctional
    (residuePhysicalFunctional N c (restrictionDepth m₁ r p+restrictionDepth m₂ r p)
      hp hc hcp hN (by omega))).comp
        (residueWindowLocalMap m₁ r (by omega) h₁ c)).compl₂
          (residueWindowLocalMap m₂ r (by omega) h₂ c)

theorem nonmaximalReflectedClasses_half (N p : ℕ) {c : ℕ}
    (hc : c∈nonmaximalReflectedClasses N p) : 0<c ∧ 2*c<p := by
  have h := mem_Icc.mp (mem_sdiff.mp hc).1
  omega

def secondResidueFullBilinear (N m₁ m₂ r : ℕ) (hp : 2<p)
    (h₁ : 2*(m₁+r)-2<p^2) (h₂ : 2*(m₂+r)-2<p^2)
    (hN : 2*N<p^2) (hD : restrictionDepth m₁ r p+restrictionDepth m₂ r p<p) :
    (Fin r→PadicResidueField p) →ₗ[PadicResidueField p]
      Module.Dual (PadicResidueField p) (Fin r→PadicResidueField p) :=
  ∑ c : nonmaximalReflectedClasses N p,
    (padicReduction p ⟨secondLocalMultiplier N p c.val,
      secondLocalMultiplier_integral (by omega : N<p^2)⟩) •
      residueLocalBilinear N m₁ m₂ r c.val hp h₁ h₂ hN
        (nonmaximalReflectedClasses_half N p c.property).1
        (nonmaximalReflectedClasses_half N p c.property).2 hD

def secondResidueBilinear (N m₁ m₂ r : ℕ) (hp : 2<p)
    (h₁ : 2*(m₁+r)-2<p^2) (h₂ : 2*(m₂+r)-2<p^2)
    (hN : 2*N<p^2) (hD : restrictionDepth m₁ r p+restrictionDepth m₂ r p<p) :
    (reducedRestrictionMatrix N m₁ r (by omega : p≠2) h₁).mulVecLin.ker →ₗ[PadicResidueField p]
      Module.Dual (PadicResidueField p)
        (reducedRestrictionMatrix N m₂ r (by omega : p≠2) h₂).mulVecLin.ker :=
  (reducedRestrictionMatrix N m₂ r (by omega : p≠2) h₂).mulVecLin.ker.dualRestrict.comp
    ((secondResidueFullBilinear N m₁ m₂ r hp h₁ h₂ hN hD).domRestrict
      (reducedRestrictionMatrix N m₁ r (by omega : p≠2) h₁).mulVecLin.ker)

end Zeta3.Construction.Features

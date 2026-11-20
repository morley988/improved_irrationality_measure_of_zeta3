import Zeta3.Construction.SecondRoots
import Zeta3.Arithmetic.FeatureCounts

/-! Exact centered coordinates of the actual local feature polynomials. -/
noncomputable section
namespace Zeta3.Construction.Features
open Polynomial Finset Zeta5.Arithmetic Zeta3.Arithmetic OddZeta.FourValue

/-- Monic polynomial division is linear over the coefficient field. -/
def fieldMonicQuotientMap {F : Type*} [Field F] (L : F[X]) (hL : L.Monic) : F[X] →ₗ[F] F[X] where
  toFun P := P /ₘ L
  map_add' P Q :=
    (div_modByMonic_unique (P /ₘ L + Q /ₘ L) _ hL
      ⟨by rw [mul_add,add_left_comm,add_assoc,modByMonic_add_div,
          ← add_assoc,add_comm (L * _),modByMonic_add_div],
        (degree_add_le _ _).trans_lt
          (max_lt (degree_modByMonic_lt _ hL) (degree_modByMonic_lt _ hL))⟩).1
  map_smul' a P :=
    (div_modByMonic_unique (a • (P /ₘ L)) (a • (P %ₘ L)) hL
      ⟨by rw [mul_smul_comm,← smul_add,modByMonic_add_div],
        (degree_smul_le _ _).trans_lt (degree_modByMonic_lt _ hL)⟩).1

def polynomialShiftMap {F : Type*} [Field F] (a : F) : F[X] →ₗ[F] F[X] where
  toFun P := P.comp (X-C a)
  map_add' P Q := add_comp
  map_smul' b P := by simp only [smul_eq_C_mul,mul_comp,C_comp,RingHom.id_apply]

def centeredCoordinates {F : Type*} [Field F] (L : F[X]) (hL : L.Monic) (n : ℕ) :
    F[X] →ₗ[F] (Fin n→F) :=
  (LinearMap.pi (fun j : Fin n => Polynomial.lcoeff F j.val)).comp
    ((polynomialShiftMap (1/2:F)).comp (fieldMonicQuotientMap L hL))

@[simp] theorem centeredCoordinates_apply {F : Type*} [Field F]
    (L : F[X]) (hL : L.Monic) (n : ℕ) (P : F[X]) (j : Fin n) :
    centeredCoordinates L hL n P j=((P /ₘ L).comp (X-C (1/2:F))).coeff j.val := rfl

theorem centered_polynomial_expansion {F : Type*} [Field F] (Q : F[X]) (a : F) (n : ℕ)
    (hQ : Q.degree<n) :
    Q=∑ j:Fin n,C ((Q.comp (X-C a)).coeff j.val)*(X+C a)^j.val := by
  have hcomp : (Q.comp (X-C a)).degree<n := by
    by_cases hzero : Q=0
    · simp [hzero]
    have hn : Q.natDegree<n := (natDegree_lt_iff_degree_lt hzero).mpr hQ
    apply degree_le_natDegree.trans_lt
    rw [natDegree_comp,natDegree_X_sub_C,mul_one]
    exact_mod_cast hn
  have he : (∑ j:Fin n,monomial j.val ((Q.comp (X-C a)).coeff j.val))=Q.comp (X-C a) := by
    simpa only [Polynomial.sum_monomial_eq] using
      Polynomial.sum_fin (p:=Q.comp (X-C a)) (fun j a => monomial j a) (fun _ => monomial_zero_right _) hcomp
  have hc := congrArg (fun P : F[X] => P.comp (X+C a)) he
  simp only [Polynomial.sum_comp,monomial_comp,comp_assoc,sub_comp,X_comp,C_comp,
    add_sub_cancel_right,comp_X] at hc
  exact hc.symm

theorem rooted_centered_expansion {F : Type*} [Field F]
    (L P : F[X]) (hL : L.Monic) (n : ℕ) (hdvd : L∣P)
    (hdeg : P.degree<(n+L.natDegree:ℕ)) :
    P=∑ j:Fin n,C (centeredCoordinates L hL n P j)*(L*(X+C (1/2:F))^j.val) := by
  have hq : (P /ₘ L).degree<n := by
    by_cases hP : P=0
    · simp [hP]
    have hn := (natDegree_lt_iff_degree_lt hP).mpr hdeg
    have hLP := natDegree_le_of_dvd hdvd hP
    apply degree_le_natDegree.trans_lt
    rw [natDegree_divByMonic _ hL]
    exact_mod_cast (show P.natDegree-L.natDegree<n by omega)
  have he := centered_polynomial_expansion (P /ₘ L) (1/2:F) n hq
  have hmul : L*(P /ₘ L)=P := by
    have hrem := (modByMonic_eq_zero_iff_dvd hL).mpr hdvd
    simpa only [hrem,zero_add] using modByMonic_add_div P L
  conv_lhs => rw [← hmul,he,mul_sum]
  apply sum_congr rfl
  intro j hj
  rw [centeredCoordinates_apply]
  ring

variable {p : ℕ} [Fact p.Prime]

theorem residueWindowLocal_degree_lt_succ (m r : ℕ) (hp2 : p≠2)
    (hsmall : 2*(m+r)-2<p^2) (x : Fin r→PadicResidueField p) (c : ℤ) :
    (residueWindowLocal m r hp2 hsmall x c).degree<(restrictionDepth m r p+1:ℕ) := by
  apply degree_le_natDegree.trans_lt
  exact_mod_cast Nat.lt_succ_of_le (residueWindowLocal_natDegree_le m r hp2 hsmall x c)

theorem residueWindowLocal_degree_lt_of_top_zero (m r c : ℕ) (hp2 : p≠2)
    (hsmall : 2*(m+r)-2<p^2) (hmJ : m≤featureStart m r p)
    (x : Fin r→PadicResidueField p) (hx : (topWindowProjection m r p hmJ).mulVecLin x=0) :
    (residueWindowLocal m r hp2 hsmall x c).degree<(restrictionDepth m r p:ℕ) := by
  have htop : (residueWindowLocal m r hp2 hsmall x c).coeff (restrictionDepth m r p)=0 := by
    rw [residueWindowLocal_top ({c}:Finset ℕ) m r hp2 hsmall x ⟨c,mem_singleton_self c⟩]
    rw [topRestrictionMatrix_factor ({c}:Finset ℕ) m r hp2 hsmall hmJ,Matrix.mulVecLin_mul,
      LinearMap.comp_apply,hx,map_zero]
    rfl
  rw [degree_lt_iff_coeff_zero]
  intro k hk
  by_cases he : k=restrictionDepth m r p
  · simpa only [he] using htop
  · exact coeff_eq_zero_of_natDegree_lt
      ((residueWindowLocal_natDegree_le m r hp2 hsmall x c).trans_lt (by omega))

def localFeatureCoordinateMap (m r c n : ℕ) (hp2 : p≠2)
    (hsmall : 2*(m+r)-2<p^2) :
    (Fin r→PadicResidueField p) →ₗ[PadicResidueField p] (Fin n→PadicResidueField p) :=
  (centeredCoordinates (residueOldRoot m c) (residueOldRoot_monic m c) n).comp
    (residueWindowLocalMap m r hp2 hsmall c)

def residueLocalBasis (m c j : ℕ) : (PadicResidueField p)[X] :=
  residueOldRoot m c*(X+C (1/2:PadicResidueField p))^j

theorem residueWindowLocal_feature_expansion (m r c u : ℕ) (hp2 : p≠2)
    (hsmall : 2*(m+r)-2<p^2) (hmJ : m≤featureStart m r p)
    (hc : 0<c) (hcp : 2*c<p) (x : Fin r→PadicResidueField p)
    (hdeg : (residueWindowLocal m r hp2 hsmall x c).degree<(restrictionDepth m r p+u:ℕ)) :
    residueWindowLocal m r hp2 hsmall x c=
      ∑ j:Fin (secondLocalFeatureCount m r p c u),
        C (localFeatureCoordinateMap m r c (secondLocalFeatureCount m r p c u) hp2 hsmall x j)*
          residueLocalBasis (p:=p) m c j.val := by
  apply rooted_centered_expansion _ _ (residueOldRoot_monic m c) _
    (residueOldRoot_dvd_window m r hp2 hsmall x c)
  rw [residueOldRoot_natDegree]
  have hk := physicalOldRoots_le_depth hp2 hmJ hc hcp
  simpa only [secondLocalFeatureCount,Nat.sub_add_cancel (by omega :
    physicalLocalMultiplicity (m-1) p c≤restrictionDepth m r p+u)] using hdeg

end Zeta3.Construction.Features

import Zeta3.Construction.SecondFunctional

/-! Reduction identities for the actual local window and cubic functional. -/
noncomputable section
namespace Zeta3.Construction.Features
open Polynomial Finset Zeta5.Arithmetic Zeta5.Construction Zeta3.Arithmetic OddZeta.FourValue
variable {p : ℕ} [Fact p.Prime]

theorem reducePolynomial_sum {ι : Type*} [DecidableEq ι] (s : Finset ι) (P : ι→ℚ[X])
    (hP : ∀ i∈s,PolynomialPadicLower p 0 (P i))
    (hSum : PolynomialPadicLower p 0 (∑ i∈s,P i)) :
    reducePolynomial (∑ i∈s,P i) hSum=
      ∑ i∈s,if hi : i∈s then reducePolynomial (P i) (hP i hi) else 0 := by
  classical
  ext k
  rw [reducePolynomial_coeff]
  conv_rhs => rw [finsetSum_coeff]
  have he : (⟨(∑ i∈s,P i).coeff k,hSum k⟩ : padicIntegralSubring p)=
      ∑ i∈s,if hi : i∈s then (⟨(P i).coeff k,hP i hi k⟩ : padicIntegralSubring p) else 0 := by
    apply Subtype.ext
    change (∑ i∈s,P i).coeff k=(padicIntegralSubring p).subtype _
    rw [map_sum,finsetSum_coeff]
    apply sum_congr rfl
    intro i hi
    simp only [dif_pos hi]
    rfl
  rw [he,map_sum]
  apply sum_congr rfl
  intro i hi
  simp only [dif_pos hi,reducePolynomial_coeff]

theorem reducePolynomial_univ_sum {ι : Type*} [Fintype ι] (P : ι→ℚ[X])
    (hP : ∀ i,PolynomialPadicLower p 0 (P i))
    (hSum : PolynomialPadicLower p 0 (∑ i,P i)) :
    reducePolynomial (∑ i,P i) hSum=∑ i,reducePolynomial (P i) (hP i) := by
  classical
  simpa only [mem_univ,↓reduceDIte] using reducePolynomial_sum univ P (fun i _ => hP i) hSum

theorem centralWindow_local_integral (m r : ℕ) (hp2 : p≠2)
    (hsmall : 2*(m+r)-2<p^2) (x : Fin r→padicIntegralSubring p) (c : ℤ) :
    PolynomialPadicLower p 0
      ((centralWindowPolynomial m r (fun i => (x i:ℚ))).comp ((localAffine p c)^2)) := by
  simp only [centralWindowPolynomial,Polynomial.sum_comp,mul_comp,C_comp]
  apply PolynomialPadicLower.sum
  intro i hi
  simpa only [zero_add,centralLocal] using (PolynomialPadicLower.constant (x i).property).mul
    (centralLocal_integral hp2 (m+i.val) (window_index_small m r hsmall i) c)

theorem residueWindowLocal_reduction (m r : ℕ) (hp2 : p≠2)
    (hsmall : 2*(m+r)-2<p^2) (x : Fin r→padicIntegralSubring p) (c : ℤ) :
    reducePolynomial
      ((centralWindowPolynomial m r (fun i => (x i:ℚ))).comp ((localAffine p c)^2))
      (centralWindow_local_integral m r hp2 hsmall x c)=
      residueWindowLocal m r hp2 hsmall (fun i => padicReduction p (x i)) c := by
  let P (i : Fin r) := C (x i:ℚ)*centralLocal p (m+i.val) c
  have hP (i : Fin r) : PolynomialPadicLower p 0 (P i) := by
    simpa only [zero_add] using (PolynomialPadicLower.constant (x i).property).mul
      (centralLocal_integral hp2 (m+i.val) (window_index_small m r hsmall i) c)
  have hs : ((centralWindowPolynomial m r (fun i => (x i:ℚ))).comp ((localAffine p c)^2))=
      ∑ i,P i := by
    simp only [centralWindowPolynomial,Polynomial.sum_comp,mul_comp,C_comp,P,centralLocal]
  rw [reducePolynomial_congr hs _ (PolynomialPadicLower.sum univ P 0 (fun i _ => hP i)),
    reducePolynomial_univ_sum P hP]
  unfold residueWindowLocal
  apply sum_congr rfl
  intro i hi
  rw [reducePolynomial_mul _ _ (PolynomialPadicLower.constant (x i).property)
    (centralLocal_integral hp2 (m+i.val) (window_index_small m r hsmall i) c) (hP i),reducePolynomial_C]
  rfl

theorem reducePolynomial_natDegree_le (P : ℚ[X]) (hP : PolynomialPadicLower p 0 P) :
    (reducePolynomial P hP).natDegree≤P.natDegree := by
  exact natDegree_map_le.trans (natDegree_toSubring P _ _).le

theorem residuePhysicalFunctional_reduce (N c d : ℕ)
    (hp : 2<p) (hc : 0<c) (hcp : 2*c<p) (hsmall : 2*N<p^2)
    (hd : d≤(physicalLocalMonic N p c).natDegree+(p-1))
    (P : ℚ[X]) (hP : PolynomialPadicLower p 0 P) (hPd : P.natDegree≤d) :
    residuePhysicalFunctional N c d hp hc hcp hsmall hd (reducePolynomial P hP)=
      padicReduction p ⟨physicalLocalCubicFunctional N p c P,
        physicalLocalCubicFunctional_integral hp hc hcp hsmall hP (hPd.trans hd)⟩ := by
  classical
  let f := physicalLocalCubicFunctionalMap N p c
  let a (j : Fin (d+1)) : padicIntegralSubring p := ⟨P.coeff j.val,hP j.val⟩
  let b (j : Fin (d+1)) : padicIntegralSubring p :=
    ⟨physicalLocalCubicFunctional N p c (X^j.val),
      physicalLocalCubicFunctional_integral hp hc hcp hsmall
        (polynomialPadicLower_X.pow j.val) (by rw [natDegree_X_pow];omega)⟩
  have hexp : P=∑ j:Fin (d+1),C (P.coeff j.val)*X^j.val := by
    rw [Fin.sum_univ_eq_sum_range (fun j => C (P.coeff j)*X^j)]
    exact P.as_sum_range_C_mul_X_pow' (by omega)
  have hf : physicalLocalCubicFunctional N p c P=
      ∑ j:Fin (d+1),(a j:ℚ)*(b j:ℚ) := by
    rw [← physicalLocalCubicFunctionalMap_apply]
    change f P= _
    rw [hexp,map_sum]
    apply sum_congr rfl
    intro j hj
    rw [← smul_eq_C_mul,map_smul]
    simp only [f,a,b,physicalLocalCubicFunctionalMap_apply,smul_eq_mul]
  have he : (⟨physicalLocalCubicFunctional N p c P,
      physicalLocalCubicFunctional_integral hp hc hcp hsmall hP (hPd.trans hd)⟩ : padicIntegralSubring p)=
      ∑ j:Fin (d+1),a j*b j := by
    apply Subtype.ext
    change physicalLocalCubicFunctional N p c P=(padicIntegralSubring p).subtype _
    rw [map_sum]
    simp only [map_mul]
    exact hf
  rw [he,map_sum]
  have hrdeg := (reducePolynomial_natDegree_le P hP).trans hPd
  have hr : reducePolynomial P hP=∑ j:Fin (d+1),
      monomial j.val (padicReduction p (a j)) := by
    rw [Fin.sum_univ_eq_sum_range (fun j => monomial j (padicReduction p ⟨P.coeff j,hP j⟩))]
    simpa only [reducePolynomial_coeff] using
      (reducePolynomial P hP).as_sum_range' (d+1) (by omega)
  rw [hr,map_sum]
  apply sum_congr rfl
  intro j hj
  rw [residuePhysicalFunctional_monomial,dif_pos (by have := j.isLt;omega),map_mul]

end Zeta3.Construction.Features

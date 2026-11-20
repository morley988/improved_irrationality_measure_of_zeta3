import Zeta3.Construction.FeatureReduction

/-! Finite-degree rational local-integral lifts of actual residue polynomials. -/
noncomputable section
namespace Zeta3.Arithmetic
open Polynomial Finset Zeta5.Arithmetic Zeta3.Construction.Features OddZeta.FourValue
variable {p : ℕ} [Fact p.Prime]

/-- Every residue polynomial of degree at most d has a local-integral rational
lift with the same degree bound. No coefficient witness is trusted. -/
theorem exists_local_polynomial_lift (Q : (PadicResidueField p)[X]) (d : ℕ)
    (hQ : Q.natDegree≤d) :
    ∃ P : ℚ[X], ∃ hP : PolynomialPadicLower p 0 P,
      P.natDegree≤d ∧ reducePolynomial P hP=Q := by
  classical
  choose a ha using fun j : ℕ => padicReduction_surjective (p:=p) (Q.coeff j)
  let PI : (padicIntegralSubring p)[X] := ∑j∈range (d+1),monomial j (a j)
  let P : ℚ[X] := PI.map (padicIntegralSubring p).subtype
  have hP : PolynomialPadicLower p 0 P := by
    intro j
    change PadicLower p 0 ((PI.map (padicIntegralSubring p).subtype).coeff j)
    rw [coeff_map]
    exact (PI.coeff j).property
  refine ⟨P,hP,?_,?_⟩
  · apply Polynomial.natDegree_map_le.trans
    apply Polynomial.natDegree_sum_le_of_forall_le
    intro j hj
    exact (Polynomial.natDegree_monomial_le (a j)).trans (by have := mem_range.mp hj;omega)
  · have he : integralPolynomial P hP=PI := by
      apply Polynomial.map_injective (padicIntegralSubring p).subtype Subtype.val_injective
      rw [integralPolynomial_map]
    rw [reducePolynomial,he]
    simp only [PI,Polynomial.map_sum,Polynomial.map_monomial,ha]
    exact (Q.as_sum_range' (d+1) (by omega)).symm

end Zeta3.Arithmetic

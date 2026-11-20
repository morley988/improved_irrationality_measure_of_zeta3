import Zeta3.Construction.SecondCoordinates
import Zeta3.Construction.SecondMatrix

/-! Integral centered feature bases and the actual local parity rank cap. -/
noncomputable section
namespace Zeta3.Construction.Features
open Polynomial Finset Matrix Module Zeta5.Arithmetic Zeta3.Arithmetic OddZeta.FourValue
variable {p : ℕ} [Fact p.Prime]

theorem reducePolynomial_add (P Q : ℚ[X]) (hP : PolynomialPadicLower p 0 P)
    (hQ : PolynomialPadicLower p 0 Q) (hPQ : PolynomialPadicLower p 0 (P+Q)) :
    reducePolynomial (P+Q) hPQ=reducePolynomial P hP+reducePolynomial Q hQ := by
  have he : integralPolynomial (P+Q) hPQ=integralPolynomial P hP+integralPolynomial Q hQ := by
    apply Polynomial.map_injective (padicIntegralSubring p).subtype Subtype.val_injective
    simp only [Polynomial.map_add,integralPolynomial_map]
  simp only [reducePolynomial,he,Polynomial.map_add]

theorem reducePolynomial_pow (P : ℚ[X]) (hP : PolynomialPadicLower p 0 P)
    (j : ℕ) (hPow : PolynomialPadicLower p 0 (P^j)) :
    reducePolynomial (P^j) hPow=(reducePolynomial P hP)^j := by
  have he : integralPolynomial (P^j) hPow=(integralPolynomial P hP)^j := by
    apply Polynomial.map_injective (padicIntegralSubring p).subtype Subtype.val_injective
    simp only [Polynomial.map_pow,integralPolynomial_map]
  simp only [reducePolynomial,he,Polynomial.map_pow]

theorem reducePolynomial_X (h : PolynomialPadicLower p 0 (X:ℚ[X])) :
    reducePolynomial X h=(X:(PadicResidueField p)[X]) := by
  simpa only [Polynomial.map_X] using reducePolynomial_integer_map (p:=p) (X:ℤ[X])
    (polynomialPadicLower_integer_map (X:ℤ[X]))

theorem reduction_half (hp : 2<p) :
    padicReduction p ⟨(1/2:ℚ),half_integral hp⟩=(1/2:PadicResidueField p) := by
  have htwo : (2:PadicResidueField p)≠0 := by
    apply residue_natCast_ne_zero (n:=2)
    intro h
    have := Nat.le_of_dvd (by norm_num : 0<2) h
    omega
  have he : (2:padicIntegralSubring p)*⟨(1/2:ℚ),half_integral hp⟩=1 := by
    apply Subtype.ext
    change (2:ℚ)*(1/2)=1
    norm_num
  have h := congrArg (padicReduction p) he
  simp only [map_mul,map_ofNat,map_one] at h
  exact (eq_div_iff htwo).mpr (by simpa only [mul_comm] using h)

theorem centeredLocalMonomial_integral (hp : 2<p) (j : ℕ) :
    PolynomialPadicLower p 0 (centeredLocalMonomial j) :=
  (polynomialPadicLower_X.add (PolynomialPadicLower.constant (half_integral hp))).pow j

theorem reduce_centeredLocalMonomial (hp : 2<p) (j : ℕ) :
    reducePolynomial (centeredLocalMonomial j) (centeredLocalMonomial_integral hp j)=
      (X+C (1/2:PadicResidueField p))^j := by
  let hbase := polynomialPadicLower_X.add (PolynomialPadicLower.constant (half_integral hp))
  calc
    _ = (reducePolynomial (X+C (1/2:ℚ)) hbase)^j :=
      reducePolynomial_pow _ hbase j (centeredLocalMonomial_integral hp j)
    _ = _ := by
      rw [reducePolynomial_add _ _ polynomialPadicLower_X
        (PolynomialPadicLower.constant (half_integral hp)) hbase,
        reducePolynomial_X,reducePolynomial_C (1/2:ℚ) (half_integral hp),reduction_half hp]

@[simp] theorem centeredLocalMonomial_natDegree (j : ℕ) :
    (centeredLocalMonomial j).natDegree=j := by
  simp [centeredLocalMonomial,natDegree_pow]

def rationalLocalBasis (m c j : ℕ) : ℚ[X] :=
  physicalLocalMonic (m-1) p c*centeredLocalMonomial j

theorem rationalLocalBasis_integral (m c j : ℕ) (hp : 2<p) :
    PolynomialPadicLower p 0 (rationalLocalBasis (p:=p) m c j) := by
  change PolynomialPadicLower p 0 (physicalLocalMonic (m-1) p c*centeredLocalMonomial j)
  simpa only [zero_add] using (physicalLocalMonic_integral (p:=p) (m-1) (c:ℤ)).mul
    (centeredLocalMonomial_integral hp j)

theorem rationalLocalBasis_natDegree (m c j : ℕ) :
    (rationalLocalBasis (p:=p) m c j).natDegree=physicalLocalMultiplicity (m-1) p c+j := by
  have hm : (centeredLocalMonomial j).Monic := (monic_X_add_C (1/2:ℚ)).pow j
  rw [rationalLocalBasis,(physicalLocalMonic_monic (p:=p) (m-1) (c:ℤ)).natDegree_mul hm,
    physicalLocalMonic_natDegree,centeredLocalMonomial_natDegree]

theorem residueLocalBasis_reduce (m c j : ℕ) (hp : 2<p) :
    reducePolynomial (rationalLocalBasis (p:=p) m c j) (rationalLocalBasis_integral m c j hp)=
      residueLocalBasis (p:=p) m c j := by
  calc
    _ = reducePolynomial (physicalLocalMonic (m-1) p c) (physicalLocalMonic_integral (m-1) (c:ℤ))*
        reducePolynomial (centeredLocalMonomial j) (centeredLocalMonomial_integral hp j) :=
      reducePolynomial_mul _ _ (physicalLocalMonic_integral (m-1) (c:ℤ))
        (centeredLocalMonomial_integral hp j) (rationalLocalBasis_integral m c j hp)
    _ = _ := by rw [reduce_centeredLocalMonomial hp j];rfl

def secondLocalFeatureMatrix (N m₁ m₂ r c u₁ u₂ : ℕ) (hp : 2<p)
    (hc : 0<c) (hcp : 2*c<p) (hN : 2*N<p^2)
    (hD : restrictionDepth m₁ r p+restrictionDepth m₂ r p<p) :
    Matrix (Fin (secondLocalFeatureCount m₁ r p c u₁))
      (Fin (secondLocalFeatureCount m₂ r p c u₂)) (PadicResidueField p) :=
  fun i j => residuePhysicalFunctional N c (restrictionDepth m₁ r p+restrictionDepth m₂ r p)
    hp hc hcp hN (by omega)
      (residueLocalBasis m₁ c i.val*residueLocalBasis m₂ c j.val)

theorem secondLocalFeatureMatrix_same_parity_zero
    (N m₁ m₂ r c u₁ u₂ : ℕ) (hp : 2<p)
    (hc : 0<c) (hcp : 2*c<p) (hN : 2*N<p^2)
    (hD : restrictionDepth m₁ r p+restrictionDepth m₂ r p<p)
    (hu₁ : u₁≤1) (hu₂ : u₂≤1) (hσ : 2*(N%p)<p)
    (hnot : c∉maximalReflectedClasses N p)
    (hk₁ : Even (physicalLocalMultiplicity (m₁-1) p c))
    (hk₂ : Even (physicalLocalMultiplicity (m₂-1) p c))
    (i : Fin (secondLocalFeatureCount m₁ r p c u₁))
    (j : Fin (secondLocalFeatureCount m₂ r p c u₂)) (hij : Even (i.val+j.val)) :
    secondLocalFeatureMatrix N m₁ m₂ r c u₁ u₂ hp hc hcp hN hD i j=0 := by
  let P := rationalLocalBasis (p:=p) m₁ c i.val*rationalLocalBasis (p:=p) m₂ c j.val
  have hP : PolynomialPadicLower p 0 P := by
    simpa only [zero_add] using (rationalLocalBasis_integral m₁ c i.val hp).mul
      (rationalLocalBasis_integral m₂ c j.val hp)
  have hPd : P.natDegree≤restrictionDepth m₁ r p+restrictionDepth m₂ r p := by
    apply natDegree_mul_le.trans
    rw [rationalLocalBasis_natDegree,rationalLocalBasis_natDegree]
    have hi := i.isLt
    have hj := j.isLt
    unfold secondLocalFeatureCount at hi hj
    omega
  have hred : reducePolynomial P hP=residueLocalBasis m₁ c i.val*residueLocalBasis m₂ c j.val := by
    rw [reducePolynomial_mul _ _ (rationalLocalBasis_integral m₁ c i.val hp)
      (rationalLocalBasis_integral m₂ c j.val hp) _,residueLocalBasis_reduce _ _ _ hp,
      residueLocalBasis_reduce _ _ _ hp]
  change residuePhysicalFunctional N c _ hp hc hcp hN _ _=0
  rw [← hred,residuePhysicalFunctional_reduce N c _ hp hc hcp hN _ P hP hPd]
  apply (padicReduction_eq_zero _).mpr
  left
  dsimp [P,rationalLocalBasis]
  rw [physicalLocalMonic_even_count (m₁-1) c hc hcp hk₁,
    physicalLocalMonic_even_count (m₂-1) c hc hcp hk₂]
  exact physicalLocalCubicFunctional_same_parity_zero N c _ _ i.val j.val hc hcp
    ((Fact.out:p.Prime).mod_two_eq_one_iff_ne_two.mpr (by omega)) hσ hnot hij

theorem secondLocalFeatureMatrix_rank_le
    (N m₁ m₂ r c u₁ u₂ : ℕ) (hp : 2<p)
    (hc : 0<c) (hcp : 2*c<p) (hN : 2*N<p^2)
    (hD : restrictionDepth m₁ r p+restrictionDepth m₂ r p<p)
    (hu₁ : u₁≤1) (hu₂ : u₂≤1) (hnot : c∉maximalReflectedClasses N p) :
    (secondLocalFeatureMatrix N m₁ m₂ r c u₁ u₂ hp hc hcp hN hD).rank≤
      secondLocalRankCap N m₁ m₂ r p c u₁ u₂ := by
  unfold secondLocalRankCap
  split_ifs with hh
  · apply matrix_rank_le_parity_cap
    intro i j hij
    exact secondLocalFeatureMatrix_same_parity_zero N m₁ m₂ r c u₁ u₂ hp hc hcp hN hD
      hu₁ hu₂ hh.1 hnot hh.2.1 hh.2.2 i j hij
  · exact le_min (Matrix.rank_le_height _) (Matrix.rank_le_width _)

end Zeta3.Construction.Features

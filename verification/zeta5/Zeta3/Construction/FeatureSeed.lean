import Zeta3.Construction.FeatureNumbers

/-! The leading coefficient at the first complete central-factorial band
is an actual local unit, proved by extracting its divisible root factors. -/

noncomputable section
namespace Zeta3.Construction.Features
open Polynomial Finset Zeta5.Construction Zeta5.Arithmetic OddZeta.FourValue
variable {p : ℕ} [Fact p.Prime]

theorem residue_unit_ne_zero (x : ℚ) (hx : PadicLower p 0 x)
    (hx0 : x ≠ 0) (hi : PadicLower p 0 x⁻¹) : padicReduction p ⟨x,hx⟩ ≠ 0 := by
  intro h
  have h1 := ((padicReduction_eq_zero _).mp h).mul hi
  rw [mul_inv_cancel₀ hx0] at h1
  norm_num [PadicLower] at h1

theorem reduce_localUnitFactor_constant {ι : Type*} [DecidableEq ι]
    (c : ℤ) (s : Finset ι) (r : ι → ℤ) :
    reducePolynomial (localUnitFactor p c s r) (localUnitFactor_integral c s r) =
      C (padicReduction p ⟨(localUnitFactor p c s r).coeff 0,
        localUnitFactor_integral c s r 0⟩) := by
  letI := residueField_charP (p:=p)
  let Q : ℤ[X] := ∏ i ∈ s.filter (fun i => ¬(p:ℤ) ∣ c-r i),
    (C c+C (p:ℤ)*X-C (r i))
  have hQ : Q.map (Int.castRingHom ℚ) = localUnitFactor p c s r := by
    simp [Q, Polynomial.map_prod, localUnitFactor, localLinearFactor, localAffine]
  have hQi := polynomialPadicLower_integer_map (p:=p) Q
  have he : reducePolynomial (localUnitFactor p c s r) (localUnitFactor_integral c s r) =
      Q.map (Int.castRingHom (PadicResidueField p)) := by
    rw [← reducePolynomial_congr hQ hQi (localUnitFactor_integral c s r)]
    exact reducePolynomial_integer_map Q hQi
  have hconst : ∃ a : PadicResidueField p,
      Q.map (Int.castRingHom (PadicResidueField p)) = C a := by
    refine ⟨∏ i ∈ s.filter (fun i => ¬(p:ℤ) ∣ c-r i), ((c:PadicResidueField p)-(r i:PadicResidueField p)), ?_⟩
    simp [Q, Polynomial.map_prod, ← C_sub, map_prod]
  obtain ⟨a,ha⟩ := hconst
  have hc := congrArg (fun P : (PadicResidueField p)[X] => P.coeff 0) (he.trans ha)
  rw [reducePolynomial_coeff, coeff_C_zero] at hc
  rw [he, ha, hc]

theorem reduce_localUnitFactor_constant_ne_zero {ι : Type*} [DecidableEq ι]
    (c : ℤ) (s : Finset ι) (r : ι → ℤ) :
    padicReduction p ⟨(localUnitFactor p c s r).coeff 0,
      localUnitFactor_integral c s r 0⟩ ≠ 0 :=
  residue_unit_ne_zero _ _ (localUnitFactor_constant_ne_zero c s r)
    (localUnitFactor_inverse_constant_integral c s r)

theorem rootPolynomial_local_signed_product (j : ℕ) (c : ℤ) :
    (rootPolynomial (j+1)).comp ((localAffine p c)^2) =
      (localAffine p c)^2 * ∏ i : Fin j × Bool, localLinearFactor p c (signedPhysicalRoot i) := by
  rw [Fintype.prod_prod_type]
  simp only [Fintype.prod_bool, signedPhysicalRoot, ↓reduceIte,
    Bool.false_eq_true, Int.cast_neg, Int.cast_natCast, C_neg, localLinearFactor, sub_neg_eq_add]
  rw [rootPolynomial, Finset.prod_range_succ', mul_comp, Polynomial.prod_comp]
  simp only [sub_comp, X_comp, C_comp, Nat.cast_zero, zero_pow (by decide : 2≠0), C_0, sub_zero]
  rw [← Fin.prod_univ_eq_prod_range]
  rw [mul_comm]
  congr 1
  apply Finset.prod_congr rfl
  intro i hi
  rw [C_pow]
  ring

def centralBandScalar (p D J : ℕ) : ℚ := (p:ℚ)^D / ((2*J).factorial:ℚ)

theorem centralBandScalar_ne_zero (D J : ℕ) : centralBandScalar p D J ≠ 0 := by
  unfold centralBandScalar
  apply div_ne_zero
  · exact pow_ne_zero _ (by exact_mod_cast (Fact.out : p.Prime).ne_zero)
  · exact_mod_cast Nat.factorial_ne_zero (2*J)

theorem centralBandScalar_valuation (D J : ℕ) (hJ : 2*J<p^2)
    (hD : (2*J)/p=D) : padicValRat p (centralBandScalar p D J)=0 := by
  have hp0 : (p:ℚ) ≠ 0 := by exact_mod_cast (Fact.out : p.Prime).ne_zero
  have hf0 : ((2*J).factorial:ℚ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero (2*J)
  rw [centralBandScalar, padicValRat.div (pow_ne_zero _ hp0) hf0,
    padicValRat.pow, padicValRat.self (Fact.out : p.Prime).one_lt,
    padicValRat.of_nat, factorial_padicVal_of_lt_sq hJ, hD]
  ring

theorem centralBandScalar_integral (D J : ℕ) (hJ : 2*J<p^2) (hD : (2*J)/p=D) :
    PadicLower p 0 (centralBandScalar p D J) := by
  right
  rw [centralBandScalar_valuation D J hJ hD]

theorem centralBandScalar_inverse_integral (D J : ℕ) (hJ : 2*J<p^2) (hD : (2*J)/p=D) :
    PadicLower p 0 (centralBandScalar p D J)⁻¹ := by
  right
  rw [padicValRat.inv, centralBandScalar_valuation D J hJ hD]
  norm_num

theorem centralLocal_factorization (D J : ℕ) (hJ : 0<J) (c : ℤ)
    (hk : physicalLocalMultiplicity (J-1) p c = D) :
    centralLocal p J c =
      C (centralBandScalar p D J) * physicalLocalMonic (J-1) p c *
        ((localAffine p c)^2 * localUnitFactor p c Finset.univ (@signedPhysicalRoot (J-1))) := by
  have hs := rootPolynomial_local_signed_product (p:=p) (J-1) c
  rw [Nat.sub_add_cancel hJ] at hs
  rw [centralLocal, centralPolynomial, mul_comp, C_comp, hs,
    local_linear_product_factorization]
  change C (((2*J).factorial:ℚ)⁻¹) * ((localAffine p c)^2 *
      (C ((p:ℚ)^physicalLocalMultiplicity (J-1) p c) *
        physicalLocalMonic (J-1) p c * localUnitFactor p c Finset.univ (@signedPhysicalRoot (J-1)))) = _
  rw [hk]
  simp only [centralBandScalar, div_eq_mul_inv, C_mul]
  ring

theorem reduce_localAffine_sq (c : ℤ)
    (h : PolynomialPadicLower p 0 ((localAffine p c)^2)) :
    reducePolynomial ((localAffine p c)^2) h = C ((c:PadicResidueField p)^2) := by
  have hq : PolynomialPadicLower p 0 ((localAffine p c)^2-C ((0:ℚ)^2)) := by simpa using h
  have he := reduce_local_quadratic (p:=p) 0 c hq
  simpa only [Nat.cast_zero, zero_pow (by decide : 2≠0), C_0, sub_zero] using he

theorem reducedCentralLocal_initial_coeff_ne_zero (hp2 : p≠2) (D J c : ℕ)
    (hJ : 0<J) (hsmall : 2*J<p^2) (hD : (2*J)/p=D)
    (hc : 0<c) (hcp : 2*c<p)
    (hk : physicalLocalMultiplicity (J-1) p c=D) :
    (reducedCentralLocal hp2 J hsmall c).coeff D ≠ 0 := by
  let M := physicalLocalMonic (J-1) p (c:ℤ)
  let U := localUnitFactor p (c:ℤ) Finset.univ (@signedPhysicalRoot (J-1))
  have hM : PolynomialPadicLower p 0 M := physicalLocalMonic_integral (J-1) c
  have hU : PolynomialPadicLower p 0 U := localUnitFactor_integral c _ _
  have hL : PolynomialPadicLower p 0 ((localAffine p (c:ℤ))^2) :=
    by simpa using (localAffine_integral (p:=p) (c:ℤ)).pow 2
  have hLU : PolynomialPadicLower p 0 ((localAffine p (c:ℤ))^2 * U) := by simpa using hL.mul hU
  have hS := centralBandScalar_integral (p:=p) D J hsmall hD
  have hCM : PolynomialPadicLower p 0 (C (centralBandScalar p D J)*M) :=
    by simpa using (PolynomialPadicLower.constant hS).mul hM
  have hprod : PolynomialPadicLower p 0
      (C (centralBandScalar p D J)*M*((localAffine p (c:ℤ))^2 * U)) :=
    by simpa using hCM.mul hLU
  have he := reducePolynomial_congr (centralLocal_factorization (p:=p) D J hJ c hk)
    (centralLocal_integral hp2 J hsmall c) hprod
  rw [reducePolynomial_mul _ _ hCM hLU hprod,
    reducePolynomial_mul _ _ (PolynomialPadicLower.constant hS) hM hCM,
    reducePolynomial_mul _ _ hL hU hLU,
    reducePolynomial_C _ hS, reduce_localAffine_sq _ hL,
    reduce_localUnitFactor_constant] at he
  have hMc : (reducePolynomial M hM).coeff D=1 := by
    have hd : (reducePolynomial M hM).natDegree=D :=
      (reducePolynomial_natDegree_of_monic M hM (physicalLocalMonic_monic (J-1) c)).trans
        ((physicalLocalMonic_natDegree (J-1) c).trans hk)
    rw [← hd]
    exact (reducePolynomial_monic M hM (physicalLocalMonic_monic (J-1) c)).coeff_natDegree
  have hS0 := residue_unit_ne_zero (centralBandScalar p D J) hS
    (centralBandScalar_ne_zero (p:=p) D J) (centralBandScalar_inverse_integral D J hsmall hD)
  have hU0 := reduce_localUnitFactor_constant_ne_zero (p:=p) (c:ℤ) Finset.univ
    (@signedPhysicalRoot (J-1))
  have hc0 : (c:PadicResidueField p) ≠ 0 := by
    apply residue_natCast_ne_zero
    intro hdiv
    have := Nat.le_of_dvd hc hdiv
    omega
  change (reducePolynomial (centralLocal p J c) (centralLocal_integral hp2 J hsmall c)).coeff D ≠ 0
  rw [he, ← C_mul, coeff_mul_C, coeff_C_mul, hMc]
  simpa only [Int.cast_natCast, mul_one] using mul_ne_zero hS0 (mul_ne_zero (pow_ne_zero 2 hc0) hU0)

end Zeta3.Construction.Features

import Zeta3.Construction.FeatureReduction

/-! The actual local central-factorial basis and its exact residue recurrence. -/

noncomputable section
namespace Zeta3.Construction.Features
open Polynomial Zeta5.Construction Zeta5.Arithmetic OddZeta.FourValue
variable {p : ℕ} [Fact p.Prime]

def centralLocal (p j : ℕ) (c : ℤ) : ℚ[X] :=
  (centralPolynomial j).comp ((localAffine p c)^2)

theorem centralLocal_integral (hp2 : p ≠ 2) (j : ℕ) (hj : 2*j < p^2) (c : ℤ) :
    PolynomialPadicLower p 0 (centralLocal p j c) := by
  simpa only [centralLocal, comp_assoc, pow_comp, X_comp] using
    centralPolynomial_local_integral hp2 hj c

def reducedCentralLocal (hp2 : p ≠ 2) (j : ℕ) (hj : 2*j < p^2) (c : ℤ) :
    (PadicResidueField p)[X] :=
  reducePolynomial (centralLocal p j c) (centralLocal_integral hp2 j hj c)

theorem reducedCentralLocal_coeff_zero (hp2 : p ≠ 2) (j k : ℕ)
    (hj : 2*j < p^2) (hk : (2*j)/p < k) (c : ℤ) :
    (reducedCentralLocal hp2 j hj c).coeff k = 0 := by
  rw [reducedCentralLocal, reducePolynomial_coeff, padicReduction_eq_zero]
  simpa only [centralLocal, comp_assoc, pow_comp, X_comp] using
    centralPolynomial_local_high_coeff hp2 hj hk c

theorem reducedCentralLocal_natDegree_le (hp2 : p ≠ 2) (j : ℕ)
    (hj : 2*j < p^2) (c : ℤ) :
    (reducedCentralLocal hp2 j hj c).natDegree ≤ (2*j)/p := by
  apply natDegree_le_iff_coeff_eq_zero.mpr
  intro k hk
  exact reducedCentralLocal_coeff_zero hp2 j k hj hk c

theorem centralPolynomial_succ (j : ℕ) :
    C (((2*j+2 : ℕ):ℚ) * ((2*j+1 : ℕ):ℚ)) * centralPolynomial (j+1) =
      centralPolynomial j * (X-C ((j:ℚ)^2)) := by
  have hf : ((2*(j+1)).factorial : ℚ) = ((2*j+2 : ℕ):ℚ) * ((2*j+1 : ℕ):ℚ) * ((2*j).factorial : ℚ) := by
    rw [show 2*(j+1)= (2*j+1)+1 by omega, Nat.factorial_succ, Nat.factorial_succ]
    push_cast
    ring
  have hden : ((2*j+2 : ℕ):ℚ) * ((2*j+1 : ℕ):ℚ) ≠ 0 := by positivity
  have hc : (((2*j+2 : ℕ):ℚ) * ((2*j+1 : ℕ):ℚ)) * (((2*(j+1)).factorial:ℚ)⁻¹) =
      ((2*j).factorial:ℚ)⁻¹ := by
    rw [hf, mul_inv_rev]
    field_simp
  have hr : rootPolynomial (j+1) = rootPolynomial j * (X-C ((j:ℚ)^2)) := by
    simp only [rootPolynomial, Finset.prod_range_succ]
  rw [centralPolynomial, hr, ← mul_assoc, ← mul_assoc, ← C_mul, hc]
  rfl

theorem centralLocal_succ (j : ℕ) (c : ℤ) :
    C (((2*j+2 : ℕ):ℚ) * ((2*j+1 : ℕ):ℚ)) * centralLocal p (j+1) c =
      centralLocal p j c * ((localAffine p c)^2-C ((j:ℚ)^2)) := by
  have h := congrArg (fun P : ℚ[X] => P.comp ((localAffine p c)^2)) (centralPolynomial_succ j)
  simpa only [mul_comp, C_comp, sub_comp, X_comp, centralLocal] using h

theorem reduce_local_quadratic (j : ℕ) (c : ℤ)
    (hP : PolynomialPadicLower p 0 ((localAffine p c)^2-C ((j:ℚ)^2))) :
    reducePolynomial ((localAffine p c)^2-C ((j:ℚ)^2)) hP =
      C ((c : PadicResidueField p)^2 - (j : PadicResidueField p)^2) := by
  letI := residueField_charP (p := p)
  let Q : ℤ[X] := (C c + C (p:ℤ)*X)^2-C ((j:ℤ)^2)
  have hQ : Q.map (Int.castRingHom ℚ) = (localAffine p c)^2-C ((j:ℚ)^2) := by
    simp [Q, localAffine]
  have hQi : PolynomialPadicLower p 0 (Q.map (Int.castRingHom ℚ)) := hQ.symm ▸ hP
  have he := reducePolynomial_integer_map Q hQi
  rw [← reducePolynomial_congr hQ hQi hP, he]
  simp [Q, CharP.cast_eq_zero (PadicResidueField p) p]

theorem reducedCentralLocal_succ (hp2 : p ≠ 2) (j : ℕ)
    (hj : 2*j < p^2) (hjs : 2*(j+1) < p^2) (c : ℤ) :
    C (((2*j+2 : ℕ) : PadicResidueField p) * ((2*j+1 : ℕ) : PadicResidueField p)) *
        reducedCentralLocal hp2 (j+1) hjs c =
      reducedCentralLocal hp2 j hj c *
        C ((c : PadicResidueField p)^2 - (j : PadicResidueField p)^2) := by
  let d := (2*j+2)*(2*j+1)
  have hd : PolynomialPadicLower p 0 (C (d:ℚ)) := PolynomialPadicLower.constant (padicLower_nat d)
  have hq : PolynomialPadicLower p 0 ((localAffine p c)^2-C ((j:ℚ)^2)) := by
    rw [sub_eq_add_neg]
    have hsq : PolynomialPadicLower p 0 ((localAffine p c)^2) :=
      by simpa using (localAffine_integral (p:=p) c).pow 2
    have hjsq : PadicLower p 0 ((j:ℚ)^2) := by
      convert padicLower_nat (p:=p) (j^2) using 1 <;> push_cast <;> rfl
    exact hsq.add (PolynomialPadicLower.constant hjsq).neg
  have hl : PolynomialPadicLower p 0 (C (d:ℚ)*centralLocal p (j+1) c) :=
    by simpa using hd.mul (centralLocal_integral hp2 (j+1) hjs c)
  have hr : PolynomialPadicLower p 0
      (centralLocal p j c*((localAffine p c)^2-C ((j:ℚ)^2))) :=
    by simpa using (centralLocal_integral hp2 j hj c).mul hq
  have hid : C (d:ℚ)*centralLocal p (j+1) c =
      centralLocal p j c*((localAffine p c)^2-C ((j:ℚ)^2)) := by
    simpa only [d, Nat.cast_mul] using centralLocal_succ (p:=p) j c
  have he := reducePolynomial_congr hid hl hr
  rw [reducePolynomial_mul _ _ hd (centralLocal_integral hp2 (j+1) hjs c) hl,
    reducePolynomial_mul _ _ (centralLocal_integral hp2 j hj c) hq hr,
    reducePolynomial_C_nat d hd, reduce_local_quadratic j c hq] at he
  simpa only [d, Nat.cast_mul, reducedCentralLocal] using he

theorem reducedCentralLocal_coeff_succ (hp2 : p ≠ 2) (j k : ℕ)
    (hj : 2*j < p^2) (hjs : 2*(j+1) < p^2) (c : ℤ)
    (hd : ¬ p ∣ (2*j+2)*(2*j+1)) :
    (reducedCentralLocal hp2 (j+1) hjs c).coeff k =
      (reducedCentralLocal hp2 j hj c).coeff k *
        ((c : PadicResidueField p)^2 - (j : PadicResidueField p)^2) /
          (((2*j+2 : ℕ) : PadicResidueField p) * ((2*j+1 : ℕ) : PadicResidueField p)) := by
  have h := congrArg (fun P : (PadicResidueField p)[X] => P.coeff k)
    (reducedCentralLocal_succ hp2 j hj hjs c)
  rw [coeff_C_mul, coeff_mul_C] at h
  have hd' : (((2*j+2 : ℕ) : PadicResidueField p) * ((2*j+1 : ℕ) : PadicResidueField p)) ≠ 0 := by
    simpa only [Nat.cast_mul] using residue_natCast_ne_zero hd
  apply (eq_div_iff hd').mpr
  simpa only [mul_comm] using h

end Zeta3.Construction.Features

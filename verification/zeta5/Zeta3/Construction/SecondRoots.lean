import Zeta3.Construction.SecondReduction
import Zeta3.Construction.SecondPairing

/-! The actual local features carry all old physical roots. Even root
counts give precisely the reflected even root polynomial. -/
noncomputable section
set_option maxHeartbeats 1200000
namespace Zeta3.Construction.Features
open Polynomial Finset Zeta5.Arithmetic Zeta5.Construction Zeta3.Arithmetic OddZeta.FourValue
variable {p : ℕ} [Fact p.Prime]

def residueOldRoot (m : ℕ) (c : ℤ) : (PadicResidueField p)[X] :=
  reducePolynomial (physicalLocalMonic (m-1) p c) (physicalLocalMonic_integral (m-1) c)

theorem residueOldRoot_monic (m : ℕ) (c : ℤ) : (residueOldRoot (p:=p) m c).Monic :=
  reducePolynomial_monic _ _ (physicalLocalMonic_monic (m-1) c)

theorem residueOldRoot_natDegree (m : ℕ) (c : ℤ) :
    (residueOldRoot (p:=p) m c).natDegree=physicalLocalMultiplicity (m-1) p c := by
  rw [residueOldRoot,reducePolynomial_natDegree_of_monic _ _ (physicalLocalMonic_monic _ _),
    physicalLocalMonic_natDegree]

theorem residueOldRoot_eq_nodal (m : ℕ) (c : ℤ) :
    residueOldRoot (p:=p) m c=∏ i∈localFeatureNodes m p c,
      (X-C (physicalLocalLevel p c i : PadicResidueField p)) := by
  let L : ℤ[X] := ∏ i∈localFeatureNodes m p c,(X-C (physicalLocalLevel p c i))
  have he : L.map (Int.castRingHom ℚ)=physicalLocalMonic (m-1) p c := by
    rw [physicalLocalMonic_eq_nodal]
    simp [L,Lagrange.nodal,localFeatureNodes,Polynomial.map_prod]
  calc
    _ = reducePolynomial (L.map (Int.castRingHom ℚ)) (polynomialPadicLower_integer_map L) :=
      reducePolynomial_congr he.symm _ _
    _ = L.map (Int.castRingHom (PadicResidueField p)) := reducePolynomial_integer_map _ _
    _ = _ := by simp [L,Polynomial.map_prod]

theorem residueOldRoot_dvd_window (m r : ℕ) (hp2 : p≠2)
    (hsmall : 2*(m+r)-2<p^2) (x : Fin r→PadicResidueField p) (c : ℤ) :
    residueOldRoot (p:=p) m c ∣ residueWindowLocal m r hp2 hsmall x c := by
  rw [residueOldRoot_eq_nodal]
  apply Finset.prod_dvd_of_coprime
  · intro i hi j hj hij
    have hinj := featureNodeLevel_injective (p:=p) m c (by omega : 2*(m-1)<p^2)
    apply Polynomial.isCoprime_X_sub_C_of_isUnit_sub
    apply isUnit_iff_ne_zero.mpr
    apply sub_ne_zero.mpr
    intro he
    have h := hinj (a₁:=⟨i,hi⟩) (a₂:=⟨j,hj⟩) he
    exact hij (congrArg Subtype.val h)
  · intro i hi
    apply dvd_iff_isRoot.mpr
    rw [IsRoot.def,residueWindowLocal,eval_finsetSum]
    apply sum_eq_zero
    intro j hj
    rw [eval_mul,eval_C,reducedCentralLocal_eval_level_zero hp2 (m+j.val) m
      (window_index_small m r hsmall j) c i hi (by have := i.1.isLt;omega),mul_zero]

theorem physicalLevels_full_even_interval (N c : ℕ) (hc : 0<c) (hcp : 2*c<p)
    (hcσ : p-N%p≤c) :
    physicalLevels N p c=Icc (-((N/p:ℕ):ℤ)-1) ((N/p:ℕ):ℤ) := by
  ext a
  rw [mem_physicalLevels_iff,mem_Icc]
  have hp := (Fact.out:p.Prime).pos
  have hpZ : (0:ℤ)<p := by exact_mod_cast hp
  have hs := Nat.mod_lt N hp
  have hN : (N:ℤ)=p*((N/p:ℕ):ℤ)+((N%p:ℕ):ℤ) := by
    exact_mod_cast (Nat.mod_add_div N p).symm.trans (by omega)
  have hcZ : (0:ℤ)<c := by exact_mod_cast hc
  have hcpZ : 2*(c:ℤ)<p := by exact_mod_cast hcp
  have hsZ : ((N%p:ℕ):ℤ)<p := by exact_mod_cast hs
  have hcσZ : (p:ℤ)≤c+((N%p:ℕ):ℤ) := by exact_mod_cast (show p≤c+N%p by omega)
  constructor
  · rintro ⟨hlo,hhi,hne⟩
    constructor
    · by_contra hn
      have ha : a≤-((N/p:ℕ):ℤ)-2 := by omega
      nlinarith [mul_le_mul_of_nonneg_left ha hpZ.le]
    · by_contra hn
      have ha : ((N/p:ℕ):ℤ)+1≤a := by omega
      nlinarith [mul_le_mul_of_nonneg_left ha hpZ.le]
  · rintro ⟨hlo,hhi⟩
    refine ⟨?_,?_,?_⟩
    · nlinarith [mul_le_mul_of_nonneg_left hlo hpZ.le]
    · nlinarith [mul_le_mul_of_nonneg_left hhi hpZ.le]
    · intro hz
      have hd : (p:ℤ)∣(c:ℤ) := ⟨-a,by linarith⟩
      have hd' : p∣c := by exact_mod_cast hd
      have hle := Nat.le_of_dvd hc hd'
      omega

theorem physicalLocalMonic_even_count (M c : ℕ) (hc : 0<c) (hcp : 2*c<p)
    (heven : Even (physicalLocalMultiplicity M p c)) :
    physicalLocalMonic M p c=evenLocalRootPolynomial (physicalLocalMultiplicity M p c/2) := by
  have hk := physicalLocalMultiplicity_eq_reflectedSize M p c hc hcp
  have hp := (Fact.out:p.Prime).pos
  have hs := Nat.mod_lt M hp
  have heven' : Even (reflectedSize M p c) := by simpa only [hk] using heven
  obtain ⟨a,ha⟩ := heven'
  by_cases hcs : c≤M%p
  · have hpc : p-M%p≤c := by
      by_contra hn
      have hh : reflectedSize M p c=2*(M/p)+1 := by
        simp [reflectedSize,hcs,show ¬p-c≤M%p by omega]
      rw [hh] at ha
      omega
    have hh : physicalLocalMultiplicity M p c=2*(M/p+1) := by
      rw [hk]
      simp only [reflectedSize,if_pos hcs,if_pos (show p-c≤M%p by omega)]
      omega
    rw [hh,show 2*(M/p+1)/2=M/p+1 by omega,physicalLocalMonic_eq_level_product,
      physicalLevels_full_even_interval M c hc hcp hpc,evenLocalRootPolynomial_eq_interval]
    congr 1
    ext z
    simp only [mem_Icc,Int.cast_add,Int.cast_one]
    omega
  · have hpc : ¬p-M%p≤c := by omega
    have hh : physicalLocalMultiplicity M p c=2*(M/p) := by
      rw [hk]
      simp [reflectedSize,hcs,show ¬p-c≤M%p by omega]
    have hσ : 2*(M%p)<p := by omega
    rw [hh,show 2*(M/p)/2=M/p by omega,physicalLocalMonic_eq_level_product,
      physicalLevels_low_interval M c hc hcp hσ (by omega),evenLocalRootPolynomial_eq_interval]

end Zeta3.Construction.Features

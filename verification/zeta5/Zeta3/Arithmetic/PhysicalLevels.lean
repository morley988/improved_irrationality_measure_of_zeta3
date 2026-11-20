import Zeta3.Arithmetic.LocalResidueCoordinates
import Zeta3.Arithmetic.NonmaximalSecondQuotient
import Zeta3.Arithmetic.UniversalFunctional

/-! Exact signed levels of the nonmaximal physical classes. -/
noncomputable section
namespace Zeta3.Arithmetic
open Polynomial Finset OddZeta.FourValue Zeta5.Arithmetic Zeta5.Construction
variable {p : ℕ} [Fact p.Prime]

def physicalLevels (N p : ℕ) (c : ℤ) : Finset ℤ :=
  (divisibleRootIndices p c Finset.univ (@signedPhysicalRoot N)).image (physicalLocalLevel p c)

theorem signedPhysicalRoot_ne_zero {N : ℕ} (i : Fin N × Bool) : signedPhysicalRoot i ≠ 0 := by
  rcases i with ⟨i, b⟩
  cases b <;> simp only [signedPhysicalRoot, Bool.false_eq_true, if_false, if_true] <;> omega

theorem exists_signedPhysicalRoot {N : ℕ} (x : ℤ) (hx : x ≠ 0)
    (hlo : -(N : ℤ) ≤ x) (hhi : x ≤ N) :
    ∃ i : Fin N × Bool, signedPhysicalRoot i = x := by
  by_cases hpos : 0 < x
  · have hcast : (x.toNat : ℤ) = x := Int.toNat_of_nonneg hpos.le
    have hnat : 0 < x.toNat := by omega
    have hnatN : x.toNat ≤ N := by omega
    refine ⟨(⟨x.toNat - 1, by omega⟩, true), ?_⟩
    simp only [signedPhysicalRoot, if_true]
    rw [show x.toNat - 1 + 1 = x.toNat by omega, hcast]
  · have hneg : x < 0 := by omega
    have hcast : ((-x).toNat : ℤ) = -x := Int.toNat_of_nonneg (by omega)
    have hnat : 0 < (-x).toNat := by omega
    have hnatN : (-x).toNat ≤ N := by omega
    refine ⟨(⟨(-x).toNat - 1, by omega⟩, false), ?_⟩
    simp only [signedPhysicalRoot, Bool.false_eq_true, if_false]
    rw [show (-x).toNat - 1 + 1 = (-x).toNat by omega, hcast, neg_neg]

theorem mem_physicalLevels_iff (N : ℕ) (c a : ℤ) :
    a ∈ physicalLevels N p c ↔
      -(N : ℤ) ≤ c + (p : ℤ) * a ∧ c + (p : ℤ) * a ≤ N ∧ c + (p : ℤ) * a ≠ 0 := by
  constructor
  · intro ha
    obtain ⟨i, hi, rfl⟩ := mem_image.mp ha
    have he := physicalLocalLevel_mul hi
    have hb := signedPhysicalRoot_bounds i
    have hn := signedPhysicalRoot_ne_zero i
    constructor
    · linarith
    constructor
    · linarith
    · intro hz
      apply hn
      linarith
  · rintro ⟨hlo, hhi, hx⟩
    obtain ⟨i, hi⟩ := exists_signedPhysicalRoot (c + (p : ℤ) * a) hx hlo hhi
    apply mem_image.mpr
    refine ⟨i, mem_filter.mpr ⟨mem_univ _, ?_⟩, ?_⟩
    · rw [hi]
      exact ⟨-a, by ring⟩
    · rw [physicalLocalLevel, hi]
      have he : c + (p : ℤ) * a - c = (p : ℤ) * a := by ring
      rw [he, Int.mul_ediv_cancel_left _ (by exact_mod_cast (Fact.out : p.Prime).ne_zero)]

theorem physicalLevels_low_interval (N c : ℕ)
    (hc : 0 < c) (hcp : 2 * c < p)
    (hσ : 2 * (N % p) < p) (hcσ : N % p < c) :
    physicalLevels N p c = Icc (-((N / p : ℕ) : ℤ)) (((N / p : ℕ) : ℤ) - 1) := by
  ext a
  rw [mem_physicalLevels_iff, mem_Icc]
  have hp : 0 < p := (Fact.out : p.Prime).pos
  have hpZ : (0 : ℤ) < p := by exact_mod_cast hp
  have hN : (N : ℤ) = p * ((N / p : ℕ) : ℤ) + ((N % p : ℕ) : ℤ) := by
    exact_mod_cast (Nat.mod_add_div N p).symm.trans (by omega)
  have hcZ : (0 : ℤ) < c := by exact_mod_cast hc
  have hcpZ : 2 * (c : ℤ) < p := by exact_mod_cast hcp
  have hσZ : 2 * ((N % p : ℕ) : ℤ) < p := by exact_mod_cast hσ
  have hcσZ : ((N % p : ℕ) : ℤ) < c := by exact_mod_cast hcσ
  constructor
  · rintro ⟨hlo, hhi, hne⟩
    constructor
    · by_contra hn
      have ha : a ≤ -((N / p : ℕ) : ℤ) - 1 := by omega
      nlinarith [mul_le_mul_of_nonneg_left ha hpZ.le]
    · by_contra hn
      have ha : ((N / p : ℕ) : ℤ) ≤ a := by omega
      nlinarith [mul_le_mul_of_nonneg_left ha hpZ.le]
  · rintro ⟨hlo, hhi⟩
    refine ⟨?_, ?_, ?_⟩
    · nlinarith [mul_le_mul_of_nonneg_left hlo hpZ.le]
    · nlinarith [mul_le_mul_of_nonneg_left hhi hpZ.le]
    · intro hz
      have hd : (p : ℤ) ∣ (c : ℤ) := ⟨-a, by linarith⟩
      have hd' : p ∣ c := by exact_mod_cast hd
      have hle := Nat.le_of_dvd hc hd'
      omega

theorem physicalLevels_high_interval (N c : ℕ)
    (hc : 0 < c) (hcp : 2 * c < p)
    (hσ : p ≤ 2 * (N % p)) (hcσ : c < p - N % p) :
    physicalLevels N p c = Icc (-((N / p : ℕ) : ℤ)) (((N / p : ℕ) : ℤ)) := by
  ext a
  rw [mem_physicalLevels_iff, mem_Icc]
  have hp : 0 < p := (Fact.out : p.Prime).pos
  have hpZ : (0 : ℤ) < p := by exact_mod_cast hp
  have hrem : N % p < p := Nat.mod_lt N hp
  have hN : (N : ℤ) = p * ((N / p : ℕ) : ℤ) + ((N % p : ℕ) : ℤ) := by
    exact_mod_cast (Nat.mod_add_div N p).symm.trans (by omega)
  have hcZ : (0 : ℤ) < c := by exact_mod_cast hc
  have hcpZ : 2 * (c : ℤ) < p := by exact_mod_cast hcp
  have hσZ : (p : ℤ) ≤ 2 * ((N % p : ℕ) : ℤ) := by exact_mod_cast hσ
  have hcσZ : (c : ℤ) + ((N % p : ℕ) : ℤ) < p := by exact_mod_cast (by omega : c + N % p < p)
  constructor
  · rintro ⟨hlo, hhi, hne⟩
    constructor
    · by_contra hn
      have ha : a ≤ -((N / p : ℕ) : ℤ) - 1 := by omega
      nlinarith [mul_le_mul_of_nonneg_left ha hpZ.le]
    · by_contra hn
      have ha : ((N / p : ℕ) : ℤ) + 1 ≤ a := by omega
      nlinarith [mul_le_mul_of_nonneg_left ha hpZ.le]
  · rintro ⟨hlo, hhi⟩
    refine ⟨?_, ?_, ?_⟩
    · nlinarith [mul_le_mul_of_nonneg_left hlo hpZ.le]
    · nlinarith [mul_le_mul_of_nonneg_left hhi hpZ.le]
    · intro hz
      have hd : (p : ℤ) ∣ (c : ℤ) := ⟨-a, by linarith⟩
      have hd' : p ∣ c := by exact_mod_cast hd
      have hle := Nat.le_of_dvd hc hd'
      omega

theorem physicalLocalLevel_injective {N : ℕ} {c : ℤ} :
    Set.InjOn (physicalLocalLevel (N := N) p c)
      (↑(divisibleRootIndices p c Finset.univ (@signedPhysicalRoot N)) : Set (Fin N × Bool)) := by
  intro i hi j hj he
  have hi' := physicalLocalLevel_mul hi
  have hj' := physicalLocalLevel_mul hj
  apply signedPhysicalRoot_injective N
  rw [he] at hi'
  linarith

theorem physicalLocalMonic_eq_level_product (N : ℕ) (c : ℤ) :
    physicalLocalMonic N p c = ∏ a ∈ physicalLevels N p c, (X - C (a : ℚ)) := by
  rw [physicalLocalMonic_eq_nodal, physicalLevels, Finset.prod_image]
  · rfl
  · exact physicalLocalLevel_injective

theorem evenLocalRootPolynomial_eq_interval (q : ℕ) :
    evenLocalRootPolynomial q =
      ∏ a ∈ Icc (-(q : ℤ)) ((q : ℤ) - 1), (X - C (a : ℚ)) := by
  induction q with
  | zero => simp [evenLocalRootPolynomial]
  | succ q ih =>
    have hset : Icc (-((q + 1 : ℕ) : ℤ)) (((q + 1 : ℕ) : ℤ) - 1) =
        insert (-((q : ℤ) + 1)) (insert (q : ℤ) (Icc (-(q : ℤ)) ((q : ℤ) - 1))) := by
      ext a
      simp only [mem_Icc, mem_insert, Nat.cast_add, Nat.cast_one]
      omega
    have h₁ : -((q : ℤ) + 1) ∉ insert (q : ℤ) (Icc (-(q : ℤ)) ((q : ℤ) - 1)) := by
      simp only [mem_insert, mem_Icc]
      omega
    have h₂ : (q : ℤ) ∉ Icc (-(q : ℤ)) ((q : ℤ) - 1) := by simp
    rw [evenLocalRootPolynomial, prod_range_succ]
    change evenLocalRootPolynomial q * _ = _
    rw [ih, hset, prod_insert h₁, prod_insert h₂]
    simp only [Int.cast_neg, Int.cast_add, Int.cast_one, Int.cast_natCast, C_neg, C_add, C_1]
    ring

theorem physicalLocalMonic_nonmaximal_low (N c : ℕ)
    (hc : 0 < c) (hcp : 2 * c < p) (hodd : p % 2 = 1)
    (hσ : 2 * (N % p) < p) (hnot : c ∉ maximalReflectedClasses N p) :
    physicalLocalMonic N p c = evenLocalRootPolynomial (N / p) := by
  have hcσ : N % p < c := by
    by_contra hle
    apply hnot
    apply mem_filter.mpr
    refine ⟨mem_Icc.mpr ⟨hc, by omega⟩, ?_⟩
    rw [reflected_epsilon N p (Fact.out : p.Prime).pos, if_pos hσ]
    unfold reflectedSize
    split_ifs <;> omega
  rw [physicalLocalMonic_eq_level_product, physicalLevels_low_interval N c hc hcp hσ hcσ,
    evenLocalRootPolynomial_eq_interval]

def harmonicLevel (a : ℤ) : ℚ :=
  if 0 ≤ a then Zeta3.Construction.harmonicThree a.toNat
  else Zeta3.Construction.harmonicThree (-a - 1).toNat

theorem harmonicLevel_reflection (a : ℤ) : harmonicLevel (-1 - a) = harmonicLevel a := by
  by_cases ha : 0 ≤ a
  · rw [harmonicLevel, if_neg (by omega), harmonicLevel, if_pos ha]
    congr 2
    omega
  · rw [harmonicLevel, if_pos (by omega), harmonicLevel, if_neg ha]
    congr 2
    omega

theorem harmonicLevel_physical {N c : ℕ} (hc : 0 < c) (hcp : c < p)
    {i : Fin N × Bool}
    (hi : i ∈ divisibleRootIndices p c Finset.univ (@signedPhysicalRoot N)) :
    harmonicLevel (physicalLocalLevel p c i) = Zeta3.Construction.harmonicThree (i.1.val / p) := by
  have hp : 0 < p := (Fact.out : p.Prime).pos
  have hpZ : (0 : ℤ) < p := by exact_mod_cast hp
  have hcZ : (0 : ℤ) < c := by exact_mod_cast hc
  have hcpZ : (c : ℤ) < p := by exact_mod_cast hcp
  have he := physicalLocalLevel_mul hi
  rcases i with ⟨i, b⟩
  cases b
  · simp only [signedPhysicalRoot, Bool.false_eq_true, if_false] at he
    let a := physicalLocalLevel p (c : ℤ) (i, false)
    have ha : a < 0 := by
      dsimp only [a]
      by_contra hh
      have hn : 0 ≤ (p : ℤ) * physicalLocalLevel p (c : ℤ) (i, false) := mul_nonneg hpZ.le (by omega)
      omega
    have hb : ((-a - 1).toNat : ℤ) = -a - 1 := Int.toNat_of_nonneg (by omega)
    have hn : i.val = (p - c - 1) + p * (-a - 1).toNat := by
      have hpc : c + 1 ≤ p := by omega
      have hNatCast : (i.val : ℤ) = ((p - c - 1 : ℕ) : ℤ) + (p : ℤ) * ((-a - 1).toNat : ℤ) := by
        rw [hb, Nat.cast_sub (by omega : 1 ≤ p - c), Nat.cast_sub hcp.le]
        dsimp only [a]
        push_cast at he ⊢
        nlinarith
      exact_mod_cast hNatCast
    change harmonicLevel a = _
    rw [harmonicLevel, if_neg (by omega), hn, Nat.add_mul_div_left _ _ hp,
      Nat.div_eq_of_lt (by omega : p - c - 1 < p), zero_add]
  · simp only [signedPhysicalRoot, if_true] at he
    let a := physicalLocalLevel p (c : ℤ) (i, true)
    have ha : 0 ≤ a := by
      by_contra hh
      have ha' : a ≤ -1 := by omega
      have hm := mul_le_mul_of_nonneg_left ha' hpZ.le
      dsimp only [a] at hm
      push_cast at he
      nlinarith
    have hb : (a.toNat : ℤ) = a := Int.toNat_of_nonneg ha
    have hn : i.val = (c - 1) + p * a.toNat := by
      have hNatCast : (i.val : ℤ) = ((c - 1 : ℕ) : ℤ) + (p : ℤ) * (a.toNat : ℤ) := by
        rw [hb, Nat.cast_sub hc]
        dsimp only [a]
        push_cast at he ⊢
        nlinarith
      exact_mod_cast hNatCast
    change harmonicLevel a = _
    rw [harmonicLevel, if_pos ha, hn, Nat.add_mul_div_left _ _ hp,
      Nat.div_eq_of_lt (by omega : c - 1 < p), zero_add]

end Zeta3.Arithmetic

import Zeta3.Arithmetic.SecondMoment
import Zeta3.Arithmetic.ReflectedDistribution

/-! The second local form is extracted from the actual cubic functional,
with proper fractions and the polynomial quotient using the same factor. -/
noncomputable section
namespace Zeta3.Arithmetic
open Polynomial Finset OddZeta.FourValue Zeta5.Arithmetic Zeta5.Construction
variable {p : ℕ} [Fact p.Prime]

theorem sum_signed_physical_eq_reflected {M : Type*} [AddCommMonoid M]
    (N c : ℕ) (hc : 0 < c) (hcp : 2 * c < p) (f : ℕ → M) :
    (∑ i ∈ divisibleRootIndices p c Finset.univ (@signedPhysicalRoot N), f (i.1.val + 1)) =
      ∑ i ∈ reflectedNodes N p c, f i := by
  apply sum_bij (fun i _ => i.1.val + 1)
  · intro i hi
    have hm := (divisible_signedPhysicalRoot_iff hc (by omega) i).mp (mem_filter.mp hi).2
    apply mem_reflectedNodes.mpr
    refine ⟨by omega, by have := i.1.isLt; omega, ?_⟩
    cases hbi : i.2 <;> simp only [hbi, Bool.false_eq_true, ↓reduceIte] at hm
    · exact Or.inr hm
    · exact Or.inl hm
  · rintro ⟨i, bi⟩ hi ⟨j, bj⟩ hj he
    change i.val + 1 = j.val + 1 at he
    have hij : i = j := Fin.ext (by omega)
    subst j
    have hmi := (divisible_signedPhysicalRoot_iff hc (by omega) (i, bi)).mp (mem_filter.mp hi).2
    have hmj := (divisible_signedPhysicalRoot_iff hc (by omega) (i, bj)).mp (mem_filter.mp hj).2
    apply congr_arg (fun b : Bool => (i, b))
    cases bi <;> cases bj <;> simp only [Bool.false_eq_true, ↓reduceIte] at hmi hmj ⊢ <;> omega
  · intro i hi
    obtain ⟨hi0, hiN, hm⟩ := mem_reflectedNodes.mp hi
    have his : i - 1 + 1 = i := by omega
    rcases hm with hm | hm
    · refine ⟨(⟨i - 1, by omega⟩, true), ?_, his⟩
      apply mem_filter.mpr
      refine ⟨mem_univ _, ?_⟩
      apply (divisible_signedPhysicalRoot_iff hc (by omega) _).mpr
      simpa only [↓reduceIte, his] using hm
    · refine ⟨(⟨i - 1, by omega⟩, false), ?_, his⟩
      apply mem_filter.mpr
      refine ⟨mem_univ _, ?_⟩
      apply (divisible_signedPhysicalRoot_iff hc (by omega) _).mpr
      simpa only [Bool.false_eq_true, ↓reduceIte, his] using hm
  · intro i hi
    rfl

def nodeCubicFunctional (S : Finset ℤ) (L P : ℚ[X]) : ℚ :=
  (∑ a ∈ S, P.eval (a : ℚ) * (L.derivative.eval (a : ℚ))⁻¹ * harmonicLevel a) +
    (1 / 2) * bernoulliFunctional (P / L).derivative

def physicalLocalCubicFunctional (N p c : ℕ) (P : ℚ[X]) : ℚ :=
  nodeCubicFunctional (physicalLevels N p c) (physicalLocalMonic N p c) P

theorem physicalLocalCubicFunctional_eq_signed (N c : ℕ) (P : ℚ[X]) :
    physicalLocalCubicFunctional N p c P =
      (∑ i ∈ divisibleRootIndices p c Finset.univ (@signedPhysicalRoot N),
        P.eval (physicalLocalLevel p c i : ℚ) *
        ((physicalLocalMonic N p c).derivative.eval (physicalLocalLevel p c i : ℚ))⁻¹ *
        harmonicLevel (physicalLocalLevel p c i)) +
      (1 / 2) * bernoulliFunctional (P / physicalLocalMonic N p c).derivative := by
  rw [physicalLocalCubicFunctional, nodeCubicFunctional, physicalLevels, sum_image]
  exact physicalLocalLevel_injective

theorem second_local_class_reduction_to_features {N c L₀ : ℕ} {g F : ℚ[X]}
    (hp : 2 < p) (hg : SquareValuedLower p 0 g)
    (hsmall : 2 * max g.natDegree N < p ^ 2)
    (hkernel : ∀ d ∈ maximalReflectedClasses N p,
      PolynomialPadicLower p 1 (g.comp ((localAffine p d) ^ 2)))
    (hc : 0 < c) (hcp : 2 * c < p) (hnot : c ∉ maximalReflectedClasses N p)
    (hglocal : PolynomialPadicLower p 0 (g.comp ((localAffine p c) ^ 2)))
    (hF : PolynomialPadicLower p 0 F)
    (hGF : PolynomialPadicLower p 1 (g.comp ((localAffine p c) ^ 2) - F))
    (hFdegree : F.natDegree ≤ (physicalLocalMonic N p c).natDegree + (p - 1))
    (hL₀ : (scaledQuotientNumerator N p g).natDegree ≤ L₀) (hL₀p : L₀ < p ^ 2)
    (hE : L₀ / p + 3 ≤ p) :
    PadicLower p 1
      ((p : ℚ) ^ (2 + 2 * (N % p) / p) *
        (∑ i ∈ reflectedNodes N p c, (normalizedResidue N g i).coeff 0) +
        bernoulliFunctional ((scaledQuotientNumerator N p g).comp (localAffine p c)).derivative -
        secondLocalMultiplier N p c * physicalLocalCubicFunctional N p c F) := by
  have hN : N ≤ max g.natDegree N := le_max_right _ _
  have hodd := (Fact.out : p.Prime).mod_two_eq_one_iff_ne_two.mpr (by omega : p ≠ 2)
  have hm := physicalLocalMultiplicity_nonmaximal hc hcp hodd hnot
  rw [double_div_eq] at hm
  have hproper := padicLower_sum (p := p)
    (divisibleRootIndices p c Finset.univ (@signedPhysicalRoot N)) _ 1
    (fun i hi => second_residue_reduction_to_features hp hc hcp (by omega) hglocal hF hGF hi hm)
  have hmoment := second_local_moment_reduction_to_features hp hg hsmall hkernel hc hcp hnot
    hglocal hF hGF hFdegree hL₀ hL₀p hE
  have h := hproper.add hmoment
  rw [sum_sub_distrib, ← mul_sum, sum_signed_physical_eq_reflected N c hc hcp (fun i => (normalizedResidue N g i).coeff 0)] at h
  rw [physicalLocalCubicFunctional_eq_signed]
  have hs : (∑ i ∈ divisibleRootIndices p c Finset.univ (@signedPhysicalRoot N),
      secondLocalMultiplier N p c * F.eval (physicalLocalLevel p c i : ℚ) *
        ((physicalLocalMonic N p c).derivative.eval (physicalLocalLevel p c i : ℚ))⁻¹ *
        harmonicLevel (physicalLocalLevel p c i)) =
    secondLocalMultiplier N p c *
      ∑ i ∈ divisibleRootIndices p c Finset.univ (@signedPhysicalRoot N),
        F.eval (physicalLocalLevel p c i : ℚ) *
        ((physicalLocalMonic N p c).derivative.eval (physicalLocalLevel p c i : ℚ))⁻¹ *
        harmonicLevel (physicalLocalLevel p c i) := by
    rw [mul_sum]
    apply sum_congr rfl
    intro i hi
    ring
  rw [hs] at h
  convert h using 1
  ring

end Zeta3.Arithmetic

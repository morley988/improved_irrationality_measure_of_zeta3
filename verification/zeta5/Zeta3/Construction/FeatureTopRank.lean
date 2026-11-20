import Zeta3.Construction.FeatureSeed

/-! Exact rank of the top coefficients of the actual central restriction
matrix. The proof uses the proved local recurrence and unit seed. -/

noncomputable section
namespace Zeta3.Construction.Features
open Polynomial Matrix Finset Zeta5.Arithmetic OddZeta.FourValue
variable {p : ℕ} [Fact p.Prime]

theorem featureTop_index_small (m r : ℕ) (hsmall : 2*(m+r)-2<p^2)
    (h : Fin (featureTopCount m r p)) :
    2*(featureStart m r p+h.val)<p^2 := by
  have hh := h.isLt
  unfold featureTopCount at hh
  omega

def topFeatureMatrix (s : Finset ℕ) (m r : ℕ) (hp2 : p≠2)
    (hsmall : 2*(m+r)-2<p^2) :
    Matrix s (Fin (featureTopCount m r p)) (PadicResidueField p) :=
  fun c h => (reducedCentralLocal hp2 (featureStart m r p+h.val)
    (featureTop_index_small m r hsmall h) (c:ℕ)).coeff (restrictionDepth m r p)

theorem topFeatureMatrix_rank (s : Finset ℕ) (m r : ℕ) (hp2 : p≠2)
    (hsmall : 2*(m+r)-2<p^2) (hm : 0<m) (hmJ : m≤featureStart m r p)
    (hs : ∀ c∈s, 0<c ∧ 2*c<p) :
    (topFeatureMatrix s m r hp2 hsmall).rank =
      min (featureTopCount m r p) s.card := by
  let J := featureStart m r p
  let D := restrictionDepth m r p
  let H := featureTopCount m r p
  have hJR : J≤m+r-1 := featureStart_le m r p (by omega)
  have hH : 0<H := by dsimp [H, featureTopCount]; omega
  have hJ : 0<J := lt_of_lt_of_le hm hmJ
  have hJsmall : 2*J<p^2 := by omega
  have hD : (2*J)/p=D := feature_high_depth m r p J (Fact.out : p.Prime).pos le_rfl (by omega)
  have hpodd : p%2=1 := (Fact.out : p.Prime).mod_two_eq_one_iff_ne_two.mpr hp2
  let T : s → ℕ → PadicResidueField p := fun c h =>
    if hh : h<H then
      (reducedCentralLocal hp2 (J+h) (featureTop_index_small m r hsmall ⟨h,hh⟩) (c:ℕ)).coeff D
    else 0
  have hT0 : ∀ c, T c 0 ≠ 0 := by
    intro c
    dsimp only [T]
    rw [dif_pos hH]
    have hk : physicalLocalMultiplicity (J-1) p (c:ℕ)=D := by
      rw [physicalLocalMultiplicity_eq_reflectedSize (J-1) p c (hs c c.property).1 (hs c c.property).2]
      exact reflectedSize_halfBoundary D p c hpodd (hs c c.property).1 (hs c c.property).2
    simpa only [Nat.add_zero] using reducedCentralLocal_initial_coeff_ne_zero hp2 D J c hJ
      hJsmall hD (hs c c.property).1 (hs c c.property).2 hk
  let d : ℕ → PadicResidueField p := fun h => ((2*(J+h)+2:ℕ):PadicResidueField p) *
    ((2*(J+h)+1:ℕ):PadicResidueField p)
  have hd : ∀ h, h+1<H → d h≠0 := by
    intro h hh
    have hJR' : J+h+1<m+r := by dsimp [H, featureTopCount] at hh; omega
    have hhunit := feature_high_denominator_unit m r p (J+h) (Fact.out : p.Prime)
      (by dsimp [J]; omega) hJR'
    simpa only [d, Nat.cast_mul] using residue_natCast_ne_zero hhunit
  have hstep : ∀ c h, h+1<H → T c (h+1)=
      T c h*((c.val:PadicResidueField p)^2-((J+h:ℕ):PadicResidueField p)^2)/d h := by
    intro c h hh
    have hh0 : h<H := by omega
    have hJR' : J+h+1<m+r := by dsimp [H, featureTopCount] at hh; omega
    have hhunit := feature_high_denominator_unit m r p (J+h) (Fact.out : p.Prime)
      (by dsimp [J]; omega) hJR'
    dsimp only [T]
    rw [dif_pos hh, dif_pos hh0]
    simpa only [Nat.add_assoc, Int.cast_natCast, d] using
      reducedCentralLocal_coeff_succ hp2 (J+h) D
        (featureTop_index_small m r hsmall ⟨h,hh0⟩)
        (by have := featureTop_index_small m r hsmall ⟨h+1,hh⟩; simpa only [Nat.add_assoc] using this)
        (c:ℕ) hhunit
  have he : topFeatureMatrix s m r hp2 hsmall = Matrix.of (fun c (h:Fin H) => T c h.val) := by
    ext c h
    dsimp only [topFeatureMatrix, Matrix.of_apply, T]
    rw [dif_pos (show h.val<H from h.isLt)]
  rw [he]
  simpa only [Fintype.card_coe] using recurrence_feature_rank H
    (fun c:s => (c.val:PadicResidueField p)^2) (residue_square_injective s hs)
    (fun h => ((J+h:ℕ):PadicResidueField p)^2) d hd T hT0 hstep

def reducedRestrictionMatrix (N m r : ℕ) (hp2 : p≠2)
    (hsmall : 2*(m+r)-2<p^2) :
    Matrix (WindowRestrictionIndex N m r p) (Fin r) (PadicResidueField p) :=
  fun a i => padicReduction p ⟨centralRestrictionMatrix N m r p a i,
    centralRestrictionMatrix_integral N m r hp2 hsmall a i⟩

theorem reducedRestrictionMatrix_eq_local (N m r : ℕ) (hp2 : p≠2)
    (hsmall : 2*(m+r)-2<p^2) (a : WindowRestrictionIndex N m r p) (i : Fin r) :
    reducedRestrictionMatrix N m r hp2 hsmall a i =
      (reducedCentralLocal hp2 (m+i.val) (by have := i.isLt; omega) a.1.val).coeff a.2.val := by
  rw [reducedCentralLocal, reducePolynomial_coeff]
  rfl

end Zeta3.Construction.Features

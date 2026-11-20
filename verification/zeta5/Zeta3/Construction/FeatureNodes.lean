import Zeta3.Construction.FeatureLinear
import Zeta5.Arithmetic.LocalInterpolation

/-! Distinct local interpolation nodes and the triangular central basis. -/

noncomputable section
namespace Zeta3.Construction.Features
open Polynomial Finset Matrix Zeta5.Construction Zeta5.Arithmetic OddZeta.FourValue
variable {p : ℕ} [Fact p.Prime]

def localFeatureNodes (J p : ℕ) (c : ℤ) : Finset (Fin (J-1) × Bool) :=
  divisibleRootIndices p c Finset.univ (@signedPhysicalRoot (J-1))

def freeLocalFeatureNodes (J m p : ℕ) (c : ℤ) : Finset (Fin (J-1) × Bool) :=
  (localFeatureNodes J p c).filter (fun i => m ≤ i.1.val + 1)

abbrev FreeFeatureIndex (s : Finset ℕ) (J m p : ℕ) :=
  Σ c:s, {i // i∈freeLocalFeatureNodes J m p (c:ℕ)}

def featureNodeNumber {s : Finset ℕ} {J m p : ℕ} (a : FreeFeatureIndex s J m p) : ℕ :=
  a.2.val.1.val+1

theorem featureNodeNumber_bounds {s : Finset ℕ} {J m p : ℕ}
    (a : FreeFeatureIndex s J m p) : m≤featureNodeNumber a ∧ featureNodeNumber a<J := by
  have ha := (Finset.mem_filter.mp a.2.property).2
  have hb := a.2.val.1.isLt
  exact ⟨ha,by dsimp [featureNodeNumber]; omega⟩

theorem featureNodeNumber_injective (s : Finset ℕ) (J m p : ℕ)
    (hs : ∀ c∈s, 0<c ∧ 2*c<p) :
    Function.Injective (@featureNodeNumber s J m p) := by
  rintro ⟨c,⟨⟨i,bi⟩,hi⟩⟩ ⟨d,⟨⟨j,bj⟩,hj⟩⟩ he
  change i.val+1=j.val+1 at he
  have hij : i=j := Fin.ext (by omega)
  subst j
  have hci := (hs c c.property).1
  have hcp := (hs c c.property).2
  have hdi := (hs d d.property).1
  have hdp := (hs d d.property).2
  have hmi := (divisible_signedPhysicalRoot_iff (p:=p) (c:=c.val) hci (by omega) (i,bi)).mp
    (Finset.mem_filter.mp (Finset.mem_filter.mp hi).1).2
  have hmj := (divisible_signedPhysicalRoot_iff (p:=p) (c:=d.val) hdi (by omega) (i,bj)).mp
    (Finset.mem_filter.mp (Finset.mem_filter.mp hj).1).2
  have hcd : c=d := by
    apply Subtype.ext
    cases bi <;> cases bj <;> simp only [Bool.false_eq_true, ↓reduceIte] at hmi hmj <;> omega
  subst d
  have hbb : bi=bj := by
    cases bi <;> cases bj <;> simp only [Bool.false_eq_true, ↓reduceIte] at hmi hmj ⊢ <;> omega
  subst bj
  rfl

theorem localFeatureNodes_low_card (J m p : ℕ) (hmJ : m≤J) (c : ℤ) :
    ((localFeatureNodes J p c).filter (fun i => i.1.val+1<m)).card =
      physicalLocalMultiplicity (m-1) p c := by
  symm
  unfold physicalLocalMultiplicity
  apply Finset.card_bij (fun i _ => (Fin.castLE (Nat.sub_le_sub_right hmJ 1) i.1,i.2))
  · intro i hi
    apply Finset.mem_filter.mpr
    refine ⟨?_,?_⟩
    · apply Finset.mem_filter.mpr
      exact ⟨Finset.mem_univ _, (Finset.mem_filter.mp hi).2⟩
    · have := i.1.isLt
      simp only [Fin.coe_castLE]
      omega
  · intro i hi j hj he
    apply Prod.ext
    · apply Fin.ext
      exact congrArg (fun x : Fin (J-1)×Bool => x.1.val) he
    · exact congrArg (fun x : Fin (J-1)×Bool => x.2) he
  · intro i hi
    obtain ⟨hi,hlt⟩ := Finset.mem_filter.mp hi
    let j : Fin (m-1)×Bool := (⟨i.1.val,by omega⟩,i.2)
    refine ⟨j,?_,?_⟩
    · apply Finset.mem_filter.mpr
      exact ⟨Finset.mem_univ _, (Finset.mem_filter.mp hi).2⟩
    · apply Prod.ext
      · apply Fin.ext
        rfl
      · rfl

theorem freeLocalFeatureNodes_card (J m p : ℕ) (hmJ : m≤J) (c : ℤ) :
    (freeLocalFeatureNodes J m p c).card =
      physicalLocalMultiplicity (J-1) p c - physicalLocalMultiplicity (m-1) p c := by
  have h := Finset.card_filter_add_card_filter_not (s:=localFeatureNodes J p c)
    (p:=fun i => i.1.val+1<m)
  rw [localFeatureNodes_low_card J m p hmJ c] at h
  have he : ((localFeatureNodes J p c).filter (fun i => ¬i.1.val+1<m)) =
      freeLocalFeatureNodes J m p c := by simp only [freeLocalFeatureNodes, not_lt]
  rw [he] at h
  change physicalLocalMultiplicity (m-1) p c + (freeLocalFeatureNodes J m p c).card =
    physicalLocalMultiplicity (J-1) p c at h
  omega

theorem featureNodeLevel_injective (J : ℕ) (c : ℤ) (hsmall : 2*(J-1)<p^2) :
    Function.Injective (fun i : localFeatureNodes J p c =>
      (physicalLocalLevel p c i.val : PadicResidueField p)) := by
  letI := residueField_charP (p:=p)
  intro i j h
  apply Subtype.ext
  by_contra hne
  have hd := physicalLocalLevel_unit_differences (p:=p) c hsmall
    i.val i.property j.val j.property hne
  apply hd
  apply (CharP.intCast_eq_zero_iff (PadicResidueField p) p _).mp
  simpa only [Int.cast_sub, h, sub_self]

theorem centralLocal_eval_level (j J : ℕ) (c : ℤ)
    (i : Fin (J-1)×Bool) (hi : i∈localFeatureNodes J p c) :
    (centralLocal p j c).eval (physicalLocalLevel p c i : ℚ) =
      (centralPolynomial j).eval (((i.1.val+1:ℕ):ℚ)^2) := by
  simp only [centralLocal, eval_comp, eval_pow, localAffine, eval_add, eval_C, eval_mul, eval_X]
  rw [physicalLocalLevel_reconstruct hi]
  rcases i with ⟨i,b⟩
  cases b <;> simp [signedPhysicalRoot]
  congr 1
  ring

theorem reducedCentralLocal_eval_level_zero (hp2 : p≠2) (j J : ℕ)
    (hsmall : 2*j<p^2) (c : ℤ) (i : Fin (J-1)×Bool)
    (hi : i∈localFeatureNodes J p c) (hij : i.1.val+1<j) :
    (reducedCentralLocal hp2 j hsmall c).eval
      (physicalLocalLevel p c i : PadicResidueField p)=0 := by
  rw [reducedCentralLocal,reducePolynomial_eval_int,padicReduction_eq_zero]
  left
  change (centralLocal p j c).eval (physicalLocalLevel p c i : ℚ)=0
  rw [centralLocal_eval_level j J c i hi]
  exact centralPolynomial_eval_square_eq_zero hij

theorem reducedCentralLocal_eval_level_self_ne_zero (hp2 : p≠2) (J : ℕ)
    (c : ℤ) (i : Fin (J-1)×Bool) (hi : i∈localFeatureNodes J p c)
    (hsmall : 2*(i.1.val+1)<p^2) :
    (reducedCentralLocal hp2 (i.1.val+1) hsmall c).eval
      (physicalLocalLevel p c i : PadicResidueField p)≠0 := by
  rw [reducedCentralLocal,reducePolynomial_eval_int]
  intro hz
  have hh := (padicReduction_eq_zero _).mp hz
  have hval : 2*(centralLocal p (i.1.val+1) c).eval (physicalLocalLevel p c i : ℚ)=1 := by
    rw [centralLocal_eval_level (i.1.val+1) J c i hi]
    simpa only [centralStar, if_neg (by omega : i.1.val+1≠0), eval_mul, eval_C] using
      centralStar_eval_square_self (i.1.val+1)
  have h1 : PadicLower p 1 (2*(centralLocal p (i.1.val+1) c).eval (physicalLocalLevel p c i : ℚ)) :=
    by simpa using (padicLower_nat (p:=p) 2).mul hh
  rw [hval] at h1
  norm_num [PadicLower] at h1

end Zeta3.Construction.Features

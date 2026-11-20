import Zeta3.Arithmetic.FeatureRankEnvelope
import Zeta3.Arithmetic.AffineCertificate

/-! The actual discrete feature envelope, expressed at the limiting prime
ratio beta=p/N. These identities precede any finite cell certificate. -/
noncomputable section
namespace Zeta3.Arithmetic
open Polynomial Finset Matrix Module OddZeta.FourValue Zeta5.Construction
open Zeta5.Arithmetic Zeta3.Construction.Features

def profileWidth (q e : ℕ) (β : ℝ) : ℝ := 1-((q:ℝ)+(e:ℝ)/2)*β

def profileRootCount (q e a : ℕ) (s β : ℝ) : ℝ :=
  if e=0 then rootPrefixProfile a (s-(a:ℝ)*β) (profileWidth q e β) β
  else rootPrefixProfile a (s-(a:ℝ)*β) (β/2) β -
    rootPrefixProfile a (s-(a:ℝ)*β) (β/2-profileWidth q e β) β

def featureShape (q e D a : ℕ) (s ρ β : ℝ) : ℝ :=
  (D:ℝ)*profileWidth q e β-profileRootCount q e a s β+
    min (ρ-(D:ℝ)*β/2) (profileWidth q e β)

theorem rootPrefixProfile_scale (q : ℕ) (s x P t : ℝ) (ht : 0≤t) :
    rootPrefixProfile q (t*s) (t*x) (t*P)=t*rootPrefixProfile q s x P := by
  unfold rootPrefixProfile
  rw [show t*x+t*s-t*P=t*(x+s-P) by ring,
    ← mul_min_of_nonneg x s ht, ← mul_zero t, ← mul_max_of_nonneg 0 (x+s-P) ht]
  ring

theorem floor_ratio_nat (N k p : ℕ) (hN : 0<N) :
    ⌊((k:ℝ)/N)/((p:ℝ)/N)⌋₊=k/p := by
  rw [div_div_div_cancel_right₀ (by exact_mod_cast hN.ne' : (N:ℝ)≠0),
    Nat.floor_div_natCast,Nat.floor_natCast]

variable {p : ℕ} [Fact p.Prime]

theorem maximalWidth_scaled (N q e : ℕ) (hN : 0<N)
    (hq : N/p=q) (he : 2*(N%p)/p=e) :
    maximalWidth N p=(N:ℝ)*profileWidth q e ((p:ℝ)/N) := by
  have hN0 : (N:ℝ)≠0 := by exact_mod_cast hN.ne'
  have hd : ((N%p:ℕ):ℝ)+(p:ℝ)*q=N := by
    have hh := Nat.mod_add_div N p
    rw [hq] at hh
    exact_mod_cast hh
  unfold maximalWidth profileWidth
  rw [he]
  field_simp
  nlinarith

theorem maximalOldRootProfile_scaled (N m q e a : ℕ) (hN : 0<N)
    (hq : N/p=q) (he : 2*(N%p)/p=e) (ha : m/p=a) :
    maximalOldRootProfile N m p=(N:ℝ)*profileRootCount q e a ((m:ℝ)/N) ((p:ℝ)/N) := by
  have hp := (Fact.out : p.Prime).pos
  have hN0 : (N:ℝ)≠0 := by exact_mod_cast hN.ne'
  have hNr : (0:ℝ)≤N := Nat.cast_nonneg _
  have hmd : ((m%p:ℕ):ℝ)+(p:ℝ)*a=m := by
    have hh := Nat.mod_add_div m p
    rw [ha] at hh
    exact_mod_cast hh
  have hrem : ((m%p:ℕ):ℝ)=(N:ℝ)*((m:ℝ)/N-(a:ℝ)*((p:ℝ)/N)) := by field_simp; nlinarith
  have hpval : (p:ℝ)=(N:ℝ)*((p:ℝ)/N) := by field_simp
  have hw := maximalWidth_scaled N q e hN hq he
  by_cases hσ : 2*(N%p)<p
  · have he0 : e=0 := by rw [reflected_epsilon N p hp,if_pos hσ] at he; omega
    rw [he0] at hw ⊢
    have hs : ((N%p:ℕ):ℝ)=(N:ℝ)*profileWidth q 0 ((p:ℝ)/N) := by
      simpa only [maximalWidth,reflected_epsilon N p hp,if_pos hσ,Nat.cast_zero,zero_mul,zero_div,sub_zero] using hw
    rw [maximalOldRootProfile,if_pos hσ,profileRootCount,if_pos rfl,ha]
    calc
      _ = rootPrefixProfile a
          ((N:ℝ)*((m:ℝ)/N-(a:ℝ)*((p:ℝ)/N)))
          ((N:ℝ)*profileWidth q 0 ((p:ℝ)/N)) ((N:ℝ)*((p:ℝ)/N)) := by
        congr 1
      _ = _ := rootPrefixProfile_scale _ _ _ _ _ hNr
  · have he1 : e=1 := by rw [reflected_epsilon N p hp,if_neg hσ] at he; omega
    rw [he1] at hw ⊢
    have hs : (p:ℝ)-((N%p:ℕ):ℝ)=(N:ℝ)*(((p:ℝ)/N)/2-profileWidth q 1 ((p:ℝ)/N)) := by
      simp only [maximalWidth,reflected_epsilon N p hp,if_neg hσ,Nat.cast_one,one_mul] at hw
      field_simp
      nlinarith
    have hhalf : (p:ℝ)/2=(N:ℝ)*(((p:ℝ)/N)/2) := by field_simp
    rw [maximalOldRootProfile,if_neg hσ,profileRootCount,if_neg (by decide : ¬(1:ℕ)=0),ha,mul_sub]
    congr 1
    · calc
        _ = rootPrefixProfile a
            ((N:ℝ)*((m:ℝ)/N-(a:ℝ)*((p:ℝ)/N)))
            ((N:ℝ)*(((p:ℝ)/N)/2)) ((N:ℝ)*((p:ℝ)/N)) := by
          congr 1
        _ = _ := rootPrefixProfile_scale _ _ _ _ _ hNr
    · calc
        _ = rootPrefixProfile a
            ((N:ℝ)*((m:ℝ)/N-(a:ℝ)*((p:ℝ)/N)))
            ((N:ℝ)*(((p:ℝ)/N)/2-profileWidth q 1 ((p:ℝ)/N))) ((N:ℝ)*((p:ℝ)/N)) := by
          congr 1
        _ = _ := rootPrefixProfile_scale _ _ _ _ _ hNr

theorem featureRankProfile_scaled (N m r q e D a : ℕ) (hN : 0<N)
    (hq : N/p=q) (he : 2*(N%p)/p=e)
    (hD : 2*(m+r)/p=D) (ha : m/p=a) :
    featureRankProfile N m r p=(N:ℝ)*featureShape q e D a ((m:ℝ)/N) (((m+r:ℕ):ℝ)/N) ((p:ℝ)/N) := by
  have hN0 : (N:ℝ)≠0 := by exact_mod_cast hN.ne'
  have hH : ((m+r:ℕ):ℝ)-(D:ℝ)*(p:ℝ)/2 =
      (N:ℝ)*(((m+r:ℕ):ℝ)/N-(D:ℝ)*((p:ℝ)/N)/2) := by field_simp <;> ring
  rw [featureRankProfile,hD,maximalWidth_scaled N q e hN hq he,
    maximalOldRootProfile_scaled N m q e a hN hq he ha,hH,
    ← mul_min_of_nonneg _ _ (show (0:ℝ)≤N from Nat.cast_nonneg _)]
  unfold featureShape
  ring

end Zeta3.Arithmetic

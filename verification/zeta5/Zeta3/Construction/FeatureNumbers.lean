import Zeta3.Construction.FeatureCentral

/-! Exact endpoints and dimensions of the two bands of local features. -/

namespace Zeta3.Construction.Features
open Zeta5.Arithmetic

def featureStart (m r p : ℕ) : ℕ := (restrictionDepth m r p * p + 1)/2
def featureTopCount (m r p : ℕ) : ℕ := m+r-featureStart m r p
def featureLowCount (N m r p : ℕ) : ℕ :=
  ∑ c ∈ maximalReflectedClasses N p,
    (restrictionDepth m r p - physicalLocalMultiplicity (m-1) p c)
def featureRankBound (N m r p : ℕ) : ℕ :=
  featureLowCount N m r p + min (featureTopCount m r p) (maximalReflectedClasses N p).card
def featureTopKernel (N m r p : ℕ) : ℕ :=
  featureTopCount m r p - (maximalReflectedClasses N p).card

theorem featureStart_twice_lower (m r p : ℕ) :
    restrictionDepth m r p * p ≤ 2*featureStart m r p := by
  unfold featureStart
  omega

theorem featureStart_twice_upper (m r p : ℕ) :
    2*featureStart m r p ≤ restrictionDepth m r p * p + 1 := by
  unfold featureStart
  omega

theorem featureStart_le (m r p : ℕ) (hmr : 0<m+r) : featureStart m r p ≤ m+r-1 := by
  have hmul := Nat.div_mul_le_self (2*(m+r)-2) p
  unfold featureStart restrictionDepth
  omega

theorem feature_low_depth (m r p j : ℕ) (hp : 0<p) (hj : j<featureStart m r p) :
    (2*j)/p < restrictionDepth m r p := by
  apply (Nat.div_lt_iff_lt_mul hp).mpr
  have h := featureStart_twice_upper m r p
  omega

theorem feature_high_depth (m r p j : ℕ) (hp : 0<p)
    (hj : featureStart m r p ≤ j) (hjr : j<m+r) :
    (2*j)/p = restrictionDepth m r p := by
  apply Nat.div_eq_of_lt_le
  · have hl := featureStart_twice_lower m r p
    omega
  · have hu := Nat.lt_mul_div_succ (2*(m+r)-2) hp
    have hu' : 2*(m+r)-2 < (restrictionDepth m r p + 1)*p := by
      simpa only [restrictionDepth, Nat.mul_comm] using hu
    omega

theorem not_dvd_between_multiples (p D a : ℕ) (hp : 0<p)
    (hlo : D*p<a) (hhi : a<(D+1)*p) : ¬p∣a := by
  rintro ⟨b,rfl⟩
  have hb : D<b := by nlinarith
  have hb' : b<D+1 := by nlinarith
  omega

theorem feature_high_denominator_unit (m r p j : ℕ) (hp : p.Prime)
    (hj : featureStart m r p ≤ j) (hjr : j+1<m+r) :
    ¬p ∣ (2*j+2)*(2*j+1) := by
  intro hd
  have hlo := featureStart_twice_lower m r p
  have hhi := Nat.lt_mul_div_succ (2*(m+r)-2) hp.pos
  have hhi' : 2*(m+r)-2 < (restrictionDepth m r p+1)*p := by
    simpa only [restrictionDepth, Nat.mul_comm] using hhi
  rcases hp.dvd_mul.mp hd with h | h
  · exact not_dvd_between_multiples p (restrictionDepth m r p) (2*j+2) hp.pos
      (by omega) (by omega) h
  · exact not_dvd_between_multiples p (restrictionDepth m r p) (2*j+1) hp.pos
      (by omega) (by omega) h

theorem halfBoundary_even (b p : ℕ) : ((2*b)*p+1)/2 = b*p := by
  rw [show (2*b)*p+1=2*(b*p)+1 by ring]
  omega

theorem halfBoundary_odd (b p : ℕ) : ((2*b+1)*p+1)/2 = b*p+(p+1)/2 := by
  rw [show (2*b+1)*p+1=2*(b*p)+(p+1) by ring]
  omega

theorem reflectedSize_halfBoundary (D p c : ℕ) (hp : p%2=1)
    (hc : 0<c) (hcp : 2*c<p) :
    reflectedSize (((D*p+1)/2)-1) p c = D := by
  have hp0 : 0<p := by omega
  rcases Nat.even_or_odd D with he | ho
  · obtain ⟨b,hb⟩ := he
    have hD : D=2*b := by omega
    rw [hD, halfBoundary_even]
    by_cases hb0 : b=0
    · subst b
      simp [reflectedSize, hc.ne', show p-c≠0 by omega]
    · have hbp : b*p-1=(b-1)*p+(p-1) := by
        have hb1 : b-1+1=b := by omega
        have hp1 : p-1+1=p := by omega
        have hbp1 : b*p-1+1=b*p := Nat.sub_add_cancel
          (Nat.succ_le_of_lt (Nat.mul_pos (Nat.pos_of_ne_zero hb0) hp0))
        nlinarith
      have hmod : (b*p-1)%p=p-1 := by rw [hbp]; simp [Nat.mod_eq_of_lt (by omega : p-1<p)]
      have hdiv : (b*p-1)/p=b-1 := by
        rw [hbp, Nat.add_div hp0]
        simp [Nat.div_eq_of_lt (by omega : p-1<p), Nat.mod_eq_of_lt (by omega : p-1<p), hp0,
          show ¬p≤p-1 by omega]
      simp only [reflectedSize, hmod, hdiv]
      rw [if_pos (by omega : c≤p-1), if_pos (by omega : p-c≤p-1)]
      omega
  · obtain ⟨b,hb⟩ := ho
    rw [hb, halfBoundary_odd]
    have hbp : b*p+(p+1)/2-1=b*p+(p-1)/2 := by omega
    have hmod : (b*p+(p-1)/2)%p=(p-1)/2 := by
      simp [Nat.mod_eq_of_lt (by omega : (p-1)/2<p)]
    have hdiv : (b*p+(p-1)/2)/p=b := by
      rw [Nat.add_div hp0]
      simp [Nat.div_eq_of_lt (by omega : (p-1)/2<p), Nat.mod_eq_of_lt (by omega : (p-1)/2<p), hp0,
        show ¬p≤(p-1)/2 by omega]
    rw [hbp]
    simp only [reflectedSize, hmod, hdiv]
    rw [if_pos (by omega : c≤(p-1)/2), if_neg (by omega : ¬p-c≤(p-1)/2)]
    omega

end Zeta3.Construction.Features

import Zeta3.Analysis.ContourRiemann
import Zeta3.Analysis.DeterminantMajorant

/-! Finite spectral products are controlled by the actual response integral.
This proof keeps the endpoint and polynomial-factor errors explicit. -/

noncomputable section
namespace Zeta3.Analysis
open Real Set Finset MeasureTheory
open scoped BigOperators

theorem sum_pairs (f : ℕ→ℝ) (m : ℕ) :
    (∑ j∈range (2*m),f (j/2))=2*∑ k∈range m,f k := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [show 2*(m+1)=2*m+1+1 by omega,Finset.sum_range_succ,Finset.sum_range_succ,
      Finset.sum_range_succ,ih]
    rw [show (2*m+1)/2=m by omega,show (2*m)/2=m by omega]
    ring

theorem sum_clamped_pairs (f : ℕ→ℝ) (r m : ℕ) (hmr : 2*m≤r) :
    (∑ j∈range r,f (min (j/2) m))=
      2*(∑ k∈range m,f k)+(r-2*m:ℕ)*f m := by
  obtain ⟨k,hk⟩ := Nat.exists_eq_add_of_le hmr
  subst r
  rw [Finset.sum_range_add]
  have hfirst : (∑ j∈range (2*m),f (min (j/2) m))=2*∑ j∈range m,f j := by
    have he : (∑ j∈range (2*m),f (min (j/2) m))=∑ j∈range (2*m),f (j/2) := by
      apply Finset.sum_congr rfl
      intro j hj
      rw [min_eq_left (by have:=Finset.mem_range.mp hj; omega)]
    rw [he,sum_pairs]
  have htail : (∑ j∈range k,f (min ((2*m+j)/2) m))=(k:ℝ)*f m := by
    have he : ∀ j, min ((2*m+j)/2) m=m := by intro j; omega
    simp only [he,Finset.sum_const,Finset.card_range,nsmul_eq_mul]
  rw [hfirst,htail]
  simp

theorem log_one_add_spectral_factor_le {u eig D N a b : ℝ}
    (hu : 0≤u) (heig : 0≤eig) (hD : 0≤D) (hN : 0≤N) (hab : a≤b)
    (hur : u≤Real.exp (-a*N)) (heigb : eig≤D*Real.exp (N*b)) :
    Real.log (1+u*eig)≤Real.log (1+D)+N*(b-a) := by
  have hb : 0≤N*(b-a) := mul_nonneg hN (sub_nonneg.mpr hab)
  have hexp : 1≤Real.exp (N*(b-a)) := Real.one_le_exp_iff.mpr hb
  have hmul : u*eig≤D*Real.exp (N*(b-a)) := by
    calc
      u*eig ≤ Real.exp (-a*N)*(D*Real.exp (N*b)) :=
        mul_le_mul hur heigb heig (Real.exp_pos _).le
      _ = D*Real.exp (N*(b-a)) := by
        rw [mul_left_comm,← Real.exp_add]
        congr 1
        ring
  have hbig : 1+u*eig≤(1+D)*Real.exp (N*(b-a)) := by nlinarith
  have h := Real.log_le_log (by positivity : 0<1+u*eig) hbig
  rw [Real.log_mul (by positivity) (Real.exp_ne_zero _),Real.log_exp] at h
  exact h

theorem antitone_profile_left_sum_bound (g : ℝ→ℝ) (T N : ℝ) (m : ℕ)
    (hN : 0<N) (hT : 0≤T) (hm : 2*(m:ℝ)/N≤T)
    (hg : AntitoneOn g (Icc 0 T)) :
    (2/N)*(∑ k∈range m,(g (2*(k:ℝ)/N)-g T)) ≤
      (∫ t in 0..T,g t-g T)+(2/N)*(g 0-g T) := by
  let f : ℝ→ℝ := fun t => g t-g T
  have hf : AntitoneOn f (Icc 0 T) := fun x hx y hy hxy => sub_le_sub_right (hg hx hy hxy) _
  have hh : 0≤2/N := by positivity
  have hlen : (2/N)*(m:ℝ)=2*(m:ℝ)/N := by ring
  have hmono : AntitoneOn f (Icc 0 ((2/N)*(m:ℝ))) := by
    apply hf.mono
    exact Icc_subset_Icc le_rfl (by rw [hlen];exact hm)
  have hzero : MonotoneOn (fun _ : ℝ => (0:ℝ)) (Icc 0 ((2/N)*(m:ℝ))) :=
    fun _ _ _ _ _ => le_rfl
  have hleft := left_sum_add_le_integral (g:=f) (k:=fun _ => (0:ℝ)) hh m hmono hzero
  simp only [add_zero,hlen] at hleft
  have hfn : 0≤f (2*(m:ℝ)/N) := by
    exact sub_nonneg.mpr (hg ⟨by positivity,hm⟩ ⟨hT,le_rfl⟩ hm)
  have hfi : IntervalIntegrable f volume 0 T := by
    apply AntitoneOn.intervalIntegrable
    simpa only [uIcc_of_le hT] using hf
  have hfm : 0≤ᵐ[volume.restrict (Ioc 0 T)] f := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    exact sub_nonneg.mpr (hg ⟨ht.1.le,ht.2⟩ ⟨hT,le_rfl⟩ ht.2)
  have hint := intervalIntegral.integral_mono_interval (a:=0) (b:=2*(m:ℝ)/N)
    (c:=0) (d:=T) le_rfl (by positivity) hm hfm hfi
  have he : (∑ k∈range m,f ((2/N)*(k:ℝ)))=
      ∑ k∈range m,(g (2*(k:ℝ)/N)-g T) := by
    apply Finset.sum_congr rfl
    intro k hk
    dsimp [f]
    congr 2
    ring
  rw [he] at hleft
  dsimp only [f] at hleft hfn hint
  nlinarith

/-- Every two consecutive eigenvalues cost one profile sample. The tail is
kept as an explicit nonnegative endpoint error. -/
theorem spectral_log_product_le (g : ℝ→ℝ) (T N D u : ℝ) (r m : ℕ)
    (hN : 0<N) (hT : 0≤T) (hD : 0≤D) (hu : 0≤u)
    (hmr : 2*m<r) (hm : 2*(m:ℝ)/N≤T)
    (hg : AntitoneOn g (Icc 0 T)) (hur : u≤Real.exp (-g T*N))
    (eig : Fin r→ℝ) (heig : ∀ j,0≤eig j) (hanti : Antitone eig)
    (hbound : ∀ (k : ℕ) (hk : k≤m), eig ⟨2*k,by omega⟩≤D*Real.exp (N*g (2*(k:ℝ)/N))) :
    Real.log (∏ j:Fin r,(1+u*eig j)) ≤
      N^2*(∫ t in 0..T,g t-g T)+2*N*(g 0-g T)+(r:ℝ)*Real.log (1+D)+
        N*(r:ℝ)*(g (2*(m:ℝ)/N)-g T) := by
  let f : ℕ→ℝ := fun k => g (2*(k:ℝ)/N)-g T
  have hf (k : ℕ) (hk : k≤m) : 0≤f k := by
    have hkt : 2*(k:ℝ)/N≤T := by
      apply le_trans _ hm
      exact div_le_div_of_nonneg_right (by exact_mod_cast (show 2*k≤2*m by omega)) hN.le
    exact sub_nonneg.mpr (hg ⟨by positivity,hkt⟩ ⟨hT,le_rfl⟩ hkt)
  have hpoint (j : Fin r) : Real.log (1+u*eig j)≤Real.log (1+D)+N*f (min (j.val/2) m) := by
    let k := min (j.val/2) m
    have hkm : k≤m := min_le_right _ _
    have hkj : 2*k≤j.val := by dsimp [k];omega
    have hki : (⟨2*k,by omega⟩:Fin r)≤j := hkj
    have heigb := (hanti hki).trans (hbound k hkm)
    exact log_one_add_spectral_factor_le hu (heig j) hD hN.le
      (by have:=hf k hkm;dsimp[f] at this;linarith) hur heigb
  have hsum := Finset.sum_le_sum (fun j (_ : j ∈ (Finset.univ : Finset (Fin r))) => hpoint j)
  rw [Finset.sum_add_distrib,Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,
    ← Finset.mul_sum] at hsum
  have hgroup : (∑ j:Fin r,f (min (j.val/2) m))=
      2*(∑ k∈range m,f k)+(r-2*m:ℕ)*f m := by
    rw [Fin.sum_univ_eq_sum_range (fun j => f (min (j/2) m))]
    exact sum_clamped_pairs f r m hmr.le
  rw [hgroup] at hsum
  have htail : ((r-2*m:ℕ):ℝ)*f m≤(r:ℝ)*f m := by
    exact mul_le_mul_of_nonneg_right (by exact_mod_cast Nat.sub_le r (2*m)) (hf m le_rfl)
  have hgrid := antitone_profile_left_sum_bound g T N m hN hT hm hg
  have hgrid' := mul_le_mul_of_nonneg_left hgrid (sq_nonneg N)
  have hscale : N^2*((2/N)*(∑ k∈range m,f k))=2*N*(∑ k∈range m,f k) := by
    field_simp <;> ring
  have hscale' : N^2*((2/N)*(g 0-g T))=2*N*(g 0-g T) := by
    field_simp <;> ring
  change N^2*((2/N)*(∑ k∈range m,f k))≤_ at hgrid'
  rw [hscale,mul_add,hscale'] at hgrid'
  rw [Real.log_prod (fun j _ => (show 0<1+u*eig j by have:=heig j;positivity).ne')]
  dsimp only [f] at hsum htail hgrid'
  nlinarith

end Zeta3.Analysis

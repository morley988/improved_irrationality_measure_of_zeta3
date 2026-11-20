import Zeta3.Arithmetic.SecondTransportClosed
import Zeta3.Arithmetic.FeatureRankEnvelope
import Zeta3.Arithmetic.NormalizerLocalBounds

/-! The concrete stage uses the better of the proved first- and second-layer
prices. These are the actual finite feature/parity dimensions. -/
noncomputable section
namespace Zeta3.Arithmetic
open Polynomial Zeta5.Arithmetic Zeta5.Endpoint Zeta3.Construction
open Zeta3.Construction.Features OddZeta.FourValue
variable {p : ℕ} [Fact p.Prime]

def stageFirstFeaturePrice (n p : ℕ) : ℕ :=
  (2+2*((50*n)%p)/p)*(51*n)+
    min (featureRankBound (50*n) (4*n) (51*n) p)
      (featureRankBound (50*n) (16*n) (51*n) p)

def stageSecondFeaturePrice (n p : ℕ) : ℕ :=
  (1+2*((50*n)%p)/p)*(51*n)+
    featureRankBound (50*n) (4*n) (51*n) p+
    featureRankBound (50*n) (16*n) (51*n) p+
    secondRankBound (50*n) (4*n) (16*n) (51*n) p

def stageFeaturePrice (n p : ℕ) : ℕ :=
  min (stageFirstFeaturePrice n p) (stageSecondFeaturePrice n p)

theorem windowDeterminant_firstFeaturePrice (n : ℕ) (hn : 0<n) (hp : 2<p)
    (hstrong : 536*n+100<p^2) (hpr : p<102*n) :
    PolynomialPadicLower p (-(stageFirstFeaturePrice n p:ℤ)) (windowDeterminant n) := by
  have h := unscaledCentralPencil_feature_rank_bound (50*n) (4*n) (16*n) (51*n) hp
    (by omega) (by omega) (by omega) (by omega)
    (featureStart_ge_window (4*n) (51*n) hp (by omega))
    (featureStart_ge_window (16*n) (51*n) hp (by omega))
  change PolynomialPadicLower p _ (unscaledCentralPencil (50*n) (4*n) (16*n) (51*n)).det
  convert h using 1
  simp only [stageFirstFeaturePrice,Nat.cast_add,Nat.cast_mul,Nat.cast_ofNat,Nat.cast_min]
  ring

theorem windowDeterminant_secondFeaturePrice (n : ℕ) (hn : 0<n) (hp : 2<p)
    (hstrong : 536*n+100<p^2) (hpr : p<102*n) :
    PolynomialPadicLower p (-(stageSecondFeaturePrice n p:ℤ)) (windowDeterminant n) := by
  have h := unscaledCentralPencil_second_bound (50*n) (4*n) (16*n) (51*n) hp
    (by omega) (by omega) (by omega) (by omega)
    (featureStart_ge_window (4*n) (51*n) hp (by omega))
    (featureStart_ge_window (16*n) (51*n) hp (by omega))
  change PolynomialPadicLower p _ (unscaledCentralPencil (50*n) (4*n) (16*n) (51*n)).det
  convert h using 1
  simp only [stageSecondFeaturePrice,Nat.cast_add,Nat.cast_mul,Nat.cast_ofNat]
  ring

theorem windowDeterminant_stageFeaturePrice (n : ℕ) (hn : 0<n) (hp : 2<p)
    (hstrong : 536*n+100<p^2) (hpr : p<102*n) :
    PolynomialPadicLower p (-(stageFeaturePrice n p:ℤ)) (windowDeterminant n) := by
  by_cases h : stageFirstFeaturePrice n p≤stageSecondFeaturePrice n p
  · simpa only [stageFeaturePrice,min_eq_left h] using
      windowDeterminant_firstFeaturePrice n hn hp hstrong hpr
  · simpa only [stageFeaturePrice,min_eq_right (Nat.le_of_lt (Nat.lt_of_not_ge h))] using
      windowDeterminant_secondFeaturePrice n hn hp hstrong hpr

theorem windowNormalizer_stageFeaturePrice_bound (n : ℕ) (hn : 0<n) (hp : 2<p)
    (hstrong : 536*n+100<p^2) (hpr : p<102*n) :
    padicValRat p (windowNormalizer n)≤(stageFeaturePrice n p:ℤ) := by
  have h := primitiveNormalizer_padicVal_le (windowDeterminant n)
    (windowDeterminant_ne_zero n) p (-(stageFeaturePrice n p:ℤ))
    (windowDeterminant_stageFeaturePrice n hn hp hstrong hpr)
  simpa only [windowNormalizer,neg_neg] using h

end Zeta3.Arithmetic

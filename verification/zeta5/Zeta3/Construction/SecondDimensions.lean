import Zeta3.Construction.FeatureKernel
import Zeta3.Arithmetic.LocalParity

/-! The exact finite second-layer rank cap, with all four choices of
retaining the top feature directions. -/
noncomputable section
namespace Zeta3.Construction.Features
open Polynomial Finset Zeta5.Arithmetic

def nonmaximalReflectedClasses (N p : ℕ) : Finset ℕ :=
  Icc 1 ((p-1)/2) \ maximalReflectedClasses N p

def secondLocalFeatureCount (m r p c u : ℕ) : ℕ :=
  restrictionDepth m r p + u - physicalLocalMultiplicity (m-1) p c

def secondLocalRankCap (N m₁ m₂ r p c u₁ u₂ : ℕ) : ℕ :=
  let n₁ := secondLocalFeatureCount m₁ r p c u₁
  let n₂ := secondLocalFeatureCount m₂ r p c u₂
  if 2*(N%p)<p ∧ Even (physicalLocalMultiplicity (m₁-1) p c) ∧
      Even (physicalLocalMultiplicity (m₂-1) p c) then
    min ((n₁+1)/2) (n₂/2)+min (n₁/2) ((n₂+1)/2)
  else min n₁ n₂

def secondFeatureCost (N m₁ m₂ r p u₁ u₂ : ℕ) : ℕ :=
  (∑ c∈nonmaximalReflectedClasses N p,secondLocalRankCap N m₁ m₂ r p c u₁ u₂)+
    (1-u₁)*featureTopKernel N m₁ r p+(1-u₂)*featureTopKernel N m₂ r p

def secondRankBound (N m₁ m₂ r p : ℕ) : ℕ :=
  min (min (r-featureRankBound N m₁ r p) (r-featureRankBound N m₂ r p))
    (min (min (secondFeatureCost N m₁ m₂ r p 0 0) (secondFeatureCost N m₁ m₂ r p 0 1))
      (min (secondFeatureCost N m₁ m₂ r p 1 0) (secondFeatureCost N m₁ m₂ r p 1 1)))

end Zeta3.Construction.Features

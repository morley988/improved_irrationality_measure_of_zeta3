import Zeta3.Arithmetic.SecondProfileComparison
import Zeta3.Arithmetic.FullCellParameters
import Zeta3.Arithmetic.FullCellsData

/-! Axiom audit of the complete actual arithmetic-to-finite-profile bridge.
The finite data are not assumed valid by these theorems; their Boolean
validation is a separate explicit hybrid-certificate obligation. -/
#print axioms Zeta3.Arithmetic.featureRankBound_le_profile
#print axioms Zeta3.Arithmetic.secondFeatureCost_le_profile
#print axioms Zeta3.Arithmetic.stage_pairBucketLength_scaled
#print axioms Zeta3.Arithmetic.windowNormalizer_secondExpr_uniform
#print axioms Zeta3.Arithmetic.ProfileCertificate.Cell.full_expression_affine
#print axioms Zeta3.Arithmetic.ProfileCertificate.Cell.full_stage_restrictionDepth

import Zeta3.Transfer.Response
import Zeta3.Transfer.ConcreteMultiplicity

/-!
# Foundational audit for the generic quantitative transfer

The declarations below report their transitive axiom dependencies. They
should contain only the standard Lean/Mathlib foundations (`propext`,
`Classical.choice`, and `Quot.sound`), never `sorryAx` or a numerical oracle.
The response theorem remains conditional on its explicitly displayed
mathematical hypotheses for the chosen polynomial family.
-/

#print axioms Zeta3.Transfer.one_le_scaled_abs_hasse_eval
#print axioms Zeta3.Transfer.hasBoundedRationalJets_of_rootMultiplicity_le
#print axioms Zeta3.Transfer.eventually_cleared_jet_exponent_neg
#print axioms Zeta3.Transfer.norm_hasse_eval_le_of_sphere_bound
#print axioms Zeta3.Transfer.approximation_exponent_le_of_local_jets
#print axioms Zeta3.Transfer.approximation_exponent_le_of_local_polynomial_decay
#print axioms Zeta3.Transfer.approximation_exponent_le_of_response
#print axioms Zeta3.Transfer.HasApproximationExponentLE.irrational
#print axioms Zeta3.Transfer.HasApproximationExponentLE.not_liouvilleWith
#print axioms Zeta3.Transfer.normalizedPencil_isSymmetric
#print axioms Zeta3.Transfer.rootMultiplicity_realPencilDeterminant_eq_finrank_ker
#print axioms Zeta3.Transfer.rootMultiplicity_eq_finrank_ker_of_eval_eq_det
#print axioms Zeta3.Transfer.windowIntegerPolynomial_rootMultiplicity_eq_hankel_nullity
#print axioms Zeta3.Transfer.windowIntegerPolynomial_hasBoundedRationalJets

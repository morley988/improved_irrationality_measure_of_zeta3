import Zeta3.Certificate.ArithmeticFinite

/-!
# Explicit external exact-arithmetic assertion for the hybrid build

`arithmeticFiniteCheck` is a closed Boolean computation. It checks all
5,949 actual Lean cells, their rational coverage and area, their floor
guards and their piecewise-affine branch choices. The external command

  lake -f lakefile.zeta3.toml env lean --run zeta3_certificates/CheckFiniteProfile.lean

completed successfully on 2026-11-19. This module records that runtime
result as one EXPLICIT AXIOM. The runtime check is not a kernel proof;
no valuation, rank, integral, asymptotic, or irrationality assertion is
postulated. The soundness implication is a kernel-checked theorem.

This assertion can later be replaced by a kernel-checked reduction of the
same Boolean, without changing the mathematical argument or cell data.
-/

namespace Zeta3.Hybrid.ExternalArithmetic

axiom arithmeticFiniteCheck_eq_true : Zeta3.Certificate.arithmeticFiniteCheck=true

theorem finiteEvidence : Zeta3.Certificate.ArithmeticFiniteEvidence :=
  Zeta3.Certificate.arithmeticFiniteCheck_sound arithmeticFiniteCheck_eq_true

end Zeta3.Hybrid.ExternalArithmetic

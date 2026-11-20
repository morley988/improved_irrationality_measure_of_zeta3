# A new irrationality bound for ζ(3), via Pearson determinants

**Author:** Morley Davidson  
**Manuscript date:** 19 November 2026

We prove the upper bound

\[
\mu(\zeta(3)) \le \frac{2225439040605380000}{447428816560392051}<4.974
\]

using asymmetric factorial-window determinants, prime-adic divisibility estimates, and spectral estimates for perturbations of the determinant polynomials.

## Manuscript

- [`manuscript/zeta3_pearson_manuscript.pdf`](manuscript/zeta3_pearson_manuscript.pdf)
- [`manuscript/zeta3_pearson_manuscript.tex`](manuscript/zeta3_pearson_manuscript.tex)

The manuscript includes historical context, the mathematical argument, and a discussion of reproducibility and the hybrid Lean formalization.

## Verification and replay

The [Lean checkpoint](verification/README.txt) contains the Lean 4.33.1 project, its pinned dependency manifest, the finite witnesses, the checkers, the build logs and the axiom audits. The mathematical reduction is kernel-checked. The archived audit of the final theorem lists eight additional finite assumptions. Seven are interval inequalities checked with Arb, and the eighth is a Boolean evaluated by running the Lean arithmetic checker over 5,949 cells.

| Item | File |
| --- | --- |
| Final theorem | [Zeta3/Hybrid/Verified.lean](verification/zeta5/Zeta3/Hybrid/Verified.lean) |
| Mathematical implication from finite evidence | [Zeta3/Endpoint/FiniteEvidence.lean](verification/zeta5/Zeta3/Endpoint/FiniteEvidence.lean) |
| Recorded replay and environment | [report.json](verification/zeta5/zeta3_certificates/certificates/hybrid_validation/report.json) |
| Final theorem’s transitive axioms | [10_hybrid_trust_zero.log](verification/zeta5/zeta3_certificates/certificates/hybrid_validation/10_hybrid_trust_zero.log) |
| Checkpoint file sizes and SHA-256 hashes | [FILE_MANIFEST.json](verification/FILE_MANIFEST.json) |
| Paper’s numerical programs, certificates and calculation instructions | [Numerical supplement](numerical-supplement/README.md) |

To reproduce the Lean result, follow **REPRODUCING THE HYBRID RESULT** in [verification/README.txt](verification/README.txt), starting in `verification/zeta5/`. The directory name comes from the shared base project. The ζ(3) targets use `lakefile.zeta3.toml`. The pinned Lean toolchain, external dependencies and build caches are obtained during setup.

The recovered checkpoint is preserved file for file under `verification/`. The [numerical supplement](numerical-supplement/) preserves the earlier reproducibility release, including the paper as it was then. The revised publication source and PDF are in [manuscript/](manuscript/).

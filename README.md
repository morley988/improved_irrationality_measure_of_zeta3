# A new irrationality bound for ζ(3), via Pearson determinants

[![Lean build and hybrid verification](https://github.com/morley988/improved_irrationality_measure_of_zeta3/actions/workflows/verify.yml/badge.svg?branch=main)](https://github.com/morley988/improved_irrationality_measure_of_zeta3/actions/workflows/verify.yml)

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

**The full Lean build and hybrid verification passed** in [GitHub Actions run 44662517131](https://github.com/morley988/improved_irrationality_measure_of_zeta3/actions/runs/44662517131), testing commit [`00745a3`](https://github.com/morley988/improved_irrationality_measure_of_zeta3/commit/00745a3c3bbd3a813a0ddda181304ea9cbbdf101) with Lean 4.33.1.

- Full `Zeta5` and `Zeta3` library and endpoint build: **4,296 jobs completed successfully**.
- Archive integrity and dependency identity: **564 checkpoint file hashes and 14 pinned dependency revisions checked**.
- Certificate and verification-gate tests: **26 passed**.
- Fresh **256-bit Arb replay**, the **5,949-cell Lean arithmetic check**, and both **`--trust=0` axiom audits**: passed.

[Download the fresh audit results and build logs](https://github.com/morley988/improved_irrationality_measure_of_zeta3/actions/runs/44662517131/artifacts/14596823037). The archive includes `replay/report.json`, `replay/09_core_trust_zero.log`, `replay/10_hybrid_trust_zero.log`, and the fresh numerical witnesses. GitHub Actions artifacts have a 90-day retention period.

The [Lean checkpoint](verification/README.txt) contains the Lean 4.33.1 project, its pinned dependency manifest, the finite witnesses, the checkers, the build logs and the axiom audits. The mathematical reduction is kernel-checked. The fresh core audit reports only `propext`, `Classical.choice`, and `Quot.sound`. The final hybrid theorem adds exactly eight documented finite numerical assumptions, with no `sorryAx` dependency. Seven are interval inequalities checked with Arb, and the eighth is a Boolean evaluated by running the Lean arithmetic checker over 5,949 cells. This remains hybrid verification; the eight finite numerical assertions are not yet proved inside the Lean kernel.

| Item | File |
| --- | --- |
| Final theorem | [Zeta3/Hybrid/Verified.lean](verification/zeta5/Zeta3/Hybrid/Verified.lean) |
| Mathematical implication from finite evidence | [Zeta3/Endpoint/FiniteEvidence.lean](verification/zeta5/Zeta3/Endpoint/FiniteEvidence.lean) |
| Original archived replay and environment | [report.json](verification/zeta5/zeta3_certificates/certificates/hybrid_validation/report.json) |
| Original archived transitive axiom audit | [10_hybrid_trust_zero.log](verification/zeta5/zeta3_certificates/certificates/hybrid_validation/10_hybrid_trust_zero.log) |
| Checkpoint file sizes and SHA-256 hashes | [FILE_MANIFEST.json](verification/FILE_MANIFEST.json) |
| Paper’s numerical programs, certificates and calculation instructions | [Numerical supplement](numerical-supplement/README.md) |

To reproduce the Lean result, follow **REPRODUCING THE HYBRID RESULT** in [verification/README.txt](verification/README.txt), starting in `verification/zeta5/`. The directory name comes from the shared base project. The ζ(3) targets use `lakefile.zeta3.toml`. The pinned Lean toolchain, external dependencies and build caches are obtained during setup.

The recovered checkpoint files are preserved under `verification/`; the added `Zeta3.lean` entry file enables the full-library build. The [numerical supplement](numerical-supplement/) preserves the earlier reproducibility release, including the paper as it was then. The revised publication source and PDF are in [manuscript/](manuscript/).

# Pearson determinants: an irrationality-measure bound below five for zeta(3)

The accompanying research report proves, by an ordinary mathematical argument with numerical certificates,

\[
\mu(\zeta(3))\le
\frac{2225439040605380000}{447428816560392051}
=4.9738393197680857\ldots<4.974.
\]

The determinant uses the cubic Prévost-type positive functional and two unequal factorial windows:

- `s1 = 2/25`, `s2 = 8/25`, `delta = 51/50`;
- `N` runs through multiples of 50;
- determinant degree `(17/25)N + 1`;
- contour parameter `u = 1000001/1000000`;
- spectral cutoff `T = 17/125`, auxiliary cutoff `Tcap = 7/50`.

## Replay

From this directory, run:

```bash
python -m pip install -r requirements.txt
python verify.py
```

The install step can be omitted if the dependencies are already present. Do not run Python with `-O` or `-OO`: the proof checks use assertions, and the launcher explicitly rejects optimized execution.

The replay took approximately 30 seconds in the recorded environment. It writes fresh results to `replayed/`, preserving the reference certificates. SciPy only proposes root brackets; the interval checker validates each bracket before using it.

## Main certified inequalities

| Quantity | Directed bound |
| --- | ---: |
| Arithmetic cost | `<= 3.852564338452367898` |
| Analytic decay | `>= 4.813666930896` |
| Net small-value exponent | `>= 0.961102592443632102` |
| Integrated simple response | `<= 0.956420575565` |
| Response slack | `>= 0.004682016878632102` |
| Simple envelope at T | `[6.545408942519, 6.545408942957]` |

The full transfer formula, using the positive slack, gives the stated rational bound below 4.974. Discarding that slack gives the simpler strict bound below 5.

## Files

- `exact_arithmetic.py` integrates the cubic local valuation profile with exact rational floors and affine branch intersections. Its 6,752 cells are provided in `certificates/arithmetic_cells.tsv`.
- `certify_analytic.py` encloses the analytic quantities with directed interval arithmetic. The main theorem uses `Gamma(delta-t)+F(t)`. The script also records a stronger optional Green-function envelope explored during research; that additional envelope is not needed for the report's theorem.
- `verify.py` replays both calculations, independently checks the exact cell coverage and area roundings, and verifies the final rational comparison.
- `certificates/` contains the reference outputs and environment versions.
- `audits/` contains the separately prepared cubic arithmetic and nullity/transfer audits. Their chronological wording records the state of each audit when written; the final theorem and successful combined certificate are in the report and final JSON.
- `project_sources/` preserves the two earlier project sources that supplied the general framework. No zeta(5) irrationality theorem or measure bound is used as an assumption in the new zeta(3) theorem.
- `Pearson_Zeta3_Measure_4_974.tex` and `.pdf` are the complete report.

## Scope

The mathematical argument uses the positive functional identities, weighted polynomial estimates, local arithmetic, the prime number theorem, and the bounded-multiplicity transfer proved or explained in the report. The executable code certifies its finite numerical inequalities. A successful run does not replace those mathematical arguments. This result has not been externally refereed or formalized in Lean. The parameter choice is not claimed to be optimal.

The scalar functional is historically related to Prévost's remainder Padé approach. The improvement here comes from the growing asymmetric determinant, cubic local divisibility, and quantitative response compression. The public benchmark checked in the research was the October 2026 bound `mu(zeta(3)) < 5.4197` of Leibtag and coauthors.

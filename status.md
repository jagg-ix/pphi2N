# pphi2N Status

**4 sorries, 21 axioms, 41 files, 0 errors.**

## Main results

### Continuum limit (proved, 0 sorries)

| Theorem | File | Statement |
|---------|------|-----------|
| `lsmTorusLimit_satisfies_OS` | ONTorusLimit.lean | O(N) LSM continuum limit on T²_L satisfies OS0+OS1+OS2 |

### Mass gap (in progress)

The mass gap proof uses HS with imaginary coupling + steepest descent
contour rotation + Brascamp-Lieb. See `docs/mass-gap-v2.tex`.

| Result | File | Status |
|--------|------|--------|
| HS identity | HSIdentity.lean | **Proved** (from Mathlib `fourierIntegral_gaussian`) |
| Multi-site HS | MultiSiteHS.lean | **Proved** (product of 1-site identities) |
| Contour rotation lemmas | ContourRotation.lean | **Proved** (|exp(iθ)|=1, exponent real after rotation) |
| HS equivalence | Equivalence.lean | **1 sorry** (complex arithmetic, routine) |
| FK bound → mass gap | FKBound.lean | **Proved** (from FK axioms) |

### N=1 test case

| Result | File | Status |
|--------|------|--------|
| N=1 setup | N1Test.lean | HS identity, gap equation, connection to P(φ)₂ |

## Axioms (11)

### Continuum limit (4)

| Axiom | File | Proof source |
|-------|------|-------------|
| `nComponentGreen_uniform_bound` | EmbeddingBound.lean | Port from gaussian-field |
| `lsmDensityTransferConstant` | ONTorusLimit.lean | Nelson bound + Jensen |
| `lsmGF_latticeApproximation_error_vanishes` | ONTorusLimit.lean | Port from pphi2 |
| `nComponentGFF_exp_moment_uniform` | ONTorusLimit.lean | Gaussian MGF |

### Matrix calculus (3)

| Axiom | File | Proof source |
|-------|------|-------------|
| `contDiff_matrix_det` | MatrixCalculus.lean | Proved with Pi norm (DetContDiff.lean), axiom due to norm transfer |
| `fderiv_log_det` | MatrixCalculus.lean | Jacobi's formula (chain rule for det) |
| `hessian_log_det` | MatrixCalculus.lean | Second derivative of log det |

### Contour shift (2)

| Axiom | File | Proof source |
|-------|------|-------------|
| `rectangle_integral_vanishes` | ContourShift.lean | Mathlib `integral_boundary_rect_eq_zero` |
| `vertical_contour_shift` | ContourShift.lean | PNT project `HolomorphicOn.vanishesOnRectangle` |

### FK bound (2)

| Axiom | File | Proof source |
|-------|------|-------------|
| `green_function_monotone` | FKBound.lean | Spectral theorem for PSD matrices |
| `feynmanKac_subGaussian_bound` | FKBound.lean | FK representation + Borell sub-Gaussian |

## File inventory (32 files)

### Model (3 files, 0 axioms)
- Model/ONModel.lean — O(N) model structure
- Model/Interaction.lean — O(N)-invariant polynomial
- Model/LSM.lean — Linear Sigma Model parameters

### LatticeField (4 files, 0 axioms)
- LatticeField/NComponentField.lean — φ : Λ → ℝ^N
- LatticeField/ONGaussian.lean — Wick constant, rising factorial
- LatticeField/ProductGFF.lean — N-component GFF via Measure.pi
- LatticeField/ProductConfiguration.lean — Configuration isomorphism

### WickOrdering (1 file, 0 axioms)
- WickOrdering/ONWick.lean — Laguerre recursion, polynomial-in-N

### SigmaMeasure (1 file, 0 axioms)
- SigmaMeasure/Basic.lean — σ-field effective action

### InteractingMeasure (4 files, 0 axioms)
- ONLatticeAction.lean — O(N) interaction V(φ)
- ONTorusMeasure.lean — Boltzmann weight, probability measure, Nelson estimate
- LatticeTranslation.lean — V(T_v φ) = V(φ) via Fintype.sum_equiv
- DensityTransfer.lean — Cauchy-Schwarz density transfer

### ContinuumLimit (5 files, 4 axioms)
- NComponentTestFunction.lean — NTP test functions
- NComponentEmbedding.lean — Componentwise embedding
- EmbeddingBound.lean — Green's function bound (1 axiom)
- LSMTorusMeasure.lean — LSM measure, Wick constant (proved)
- ONTorusLimit.lean — OS0-OS2 (3 axioms)

### GeneralResults (3 files, 3 axioms)
- MatrixCalculus.lean — det/inv/log-det smoothness (3 axioms)
- DetContDiff.lean — det C∞ with Pi norm (proved)
- TraceFormula.lean — Tr(M·E_x·N·E_y) (proved)

### MassGap (4 files, 0 axioms)
- SigmaConcentration.lean — SigmaConvexityData, arithmetic
- HubbardStratonovich.lean — Pushforward σ-measure (proved)
- MassGapDef.lean — HasCorrelationDecay, HasSpectralGap
- LatticeOperator.lean — Graph Laplacian PSD (from Mathlib)

### HSEquivalence (7 files, 4 axioms, 1 sorry)
- HSIdentity.lean — HS Gaussian identity (proved from Mathlib)
- MultiSiteHS.lean — Per-site HS + boundedness (proved)
- ContourRotation.lean — Contour rotation lemmas (proved)
- ContourShift.lean — Rectangle + vertical shift (2 axioms)
- FKBound.lean — FK + Borell → mass gap (2 axioms, theorem proved)
- Equivalence.lean — Z_original = Z_HS (1 sorry)
- N1Test.lean — N=1 test case

## Proof plan (docs/mass-gap-v2.tex)

1. HS with imaginary coupling (exact, proved in HSIdentity)
2. Gap equation determines σ* and mass m₀ (standard in 2d)
3. Steepest descent contour rotation σ → iσ'
4. Brascamp-Lieb for the rotated (real, log-concave) measure
5. Renormalized Borell/FK bound with self-energy subtraction
6. N₀ ~ √(λ/g²) threshold

## References

- Kupiainen (1980a), "On the 1/n expansion" (NLSM) — `docs/Kupiainen1980.pdf`
- Kupiainen (1980b), "1/n expansion for a QFT model" (LSM) — `docs/Kupiainen1980b.pdf`
- Dario-Garban (2025), BKT for N=2 Φ⁴ — arXiv:2311.16546
- Brascamp-Lieb (1976), J. Funct. Anal. 22
- PNT project: github.com/AlexKontorovich/PrimeNumberTheoremAnd

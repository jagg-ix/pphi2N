# pphi2N Status

**0 sorries, 18 axioms, 42 files, 0 errors.**

See `docs/axiom_status.md` for detailed inventory of all axioms
with difficulty ratings and proof plans.

## Main results

### Continuum limit (proved, 0 sorries)

| Theorem | File | Statement |
|---------|------|-----------|
| `lsmTorusLimit_satisfies_OS` | ONTorusLimit.lean | O(N) LSM continuum limit on T²_L satisfies OS0+OS1+OS2 |

### Mass gap (proved from axioms)

**`ON_LSM_hasCorrelationDecay`** (`Thimble/MassGapProof.lean`):
The O(N) LSM interacting measure has `HasCorrelationDecay` with mass
m₀ > 0 from the gap equation, uniform in lattice volume.

Proved from `correlator_le_thimble_avg` + `green_exponential_decay`.
See `docs/mass-gap-v3.tex` (29 pages) and `docs/axiom_status.md`.

| Result | File | Status |
|--------|------|--------|
| HS identity | HSIdentity.lean | **Proved** (from Mathlib `fourierIntegral_gaussian`) |
| HS equivalence | Equivalence.lean | **Proved** (push_cast + ring) |
| Gap equation | Thimble/GapEquation.lean | **Proved** (v_* < 0, spectral gap) |
| Shifted operator | Thimble/ShiftedOperator.lean | **Proved** (M ≥ m₀²) |
| Phase cancellation | Thimble/QuantumThimble.lean | **Proved** (polar form) |
| 1D diamagnetic | Thimble/DiagmagneticInequality.lean | **Proved** (a ≤ ‖a+bi‖) |
| Green's function | Thimble/GreenDecay.lean | **15 theorems proved**, 1 axiom |
| FK decay chain | Thimble/FKBoundShifted.lean | **Proved** (from axioms) |
| **Mass gap** | Thimble/MassGapProof.lean | **Proved** (HasCorrelationDecay) |

### N=1 test case

| Result | File | Status |
|--------|------|--------|
| N=1 setup | N1Test.lean | HS identity, gap equation, connection to P(φ)₂ |

## Axioms (18)

See `docs/axiom_status.md` for detailed proof plans for each axiom.

### Used in the mass gap proof (2 axioms)

Only these 2 axioms are formal dependencies of `ON_LSM_hasCorrelationDecay`:

| Axiom | File | Content | Difficulty |
|-------|------|---------|------------|
| `correlator_le_thimble_avg` | MassGapProof.lean | HS+Cauchy+triangle→\|⟨φφ⟩\|≤E[G] | medium (plumbing) |
| `green_exponential_decay` | FKBoundShifted.lean | M⁻¹≤Ce^{-m₀\|x\|} (concrete operator) | medium |

### Supporting the mass gap axioms (1 axiom)

| Axiom | File | Content | Difficulty |
|-------|------|---------|------------|
| `greenFunction_exponential_decay` | GreenDecay.lean | ‖G(n)‖≤(1/m²)r₋^dist (1D torus) | medium |

### Infrastructure — not used in mass gap (15 axioms)

Note: `vertical_contour_shift` is now **PROVED** (was axiom).
Note: `quantum_thimble_exists` is trivially true as stated.

These are infrastructure for future proofs (diamagnetic inequality,
quantum thimble theory, continuum limit, matrix calculus). None are
formal dependencies of `ON_LSM_hasCorrelationDecay`.

| Axiom | File | Content | Difficulty |
|-------|------|---------|------------|
| `quantum_thimble_exists` | QuantumThimble.lean | QHJ solution + BL var (trivially true as stated) | — |
| `resolvent_complex_bound` | FKBoundShifted.lean | \|(M+iV)⁻¹\|≤M⁻¹ (diamagnetic) | medium |
| `heat_kernel_entrywise_nonneg` | DiagmagneticInequality | exp(-tM)≥0 | medium |
| `laplace_transform_inverse` | DiagmagneticInequality | M⁻¹=∫exp(-tM)dt | medium |
| `laplace_transform_inverse_complex` | DiagmagneticInequality | (M+iV)⁻¹=∫... | medium |
| `trotter_product_matrix` | DiagmagneticInequality | Lie-Trotter | medium |
| `diamagnetic_inequality` | DiagmagneticInequality | \|exp(-t(M+iV))\|≤exp(-tM) | medium |
| `m_matrix_inverse_nonneg` | DiagmagneticInequality | M⁻¹≥0 for M-matrix | easy |
| `nComponentGreen_uniform_bound` | EmbeddingBound.lean | Port from gaussian-field | easy |
| `lsmDensityTransferConstant` | ONTorusLimit.lean | Nelson bound + Jensen | easy |
| `lsmGF_latticeApproximation_error_vanishes` | ONTorusLimit.lean | Port from pphi2 | medium |
| `nComponentGFF_exp_moment_uniform` | ONTorusLimit.lean | Gaussian MGF | easy |
| `contDiff_matrix_det` | MatrixCalculus.lean | det is C∞ (norm transfer) | easy |
| `fderiv_log_det` | MatrixCalculus.lean | Jacobi's formula | medium |
| `hessian_log_det` | MatrixCalculus.lean | Hessian of log det | medium |

### Proved (no longer axioms)

| Former axiom | Status |
|-------------|--------|
| `rectangle_integral_vanishes` | **Proved** from Mathlib CauchyIntegral |
| `inverse_HS_one_site` | **Proved** (push_cast + ring) |
| `green_function_monotone` | **Removed** (deprecated) |
| `feynmanKac_subGaussian_bound` | **Removed** (deprecated) |
| `vertical_contour_shift` | **Proved** (rectangle + limits + decay) |
| `hs_partition_complex` | **Proved** (Fubini + inverse_HS_one_site) |
| `thimble_bound` | **Proved** (from correlator_le_thimble_avg + fk_bound) |

## File inventory (41 files)

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

### HSEquivalence (7 files, 0 axioms, 0 sorries)
- HSIdentity.lean — HS Gaussian identity (proved from Mathlib)
- MultiSiteHS.lean — Per-site HS + boundedness (proved)
- ContourRotation.lean — Contour rotation lemmas (proved)
- ContourShift.lean — Rectangle integral (**proved**), vertical shift (**proved**)
- FKBound.lean — Deprecated (superseded by Thimble/FKBoundShifted)
- Equivalence.lean — Z_original = Z_HS (**proved**, was sorry)
- N1Test.lean — N=1 test case

### Thimble (10 files, 12 axioms, 0 sorries)
- HSIntegral.lean — Multi-site HS identity (**proved** from Fubini + inverse_HS)
- GapEquation.lean — Gap equation algebra, v_* < 0 (proved)
- ShiftedOperator.lean — M = -Δ+m₀², spectral gap (proved)
- QuantumThimble.lean — Phase cancellation (proved), thimble existence (1 axiom)
- QuantumHJExplicit.lean — Total phase functional, 1/N correction (proved)
- FKBoundShifted.lean — Concrete FK + Green's decay (2 axioms)
- DiagmagneticInequality.lean — Semigroup proof structure (6 axioms, 0 sorries)
- GreenDecay.lean — Lattice Green's function (15 proved, 1 axiom)
- ThimbleMeasure.lean — BL variance (proved from quantum thimble)
- MassGapProof.lean — **ON_LSM_hasCorrelationDecay** (1 axiom)

## Proof plan (docs/mass-gap-v3.tex)

1. HS with imaginary coupling (exact, proved in HSIdentity)
2. Gap equation determines v_* and mass m₀ (proved in GapEquation)
3. Contour shift to quantum thimble (positive measure)
4. FK bound uniform in u (diamagnetic inequality)
5. Trivial averaging on positive measure (|⟨φφ⟩| ≤ G_M · Z/Z = G_M)
6. Green's function decay (G_M ≤ Ce^{-m₀|x|})
7. Mass gap m₀ > 0, uniform in |Λ|

## References

- Kupiainen (1980a), "On the 1/n expansion" (NLSM) — `docs/Kupiainen1980.pdf`
- Kupiainen (1980b), "1/n expansion for a QFT model" (LSM) — `docs/Kupiainen1980b.pdf`
- Dario-Garban (2025), BKT for N=2 Φ⁴ — arXiv:2311.16546
- Brascamp-Lieb (1976), J. Funct. Anal. 22
- PNT project: github.com/AlexKontorovich/PrimeNumberTheoremAnd

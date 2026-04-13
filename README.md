# pphi2N: O(N) P(φ)₂ Euclidean Quantum Field Theory

## What this project proves

Lean 4 formalization with 17 axioms, 0 sorries, 42 files.

### Theorem 1: Continuum limit with OS axioms

**`lsmTorusLimit_satisfies_OS`** (`ContinuumLimit/ONTorusLimit.lean`):
The O(N) Linear Sigma Model on the torus T²_L has a UV continuum limit
satisfying Osterwalder-Schrader axioms OS0 (analyticity), OS1 (regularity),
OS2 (translation invariance).

### Theorem 2: Mass gap at large N

**`ON_LSM_hasCorrelationDecay`** (`Thimble/MassGapProof.lean`):
The O(N) LSM interacting measure has exponential correlation decay
(`HasCorrelationDecay`) with mass m₀ > 0 from the gap equation,
uniform in the lattice volume.

Proved from 2 axioms:
- `contour_deformation` — HS + Cauchy + quantum HJ + FK bound
- `green_exponential_decay` — lattice Green's function decay

The proof uses the **Lefschetz thimble** / quantum Hamilton-Jacobi
approach. See `docs/mass-gap-v3.tex` (28 pages) for the full
mathematical argument and `status.md` for detailed inventory.

## Proof approach for the mass gap

### The Lefschetz thimble strategy

The mass gap proof uses a novel approach based on the quantum
Hamilton-Jacobi equation. The key insight: shifting the HS
auxiliary field σ into the complex plane by a constant v_*
(determined by the gap equation) introduces a real mass m₀²
into the φ-operator. On the quantum thimble (where the total
phase vanishes), the FK bound passes through the u-average
trivially (positive measure, ratio Z/Z = 1), giving
|⟨φ(x)φ(0)⟩| ≤ Ce^{-m₀|x|} uniformly in lattice volume.

### The Hubbard-Stratonovich transformation

The quartic interaction λ(|φ|²/N - ρ²)² is linearized by an auxiliary
field σ with **imaginary** coupling (the Euclidean sign requires this):

  exp(-λa²) = c ∫ dσ exp(-σ²/(4λ) + iσa)

This is the Fourier transform of the Gaussian — proved from Mathlib's
`fourierIntegral_gaussian` in `HSEquivalence/HSIdentity.lean`.

### Steepest descent contour rotation

The imaginary coupling creates a complex (oscillatory) σ-measure.
Rotating the contour σ → iσ' eliminates the oscillations:
- The Hessian flips from -B⁻¹ (saddle = maximum) to +B⁻¹ (saddle = minimum)
- The rotated measure is real, positive, and log-concave
- Brascamp-Lieb concentration applies

### Feynman-Kac bound

After contour rotation, each φ-component sees a **real** random
potential σ'. The sub-Gaussian bound (Borell's lemma for log-concave
measures) gives:

  E_σ'[(-Δ+m₀²+2σ'z)⁻¹(x,0)] ≤ (-Δ+m²)⁻¹(x,0)

with m² = m₀² - (renormalized correction) > 0 for N ≥ N₀.

### N = 1 test case

The N=1 case is the scalar P(φ)₂ theory, where the mass gap is already
proved (Glimm-Jaffe-Spencer 1974, formalized in pphi2). The HS
transformation rewrites the degree-4 polynomial as degree-2 coupled to σ.
This tests our machinery before applying it at large N.
See `HSEquivalence/N1Test.lean`.

### N = 2 obstruction

For N = 2, the BKT transition occurs at finite λ (Dario-Garban 2025),
so σ-concentration alone cannot cover N = 2. Our proof requires N ≥ 3.

## File structure

```
Pphi2N/
  Model/                    -- O(N) model, LSM parameters
  LatticeField/             -- N-component GFF, product measure
  WickOrdering/             -- Laguerre recursion, polynomial-in-N
  SigmaMeasure/             -- σ-field effective action
  InteractingMeasure/       -- Boltzmann weight, Nelson estimate, density transfer
  ContinuumLimit/           -- Torus embedding, OS0-OS2
  GeneralResults/           -- Matrix calculus (det, log det)
  MassGap/                  -- Definitions, Laplacian PSD, σ-concentration
  HSEquivalence/            -- HS identity, contour rotation, N=1 test
  Thimble/                  -- Lefschetz thimble mass gap proof
    GapEquation.lean        -- Gap equation, shift parameter v_*
    ShiftedOperator.lean    -- Operator -Δ+m₀²+2iuz, spectral gap
    QuantumThimble.lean     -- Quantum HJ, phase cancellation
    FKBoundShifted.lean     -- FK bound for concrete shifted operator
    GreenDecay.lean         -- Lattice Green's function decay
    DiagmagneticInequality.lean -- Semigroup proof of |e^{-t(M+iV)}| ≤ e^{-tM}
    ThimbleMeasure.lean     -- BL variance on the thimble
    MassGapProof.lean       -- Main theorem: HasCorrelationDecay
docs/
  mass-gap-v3.tex           -- Mass gap proof outline (28 pages)
  sign-problem.tex          -- Lefschetz thimbles and sign problems (10 pages)
  Kupiainen1980.pdf         -- "On the 1/n expansion" (NLSM)
  Kupiainen1980b.pdf        -- "1/n expansion for a QFT model" (LSM)
```

## Build

```bash
lake build
```

## Dependencies

- [pphi2](https://github.com/mrdouglasny/pphi2) — P(φ)₂ construction
- [markov-semigroups](https://github.com/mrdouglasny/markov-semigroups) — Brascamp-Lieb
- [gaussian-field](https://github.com/mrdouglasny/gaussian-field) — GFF infrastructure
- Mathlib v4.29

## References

- Kupiainen, Comm. Math. Phys. 73 (1980) 273–294
- Kupiainen, Comm. Math. Phys. 74 (1980) 199–222
- Brascamp-Lieb, J. Funct. Anal. 22 (1976) 366–389
- Dario-Garban, Comm. Math. Phys. (2025); arXiv:2311.16546
- Glimm-Jaffe-Spencer, Ann. Math. 100 (1974) 585–632

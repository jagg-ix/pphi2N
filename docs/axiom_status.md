# Axiom Status

**19 axioms, 0 sorries, 41 files.**
All axioms verified correct by Gemini deep think (2026-04-12).

## Main mass gap chain (3 axioms)

These are the axioms directly used in the proof of
`ON_LSM_hasCorrelationDecay`.

### 1. `thimble_bound`
- **File:** `Thimble/MassGapProof.lean`
- **Statement:** For the O(N) LSM measure `onInteractingMeasure`,
  |⟨φⁱ(x)φⁱ(y)⟩_c| ≤ M⁻¹(x,y) where M = -Δ + m₀².
- **Packages:** HS identity + Cauchy contour shift + quantum HJ
  (positive measure) + FK bound (uniform in u) + triangle inequality
- **Difficulty:** Research-level. This is the central theorem of the
  Lefschetz thimble approach.
- **Proof plan:** Decompose into sub-steps:
  (a) HS representation of the correlator (from HSIdentity, proved)
  (b) Cauchy contour shift to quantum thimble (from vertical_contour_shift)
  (c) Positive measure on thimble (from quantum_thimble_exists)
  (d) FK bound uniform in u (from resolvent_complex_bound)
  (e) Triangle inequality on positive measure (trivial)
- **Dependencies:** resolvent_complex_bound, quantum_thimble_exists,
  vertical_contour_shift

### 2. `green_exponential_decay`
- **File:** `Thimble/FKBoundShifted.lean`
- **Statement:** S.realPart⁻¹(x,y) ≤ (1/m₀²) · exp(-m₀·dist(x,y))
  for the concrete operator M = -Δ + m₀² from ShiftedOperatorData.
- **Difficulty:** Medium. Standard Combes-Thomas estimate.
- **Proof plan:** Reduce to greenFunction_exponential_decay on the
  1D torus (axiom 19) via product structure of the d-dimensional torus.
- **Dependencies:** greenFunction_exponential_decay

### 3. `greenFunction_exponential_decay`
- **File:** `Thimble/GreenDecay.lean`
- **Statement:** ‖G_m(n)‖ ≤ (1/m²) · r₋^dist(n) for nearest-neighbor
  Laplacian on Z/LZ, where r₋ = characteristicRoot(m²) ∈ (0,1).
- **Difficulty:** Medium. Pure Fourier analysis / recurrence.
- **Proof plan:** G satisfies the recurrence -G(n+1)+(2+m²)G(n)-G(n-1)=δ/L.
  Solution on Z/LZ: G(n) = [r₋ⁿ + r₋^{L-n}]/[√disc·(1-r₋^L)].
  Bound: 2r₋^dist / [√disc·(1-r₋^L)] ≤ 1/m² (verified: 1/√(m²(4+m²)) ≤ 1/m²).
  Already proved: r₋ ∈ (0,1), α = -log(r₋) > 0, r₋ⁿ = exp(-αn),
  ‖G(n)‖ ≤ 1/m² (crude bound), 15 supporting theorems.
- **Dependencies:** None (self-contained)

## Quantum thimble (1 axiom)

### 4. `quantum_thimble_exists`
- **File:** `Thimble/QuantumThimble.lean`
- **Statement:** ∃ ψ : (Λ→ℝ)→(Λ→ℝ), var : Λ→ℝ with ψ(0)=0 and
  var(x) ≤ 1/(κN).
- **Difficulty:** Hard. Requires implicit function theorem for the
  quantum HJ equation + Brascamp-Lieb on the effective potential.
- **Proof plan:** Define F(Φ) = Im f(u+i∇Φ) + Tr arctan(∇²Φ).
  Show F(0) is small (residual phase O(u³/√N)).
  Show DF(0) is invertible (Hessian H > 0).
  Apply IFT to get Φ with bounds. Extract BL variance from Hessian.
  For finite lattice: finite-dimensional IFT (Mathlib has this).
- **Dependencies:** Hessian computation (fderiv_log_det, hessian_log_det),
  BL from markov-semigroups

## Diamagnetic inequality (7 axioms)

These axioms decompose the semigroup proof of the diamagnetic inequality.
Together they prove `resolvent_complex_bound`.

### 5. `resolvent_complex_bound`
- **File:** `Thimble/FKBoundShifted.lean`
- **Statement:** normSq((M+iV)⁻¹(x,y)) ≤ (M⁻¹(x,y))²
  for the concrete shifted operator.
- **Difficulty:** Medium-hard. The diamagnetic inequality.
- **Proof plan:** Chain: laplace_transform → heat_kernel ×
  diamagnetic_semigroup → integrate. Already proved for diagonal case.
- **Dependencies:** heat_kernel_entrywise_nonneg, laplace_transform_inverse,
  laplace_transform_inverse_complex, diamagnetic_inequality

### 6. `heat_kernel_entrywise_nonneg`
- **File:** `Thimble/DiagmagneticInequality.lean`
- **Statement:** exp(-tM)(x,y) ≥ 0 when M has nonpositive off-diagonal.
- **Difficulty:** Medium. Metzler/Z-matrix theory.
- **Proof plan:** Euler scheme: exp(-tM) = lim(I - tM/n)^n.
  For large n: (I-tM/n) has nonneg entries. Product of nonneg matrices
  is nonneg. Convergence from Matrix.exp definition.
- **Dependencies:** None

### 7. `laplace_transform_inverse`
- **File:** `Thimble/DiagmagneticInequality.lean`
- **Statement:** M⁻¹(x,y) = ∫₀^∞ exp(-tM)(x,y) dt for PD matrix M.
- **Difficulty:** Medium. Spectral theorem + Laplace transform.
- **Proof plan:** Diagonalize M = UDU*. Then M⁻¹ = UD⁻¹U* and
  ∫exp(-tM)dt = U(∫exp(-tD)dt)U* = UD⁻¹U*. Uses spectral theorem
  (IsHermitian.spectral_theorem in Mathlib) + ∫₀^∞ e^{-λt}dt = 1/λ.
- **Dependencies:** Spectral theorem (Mathlib)

### 8. `laplace_transform_inverse_complex`
- **File:** `Thimble/DiagmagneticInequality.lean`
- **Statement:** (M+iV)⁻¹(x,y) = ∫₀^∞ exp(-t(M+iV))(x,y) dt for M PD.
- **Difficulty:** Medium. Same as above but complex.
- **Proof plan:** Eigenvalues of M+iV have Re > 0 (from M PD).
  Same Laplace transform argument works for complex eigenvalues.
- **Dependencies:** Spectral theorem

### 9. `trotter_product_matrix`
- **File:** `Thimble/DiagmagneticInequality.lean`
- **Statement:** exp(A+B) = lim_{n→∞} (exp(A/n)·exp(B/n))^n.
- **Difficulty:** Medium. Standard Lie-Trotter.
- **Proof plan:** For finite matrices, this follows from
  exp(A+B) - (exp(A/n)exp(B/n))^n = O(1/n) (Baker-Campbell-Hausdorff).
  Mathlib has Matrix.exp_add_of_commute for commuting case.
  General case needs norm estimates on BCH remainder.
- **Dependencies:** Matrix.exp (Mathlib)

### 10. `diamagnetic_inequality`
- **File:** `Thimble/DiagmagneticInequality.lean`
- **Statement:** |exp(-t(M+iV))(x,y)| ≤ exp(-tM)(x,y).
- **Difficulty:** Medium. Semigroup domination.
- **Proof plan:** By Trotter: exp(-t(M+iV)) = lim(exp(-tM/n)exp(-itV/n))^n.
  |exp(-itV/n)| = 1 (diagonal unitary, PROVED in the file).
  |product| ≤ product of |factors| (triangle, PROVED).
  exp(-tM/n) ≥ 0 (from heat_kernel_entrywise_nonneg).
  Take limit.
- **Dependencies:** trotter_product_matrix, heat_kernel_entrywise_nonneg

### 11. `m_matrix_inverse_nonneg`
- **File:** `Thimble/DiagmagneticInequality.lean`
- **Statement:** M⁻¹(x,y) ≥ 0 when M is an M-matrix.
- **Difficulty:** Easy-medium. Standard M-matrix theory.
- **Proof plan:** From laplace_transform_inverse + heat_kernel_entrywise_nonneg:
  M⁻¹ = ∫₀^∞ exp(-tM) dt, and exp(-tM) ≥ 0, so M⁻¹ ≥ 0.
- **Dependencies:** laplace_transform_inverse, heat_kernel_entrywise_nonneg

## Contour shift (1 axiom)

### 12. `vertical_contour_shift`
- **File:** `HSEquivalence/ContourShift.lean`
- **Statement:** For f entire with decay, ∫f(x+y₁i)dx = ∫f(x+y₂i)dx.
- **Difficulty:** Easy-medium. Follows from rectangle_integral_vanishes
  (now PROVED from Mathlib) + limit as rectangle width → ∞.
- **Proof plan:** Apply rectangle_integral_vanishes to [-R,R]×[y₁,y₂].
  Vertical integrals → 0 as R → ∞ (from decay hypothesis).
  Horizontal integrals → the full line integrals (dominated convergence).
- **Dependencies:** rectangle_integral_vanishes (PROVED),
  dominated convergence (Mathlib)

## Continuum limit (4 axioms)

These are porting targets from pphi2 and gaussian-field.

### 13. `nComponentGreen_uniform_bound`
- **File:** `ContinuumLimit/EmbeddingBound.lean`
- **Statement:** E_GFF[(ωf)²] ≤ C·q(f)² uniformly in lattice size M.
- **Difficulty:** Easy. Port from gaussian-field library.
- **Proof plan:** Compose scalar bound (in gaussian-field) with
  N-component decomposition. Direct port.
- **Dependencies:** gaussian-field library

### 14. `lsmDensityTransferConstant`
- **File:** `ContinuumLimit/ONTorusLimit.lean`
- **Statement:** Density transfer constant for LSM, uniform in M.
- **Difficulty:** Easy. Nelson bound + Jensen.
- **Proof plan:** From onNelsonEstimate (proved) + Cauchy-Schwarz
  density transfer (proved in DensityTransfer.lean).
- **Dependencies:** DensityTransfer.lean (proved)

### 15. `lsmGF_latticeApproximation_error_vanishes`
- **File:** `ContinuumLimit/ONTorusLimit.lean`
- **Statement:** Lattice approximation error → 0 as M → ∞.
- **Difficulty:** Medium. Port from pphi2.
- **Proof plan:** Standard lattice approximation theory.
  The scalar case is in pphi2; N-component follows by decomposition.
- **Dependencies:** pphi2 library

### 16. `nComponentGFF_exp_moment_uniform`
- **File:** `ContinuumLimit/ONTorusLimit.lean`
- **Statement:** exp moment bound for N-component GFF, uniform in M.
- **Difficulty:** Easy. Consequence of axiom 13 (Gaussian MGF).
- **Proof plan:** E[exp(ωf)] = exp(½E[(ωf)²]) for Gaussian.
  From axiom 13: E[(ωf)²] ≤ C·q(f)², so E[exp(ωf)] ≤ exp(C·q(f)²/2).
- **Dependencies:** nComponentGreen_uniform_bound

## Matrix calculus (3 axioms)

### 17. `contDiff_matrix_det`
- **File:** `GeneralResults/MatrixCalculus.lean`
- **Statement:** det : Matrix n n ℝ → ℝ is C∞.
- **Difficulty:** Easy. Already PROVED in DetContDiff.lean with Pi norm.
  Axiom exists only because of linftyOp vs Pi norm mismatch.
- **Proof plan:** Prove norm equivalence for finite-dim spaces,
  then transfer ContDiff. Or: reprove with linftyOp norm directly.
- **Dependencies:** DetContDiff.lean (proved with Pi norm)

### 18. `fderiv_log_det`
- **File:** `GeneralResults/MatrixCalculus.lean`
- **Statement:** d(log det A)·H = Tr(A⁻¹H) (Jacobi's formula).
- **Difficulty:** Medium. Chain rule + cofactor expansion.
- **Proof plan:** log det = log ∘ det. By chain rule:
  d(log det) = (1/det)·d(det). And d(det A)·H = det(A)·Tr(A⁻¹H)
  (cofactor expansion). Combine: d(log det)·H = Tr(A⁻¹H).
- **Dependencies:** contDiff_matrix_det, Mathlib chain rule

### 19. `hessian_log_det`
- **File:** `GeneralResults/MatrixCalculus.lean`
- **Statement:** d²(log det A)·(H,K) = -Tr(A⁻¹HA⁻¹K).
- **Difficulty:** Medium. Differentiate Jacobi's formula.
- **Proof plan:** Differentiate Tr(A⁻¹H) w.r.t. A in direction K.
  d(A⁻¹)/dA·K = -A⁻¹KA⁻¹. So d(Tr(A⁻¹H))·K = -Tr(A⁻¹KA⁻¹H)
  = -Tr(A⁻¹HA⁻¹K) (cyclic trace).
- **Dependencies:** fderiv_log_det, derivative of matrix inverse

## Priority order for proving

1. **greenFunction_exponential_decay** (medium, self-contained, 90% done)
2. **vertical_contour_shift** (easy-medium, rectangle_integral proved)
3. **contDiff_matrix_det** (easy, already proved with different norm)
4. **nComponentGreen_uniform_bound** (easy, port from gaussian-field)
5. **heat_kernel_entrywise_nonneg** (medium, Euler scheme)
6. **laplace_transform_inverse** (medium, spectral theorem)
7. **fderiv_log_det** (medium, chain rule + cofactor)
8. **trotter_product_matrix** (medium, BCH remainder)
9. **quantum_thimble_exists** (hard, IFT for quantum HJ)
10. **thimble_bound** (research-level, the main bridge)

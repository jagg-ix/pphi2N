# Axiom Status

**16 axioms, 0 sorries, 42 files.**
All axioms verified correct by Gemini deep think (2026-04-12).

Former axioms now proved:
- `vertical_contour_shift` → PROVED (rectangle + limits + decay)
- `rectangle_integral_vanishes` → PROVED (Mathlib CauchyIntegral)
- `hs_correlator_identity` → removed (content in correlator_le_thimble_avg)
- `thimble_bound` → PROVED (from correlator_le_thimble_avg + fk_bound)
- `inverse_HS_one_site` → PROVED (push_cast + ring)
- `hs_partition_complex` → PROVED (Fubini + inverse_HS_one_site)

## Main mass gap chain (3 axioms)

These are the axioms directly used in the proof of
`ON_LSM_hasCorrelationDecay`.

### 1. `correlator_le_thimble_avg`
- **File:** `Thimble/MassGapProof.lean`
- **Statement:** For the O(N) LSM measure and a `ThimbleIntegralData T`,
  |⟨φⁱ(x)φⁱ(y)⟩_c| ≤ T.thimble_avg x y.
- **Note:** `thimble_bound` (|⟨φφ⟩_c| ≤ M⁻¹) is now a THEOREM
  proved from this axiom + T.fk_bound (inside ThimbleIntegralData).
- **Packages** (ORDER MATTERS — Cauchy BEFORE triangle):
  (a) HS representation of the correlator (from HSIdentity, proved)
  (b) Cauchy contour shift to quantum thimble (BEFORE absolute values!)
  (c) Triangle inequality on POSITIVE thimble measure
- **Difficulty:** Medium (measure plumbing). The hard mathematical
  content (Cauchy, quantum HJ, FK) is in the axioms it depends on.
- **Proof plan:**
  (a) Define σ-integral from algebraic HS identity (measure plumbing)
  (b) Apply vertical_contour_shift site-by-site (Fubini + decay)
  (c) On the thimble: measure positive (quantum_thimble_exists),
      so triangle inequality is clean (no sign problem)
- **Dependencies:** vertical_contour_shift, quantum_thimble_exists

### 2. `green_exponential_decay`
- **File:** `Thimble/FKBoundShifted.lean`
- **Statement:** S.realPart⁻¹(x,y) ≤ (1/m₀²) · exp(-m₀·dist(x,y))
  for the concrete operator M = -Δ + m₀² from ShiftedOperatorData.
- **Difficulty:** Medium. Standard Combes-Thomas estimate.
- **Proof plan:** Reduce to greenFunction_exponential_decay on the
  1D torus (axiom 19) via product structure of the d-dimensional torus.
- **Dependencies:** greenFunction_exponential_decay

### ~~3. `greenFunction_explicit_formula`~~ — NOW PROVED
- **File:** `Thimble/GreenDecay.lean`
- **Status:** **PROVED** via operator verification + PD injectivity.
- **Proof:** Both Fourier G and explicit formula satisfy (-Δ+m²)f = δ₀.
  Operator is injective (positive definite: Re⟨f,Af⟩ ≥ m²‖f‖²).
  Therefore G = explicit formula.
  - `nnGreenFunction_satisfies_eq`: eigenvalue identity + Fourier orthogonality
  - `explicitGreen_satisfies_eq`: char eq recurrence + Vieta jump condition
  - `nnOp_injective`: AM-GM + sum reindexing on ZMod
- **Note:** `greenFunction_exponential_decay` is also proved from this.

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

### ~~12. `vertical_contour_shift`~~ — NOW PROVED
- **File:** `HSEquivalence/ContourShift.lean`
- **Status:** **PROVED** from Mathlib (was axiom).
- **Proof:** rectangle_integral_vanishes + intervalIntegral_tendsto_integral
  + norm_integral_le_of_norm_le_const + tendsto_nhds_unique +
  Bound.div_lt_one_of_pos_of_lt. All Mathlib lemmas, 0 sorries.

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

### ~~17. `contDiff_matrix_det`~~ — NOW PROVED
- **File:** `GeneralResults/MatrixCalculus.lean`
- **Status:** **PROVED** directly with linftyOp norm.
- **Proof:** Leibniz formula (det = Σ_σ sign(σ) Π_i A(σi,i)) + each entry
  extraction is a bounded linear functional (‖A i j‖ ≤ ‖A‖_linftyOp via
  single_le_sum + le_sup). No norm transfer needed.

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

1. ~~**greenFunction_explicit_formula**~~ **PROVED!**
2. ~~**vertical_contour_shift**~~ **PROVED!**
3. ~~**contDiff_matrix_det**~~ **PROVED!**
4. **heat_kernel_entrywise_nonneg** (medium, Metzler shift — partially proved in markov-semigroups)
5. **nComponentGreen_uniform_bound** (easy, port from gaussian-field)
6. **laplace_transform_inverse** (medium, spectral theorem)
7. **fderiv_log_det** (medium, chain rule + cofactor)
8. **trotter_product_matrix** (medium, BCH remainder)
9. **quantum_thimble_exists** (hard, IFT for quantum HJ)
10. **correlator_le_thimble_avg** (medium, measure plumbing + other axioms)

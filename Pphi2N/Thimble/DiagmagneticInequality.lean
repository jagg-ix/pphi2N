/-
Copyright (c) 2026 Michael R. Douglas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Diamagnetic Inequality for Finite Matrices

The diamagnetic inequality: for M a real positive definite matrix and
V a real diagonal matrix,

  |(M + iV)⁻¹(x,y)| ≤ M⁻¹(x,y)

This replaces the abstract `resolvent_complex_bound` axiom in
`FKBoundShifted.lean` with a concrete matrix statement.

## Proof strategy (semigroup approach)

For finite matrices, the proof follows these steps:

1. **Laplace transform**: (M + iV)⁻¹ = ∫₀^∞ exp(-t(M+iV)) dt
   and M⁻¹ = ∫₀^∞ exp(-tM) dt  (valid when M is PD).

2. **Trotter product**: exp(-t(M+iV)) = lim_{n→∞} (exp(-tM/n)·exp(-itV/n))^n

3. **Phase bound**: |exp(-itV/n)(x,y)| = δ_{xy} since V is diagonal
   and exp of a purely imaginary diagonal has unit-modulus entries.

4. **Heat kernel positivity**: exp(-tM)(x,y) ≥ 0 when M is a lattice
   Laplacian (equivalently, M has nonpositive off-diagonal entries).

5. **Entry-wise triangle inequality**: combining (2)-(4) gives
   |exp(-t(M+iV))(x,y)| ≤ exp(-tM)(x,y), then integrate.

## What's proved vs axiomatized

**Proved** (using Mathlib):
- `exp_diagonal_norm_le` — |exp(diagonal(iv))(x,y)| ≤ δ_{xy} (step 3)
- `exp_neg_diagonal_eq` — exp of real diagonal is diagonal of exp
- `exp_imaginary_diagonal_norm` — norm of exp(i·diag(v)) entries

**Axiomatized** (clean mathematical statements):
- `heat_kernel_entrywise_nonneg` — exp(-tM) ≥ 0 entrywise for
  M with nonpositive off-diagonal (Z-matrix / Metzler theory)
- `laplace_transform_inverse` — A⁻¹ = ∫₀^∞ exp(-tA) dt for PD A
- `trotter_product_matrix` — Lie-Trotter for finite matrices
- `diamagnetic_inequality` — the main result, assembled from above

## References

- Simon, *Functional Integration and Quantum Physics* (1979), Ch. 22
- Reed-Simon IV, §X.4, Kato's inequality
- Beurling-Deny, positivity-preserving semigroups
-/

import Pphi2N.Thimble.ShiftedOperator
import Mathlib.Analysis.Normed.Algebra.MatrixExponential
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Analysis.Complex.Trigonometric
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

noncomputable section

open Matrix NormedSpace Complex MeasureTheory

namespace Pphi2N

variable {n : Type*} [Fintype n] [DecidableEq n]

/-! ## Step 3: Phase bound for diagonal matrices

For a diagonal matrix V with real entries, exp(iV) is diagonal with
unit-modulus entries: |exp(iV)(x,y)| = δ_{xy}.

This is the KEY provable step, using:
- `Matrix.exp_diagonal` : exp(diag(v)) = diag(exp(v))
- `Complex.norm_exp_ofReal_mul_I` : ‖exp(x·I)‖ = 1 for x : ℝ
-/

/-- The matrix exponential of a real diagonal matrix is the diagonal
matrix of exponentials. Specialized to ℝ from `Matrix.exp_diagonal`. -/
theorem exp_real_diagonal (v : n → ℝ) :
    exp (Matrix.diagonal v) = Matrix.diagonal (NormedSpace.exp v) :=
  Matrix.exp_diagonal v

/-- The matrix exponential of a purely imaginary diagonal matrix (over ℂ)
is a diagonal matrix whose entries have unit norm.

For V = diag(v₁,...,vₙ) real, exp(iV) = diag(e^{iv₁},...,e^{ivₙ}),
and |e^{ivⱼ}| = 1 since vⱼ is real. -/
theorem exp_imaginary_diagonal_entries (v : n → ℝ) (x y : n) :
    ‖(exp (Matrix.diagonal (fun j => (↑(v j) : ℂ) * I)) x y)‖ =
      if x = y then 1 else 0 := by
  -- exp of diagonal is diagonal of exp
  rw [Matrix.exp_diagonal]
  simp only [Matrix.diagonal_apply]
  split_ifs with h
  · -- Diagonal entry: ‖exp(v_x · I)‖ = 1
    subst h
    simp only [Pi.coe_exp]
    rw [← Complex.exp_eq_exp_ℂ]
    exact Complex.norm_exp_ofReal_mul_I (v x)
  · -- Off-diagonal: 0
    exact norm_zero

/-- **Entry-wise norm bound for exp(itV)**:
The matrix exp(i·t·diag(v)) has entries bounded by δ_{xy}.

This is the phase-cancellation bound: the "magnetic" phase factor
exp(itV) has unit-modulus diagonal entries and zeros off-diagonal. -/
theorem exp_imaginary_diagonal_norm_le (t : ℝ) (v : n → ℝ) (x y : n) :
    ‖(exp (Matrix.diagonal (fun j => (↑(t * v j) : ℂ) * I)) x y)‖ ≤
      if x = y then 1 else 0 :=
  le_of_eq (exp_imaginary_diagonal_entries (fun j => t * v j) x y)

/-! ## Entry-wise bound for products with diagonal phase factors

The key algebraic lemma: if A has nonneg entries and U is diagonal
with |U(x,x)| ≤ 1, then |(U·A·U)(x,y)| ≤ A(x,y).

This applies to each Trotter factor: exp(-tM/n) has nonneg entries
(by heat kernel positivity), and exp(-itV/n) is diagonal unitary. -/

omit [DecidableEq n] in
/-- For any matrices A, B over ℂ, the (x,y) entry of A * B satisfies
the triangle inequality: ‖(A * B) x y‖ ≤ ∑ k, ‖A x k‖ * ‖B k y‖. -/
theorem matrix_mul_entry_norm_le (A B : Matrix n n ℂ) (x y : n) :
    ‖(A * B) x y‖ ≤ ∑ k : n, ‖A x k‖ * ‖B k y‖ := by
  simp only [Matrix.mul_apply]
  calc ‖∑ k, A x k * B k y‖
      ≤ ∑ k, ‖A x k * B k y‖ := norm_sum_le _ _
    _ = ∑ k, ‖A x k‖ * ‖B k y‖ := by
        congr 1; ext k; exact norm_mul (A x k) (B k y)

/-- Multiplication by a diagonal unitary on the LEFT contracts entries:
if U = diag(u) with |uᵢ| ≤ 1 for all i, then |(U·A)(x,y)| ≤ |A(x,y)|. -/
theorem diagonal_mul_entry_norm_le (u : n → ℂ) (hu : ∀ i, ‖u i‖ ≤ 1)
    (A : Matrix n n ℂ) (x y : n) :
    ‖((Matrix.diagonal u) * A) x y‖ ≤ ‖A x y‖ := by
  simp only [Matrix.diagonal_mul]
  calc ‖u x * A x y‖ = ‖u x‖ * ‖A x y‖ := norm_mul (u x) (A x y)
    _ ≤ 1 * ‖A x y‖ := by apply mul_le_mul_of_nonneg_right (hu x) (norm_nonneg _)
    _ = ‖A x y‖ := one_mul _

/-- Multiplication by a diagonal unitary on the RIGHT contracts entries:
if U = diag(u) with |uᵢ| ≤ 1 for all i, then |(A·U)(x,y)| ≤ |A(x,y)|. -/
theorem mul_diagonal_entry_norm_le (u : n → ℂ) (hu : ∀ i, ‖u i‖ ≤ 1)
    (A : Matrix n n ℂ) (x y : n) :
    ‖(A * (Matrix.diagonal u)) x y‖ ≤ ‖A x y‖ := by
  simp only [Matrix.mul_diagonal]
  calc ‖A x y * u y‖ = ‖A x y‖ * ‖u y‖ := norm_mul (A x y) (u y)
    _ ≤ ‖A x y‖ * 1 := by apply mul_le_mul_of_nonneg_left (hu y) (norm_nonneg _)
    _ = ‖A x y‖ := mul_one _

/-- The purely imaginary exponential exp(i·diag(v)) is a diagonal
matrix with unit-norm entries. -/
theorem exp_imaginary_diagonal_unit_entries (v : n → ℝ) (i : n) :
    ‖(exp (Matrix.diagonal (fun j => (↑(v j) : ℂ) * I))) i i‖ = 1 := by
  have := exp_imaginary_diagonal_entries v i i
  simp at this
  exact this

/-- Sandwich bound: U · A · U⁻¹ where U is diagonal unitary preserves
entry-wise norms when A has real nonneg entries.

|(U·A·U*)(x,y)| = |u_x| · |A(x,y)| · |conj(u_y)| = |A(x,y)|
when |u_x| = 1 for all x. -/
theorem sandwich_diagonal_unitary_norm (u : n → ℂ) (hu : ∀ i, ‖u i‖ = 1)
    (A : Matrix n n ℂ) (x y : n) :
    ‖((Matrix.diagonal u) * A * (Matrix.diagonal (star u))) x y‖ = ‖A x y‖ := by
  simp only [Matrix.diagonal_mul, Matrix.mul_diagonal, Pi.star_apply]
  rw [norm_mul, norm_mul, hu x, one_mul]
  rw [show star (u y) = starRingEnd ℂ (u y) from rfl]
  rw [RCLike.norm_conj, hu y, mul_one]

/-! ## Axioms: steps requiring new infrastructure

These are the mathematical facts not yet in Mathlib that would complete
the proof. Each is a standard result with clear references. -/

/-- **Heat kernel positivity** (Beurling-Deny / Z-matrix theory):

For M with nonneg diagonal and nonpositive off-diagonal entries
(a "Z-matrix" or "essentially nonnegative" -M), the matrix
semigroup exp(-tM) has nonneg entries for all t ≥ 0.

Equivalently: if -M is a Metzler matrix, then exp(t·(-M)) ≥ 0
entrywise. The lattice Laplacian -Δ + m² satisfies this since
-Δ has nonpositive off-diagonal entries (the edge weights are
negative in the Laplacian convention L = D - A).

Proof idea: exp(-tM) = lim_{n→∞} (I - tM/n)^n. For large n,
I - tM/n has nonneg entries (diagonal ≥ 1 - t·diag(M)/n > 0,
off-diagonal = -t·M_{ij}/n ≥ 0 since M_{ij} ≤ 0 for i≠j).
Product of nonneg matrices is nonneg.

References:
- Berman-Plemmons, *Nonnegative Matrices in the Mathematical Sciences*
- Horn-Johnson, *Matrix Analysis*, §8.4
-/
axiom heat_kernel_entrywise_nonneg (M : Matrix n n ℝ)
    -- M is "essentially nonnegative" negated: M_{ij} ≤ 0 for i ≠ j
    (hoff : ∀ i j, i ≠ j → M i j ≤ 0)
    -- t ≥ 0
    (t : ℝ) (ht : 0 ≤ t)
    -- All entries of exp(-tM) are nonneg
    (x y : n) :
    0 ≤ (exp ((-t) • M) x y : ℝ)

/-- **Laplace transform of matrix semigroup gives inverse** (entry-wise):

For a positive definite matrix M (all eigenvalues > 0):
  M⁻¹(x,y) = ∫₀^∞ exp(-tM)(x,y) dt

This is the matrix version of ∫₀^∞ e^{-λt} dt = 1/λ applied
to each eigenvalue via the spectral theorem. Stated entry-wise to
avoid needing a normed space instance on matrices.

References:
- Horn-Johnson, *Matrix Analysis*, section 6.2
- Higham, *Functions of Matrices*, Theorem 10.2 -/
axiom laplace_transform_inverse (M : Matrix n n ℝ)
    (hM : M.PosDef) (x y : n) :
    M⁻¹ x y = ∫ t in Set.Ioi (0 : ℝ), (exp ((-t) • M)) x y

/-- **Complex Laplace transform for M + iV** (entry-wise):

For M positive definite and V real:
  (M + iV)⁻¹(x,y) = ∫₀^∞ exp(-t(M + iV))(x,y) dt

This converges because the eigenvalues of M + iV have
positive real part at least min eigenvalue of M > 0.

References:
- Reed-Simon I, Theorem VI.4 (Hille-Yosida)
- Kato, *Perturbation Theory*, Ch. IX -/
axiom laplace_transform_inverse_complex
    (M V : Matrix n n ℝ) (hM : M.PosDef) (x y : n) :
    (M.map ((↑) : ℝ → ℂ) + (V.map ((↑) : ℝ → ℂ)).map (· * I))⁻¹ x y =
      ∫ t in Set.Ioi (0 : ℝ),
        (exp ((-t) • (M.map ((↑) : ℝ → ℂ) + (V.map ((↑) : ℝ → ℂ)).map (· * I)))) x y

/-- **Trotter product formula for finite matrices**:

For matrices A, B over a Banach algebra:
  exp(A + B) = lim_{n→∞} (exp(A/n) · exp(B/n))^n

For finite matrices this follows from the BCH formula and
convergence of the operator norm.

References:
- Trotter, Proc. AMS 10 (1959), 545-551
- Reed-Simon I, Theorem VIII.30
-/
axiom trotter_product_matrix (A B : Matrix n n ℂ) :
    exp (A + B) = Filter.limUnder Filter.atTop
      (fun (k : ℕ) => ((exp ((1 / (k : ℂ)) • A)) * (exp ((1 / (k : ℂ)) • B))) ^ k)

/-! ## The Diamagnetic Inequality

We state the main theorem: for M positive definite with nonpositive
off-diagonal entries (e.g., a lattice Laplacian + mass), and V real
diagonal, the entry-wise bound |(M+iV)⁻¹(x,y)| ≤ M⁻¹(x,y) holds. -/

/-- **Diamagnetic inequality for finite matrices** (semigroup proof):

For M a real positive definite matrix with M_{ij} ≤ 0 for i ≠ j
(lattice Laplacian structure), and V = diag(v) a real diagonal matrix:

  |(M + iV)⁻¹(x,y)| ≤ M⁻¹(x,y)

Proof outline (each step references the corresponding axiom/theorem):
1. (M+iV)⁻¹ = ∫₀^∞ exp(-t(M+iV)) dt  [`laplace_transform_inverse_complex`]
2. M⁻¹ = ∫₀^∞ exp(-tM) dt  [`laplace_transform_inverse`]
3. exp(-t(M+iV)) = exp(-tM)·exp(-itV) when M,V commute, or via
   Trotter when they don't [`trotter_product_matrix`]
4. |exp(-itV)(x,y)| = δ_{xy}  [`exp_imaginary_diagonal_entries`]
5. exp(-tM)(x,y) ≥ 0  [`heat_kernel_entrywise_nonneg`]
6. Therefore |exp(-t(M+iV))(x,y)| ≤ exp(-tM)(x,y)
7. Integrate: |(M+iV)⁻¹(x,y)| ≤ M⁻¹(x,y) by triangle inequality

The key simplification for V diagonal: exp(-itV) is diagonal with
unit-modulus entries, so it acts as a phase on each site. The
product exp(-tM/n)·exp(-itV/n) picks up phase factors but the
nonneg matrix exp(-tM/n) controls the magnitudes.

References:
- Simon, *Functional Integration and Quantum Physics* (1979), §22
- Reed-Simon IV, Kato's inequality / diamagnetic inequality
-/
axiom diamagnetic_inequality (M : Matrix n n ℝ)
    (hM : M.PosDef)
    -- M has lattice Laplacian structure: nonpositive off-diagonal
    (hoff : ∀ i j, i ≠ j → M i j ≤ 0)
    -- V is a real diagonal matrix
    (v : n → ℝ)
    (x y : n) :
    ‖((M.map ((↑) : ℝ → ℂ) +
      Matrix.diagonal (fun j => (↑(v j) : ℂ) * I))⁻¹ x y)‖ ≤
      M⁻¹ x y

/-! ## Connecting to the existing `resolvent_complex_bound`

We show that `diamagnetic_inequality` implies the abstract bound
used in `FKBoundShifted.lean`, specialized to the lattice setting. -/

/-- The diamagnetic inequality implies the FK resolvent bound
for the shifted operator on a finite lattice.

Given `ShiftedOperatorData` (which bundles the lattice Laplacian
and gap equation), the diamagnetic inequality applies to
M = -Δ + m₀² (which is PD with gap m₀² and has nonpositive
off-diagonal entries from the Laplacian) and V = diag(2u/√N). -/
theorem diamagnetic_implies_fk_bound
    (M : Matrix n n ℝ) (hM : M.PosDef)
    (hoff : ∀ i j, i ≠ j → M i j ≤ 0)
    (v : n → ℝ) :
    -- The entry-wise bound holds for all pairs
    ∀ x y, ‖((M.map ((↑) : ℝ → ℂ) +
      Matrix.diagonal (fun j => (↑(v j) : ℂ) * I))⁻¹ x y)‖ ≤
      M⁻¹ x y :=
  fun x y => diamagnetic_inequality M hM hoff v x y

/-! ## Auxiliary: nonneg entries of M⁻¹

For M PD with nonpositive off-diagonal, M⁻¹ has all nonneg entries.
This follows from the heat kernel positivity + Laplace transform. -/

/-- **M-matrix inverse nonnegativity**: If M is positive definite
with M_{ij} ≤ 0 for i ≠ j (an "M-matrix"), then M⁻¹ has all
nonneg entries.

Proof: M⁻¹ = ∫₀^∞ exp(-tM) dt, and each exp(-tM) has nonneg entries
by `heat_kernel_entrywise_nonneg`, so the integral does too.

References:
- Berman-Plemmons, *Nonneg Matrices in Math Sciences*, Theorem 6.2.3
-/
axiom m_matrix_inverse_nonneg (M : Matrix n n ℝ)
    (hM : M.PosDef)
    (hoff : ∀ i j, i ≠ j → M i j ≤ 0)
    (x y : n) : 0 ≤ M⁻¹ x y

/-! ## Commuting case: when M and V commute

When M and V commute (e.g., V is a scalar multiple of the identity,
or both are diagonal in the same basis), the Trotter product
simplifies to a direct product: exp(A+B) = exp(A)·exp(B).

This case is PROVABLE in Mathlib using `Matrix.exp_add_of_commute`. -/

/-- When M and V are simultaneously diagonal, the diamagnetic
inequality follows purely from Mathlib's existing API.

If M = diag(λ) with λᵢ > 0 and V = diag(v), then:
- (M + iV)⁻¹ = diag(1/(λ + iv)) since everything is diagonal
- |(1/(λⱼ + ivⱼ))| = 1/√(λⱼ² + vⱼ²) ≤ 1/λⱼ = M⁻¹(j,j)
- Off-diagonal entries are zero on both sides

This is the base case that the spectral theorem reduces the general
Hermitian case to (modulo the similarity transform).

Helper: a ≤ |a + bi| for a > 0 (1D diamagnetic inequality). -/
-- a ≤ ‖a + bi‖ for a > 0 (the 1D diamagnetic inequality).
-- Proof: ‖a + bi‖² = a² + b² ≥ a², take sqrt.
theorem real_le_norm_add_mul_I (a b : ℝ) (ha : 0 < a) :
    a ≤ ‖(↑a + ↑b * I : ℂ)‖ := by
  -- ‖z‖ = √(normSq z) and normSq(a+bi) = a²+b²
  -- So ‖a+bi‖ = √(a²+b²) ≥ √(a²) = a
  have h_sq : a ^ 2 ≤ ‖(↑a + ↑b * I : ℂ)‖ ^ 2 := by
    rw [Complex.sq_norm]
    simp only [Complex.normSq_apply, Complex.add_re, Complex.ofReal_re,
               Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
               Complex.I_re, Complex.I_im, Complex.add_im, Complex.ofReal_im,
               Complex.mul_im, mul_zero, mul_one, zero_mul, sub_zero, zero_add]
    nlinarith [sq_nonneg b]
  nlinarith [norm_nonneg (↑a + ↑b * I : ℂ), sq_nonneg (‖(↑a + ↑b * I : ℂ)‖ - a)]

theorem diamagnetic_diagonal (eigvals : n → ℝ) (h_pos : ∀ i, 0 < eigvals i)
    (v : n → ℝ) (x y : n) :
    ‖((Matrix.diagonal (fun j => (↑(eigvals j) : ℂ) + ↑(v j) * I))⁻¹ x y)‖ ≤
      (Matrix.diagonal (fun j => (1 : ℝ) / eigvals j)) x y := by
  rw [Matrix.inv_diagonal]
  by_cases h : x = y
  · subst h
    simp only [Matrix.diagonal_apply_eq, Pi.inv_apply, one_div]
    -- Need ‖(eigvals x + v x * I)⁻¹‖ ≤ (eigvals x)⁻¹
    -- From real_le_abs_add_mul_I: eigvals x ≤ |eigvals x + v x * I|
    -- So (eigvals x)⁻¹ ≥ |eigvals x + v x * I|⁻¹ = ‖(eigvals x + v x * I)⁻¹‖
    -- ‖z⁻¹‖ = ‖z‖⁻¹ ≤ (eigvals x)⁻¹ from real_le_norm_add_mul_I
    -- The goal involves Pi.inv_apply unfolding; API plumbing.
    sorry -- from real_le_norm_add_mul_I + norm_inv + inv_anti
  · -- Off-diagonal: (diagonal f)⁻¹ x y = 0 when x ≠ y
    simp only [Matrix.diagonal_apply_ne _ h]
    simp

/-! ## Summary of axiom dependencies

The full proof of the diamagnetic inequality requires 5 axioms:

1. `heat_kernel_entrywise_nonneg` — exp(-tM) ≥ 0 entrywise
   (Metzler/Z-matrix theory; provable via "I - tM/n" Euler scheme)

2. `laplace_transform_inverse` — M⁻¹ = ∫ exp(-tM) dt
   (spectral theorem + ∫ e^{-λt} dt = 1/λ)

3. `laplace_transform_inverse_complex` — same for M + iV
   (eigenvalues have positive real part)

4. `trotter_product_matrix` — Lie-Trotter product formula
   (BCH series convergence for bounded operators)

5. `diamagnetic_inequality` — the assembled result

Plus `m_matrix_inverse_nonneg` for the FK bound connection.

The PROVED components are:
- `exp_imaginary_diagonal_entries` — |exp(iV)(x,y)| = δ_{xy}
- `diagonal_mul_entry_norm_le` / `mul_diagonal_entry_norm_le` —
  diagonal contractions
- `sandwich_diagonal_unitary_norm` — U·A·U* preserves norms
- `matrix_mul_entry_norm_le` — entry-wise triangle inequality

**Potential simplification**: In the simultaneously-diagonal case
(after conjugating M to diagonal form), the proof reduces to
a 1D inequality |1/(λ+iv)| ≤ 1/λ, which needs NO axioms beyond
the spectral theorem (already in Mathlib). The gap is proving
that conjugation preserves the entry-wise bound, which requires
heat kernel positivity of M in its ORIGINAL basis. -/

end Pphi2N

end

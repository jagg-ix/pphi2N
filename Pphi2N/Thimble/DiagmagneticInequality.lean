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
- `laplace_transform_inverse` — A⁻¹ = ∫₀^∞ exp(-tA) dt for PD A
  (via spectral theorem + ∫ e^{-λt} dt = 1/λ)

**Axiomatized** (clean mathematical statements):
- `heat_kernel_entrywise_nonneg` — exp(-tM) ≥ 0 entrywise for
  M with nonpositive off-diagonal (Z-matrix / Metzler theory)
- `trotter_product_matrix` — Lie-Trotter for finite matrices
- `diamagnetic_inequality` — the main result, assembled from above

## References

- Simon, *Functional Integration and Quantum Physics* (1979), Ch. 22
- Reed-Simon IV, §X.4, Kato's inequality
- Beurling-Deny, positivity-preserving semigroups
-/

import Pphi2N.Thimble.ShiftedOperator
import MarkovSemigroups.Matrix.HeatKernel
import Mathlib.Analysis.Normed.Algebra.MatrixExponential
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Analysis.Complex.Trigonometric
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Algebra.Group.Pi.Units
import Mathlib.LinearAlgebra.Complex.FiniteDimensional

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
-- Proved in markov-semigroups (MatrixSemigroup.heat_kernel_entrywise_nonneg)
-- via the Metzler shift: write -tM = -tαI + t(αI-M) with α large,
-- then exp(-tM) = exp(-tα)·exp(t(αI-M)) ≥ 0 since αI-M ≥ 0 entrywise.
theorem heat_kernel_entrywise_nonneg (M : Matrix n n ℝ)
    (hoff : ∀ i j, i ≠ j → M i j ≤ 0)
    (t : ℝ) (ht : 0 ≤ t) (x y : n) :
    0 ≤ (exp ((-t) • M) x y : ℝ) :=
  MatrixSemigroup.heat_kernel_entrywise_nonneg M hoff t ht x y

/-- **Laplace transform of matrix semigroup gives inverse** (entry-wise):

For a positive definite matrix M (all eigenvalues > 0):
  M⁻¹(x,y) = ∫₀^∞ exp(-tM)(x,y) dt

Proof via spectral theorem: M = U * diag(λ) * Uᵀ, so both sides
reduce to ∑ k, U(x,k) * (1/λ_k) * U(y,k) using the scalar identity
∫₀^∞ exp(-λt) dt = 1/λ for λ > 0.

References:
- Horn-Johnson, *Matrix Analysis*, section 6.2
- Higham, *Functions of Matrices*, Theorem 10.2 -/
-- Helper lemmas for the spectral proof
private lemma mul_diagonal_star_entry_lt (A B : Matrix n n ℝ) (d : n → ℝ) (x y : n) :
    (A * diagonal d * star B) x y = ∑ k, A x k * d k * B y k := by
  simp [mul_apply, diagonal_apply, star_apply, Finset.sum_ite_eq', Finset.mem_univ, star_trivial]

private lemma integral_exp_neg_pos_lt (lam : ℝ) (hlam : 0 < lam) :
    ∫ t in Set.Ioi (0 : ℝ), Real.exp (-lam * t) = lam⁻¹ := by
  have h1 := integral_exp_mul_Ioi (show -lam < 0 from by linarith) 0
  simp at h1; convert h1 using 1; congr 1; ext t; ring

theorem laplace_transform_inverse (M : Matrix n n ℝ)
    (hM : M.PosDef) (x y : n) :
    M⁻¹ x y = ∫ t in Set.Ioi (0 : ℝ), (exp ((-t) • M)) x y := by
  set hH := hM.isHermitian
  set U := hH.eigenvectorUnitary.val
  set ev := hH.eigenvalues
  have hev_pos : ∀ i, 0 < ev i := hM.eigenvalues_pos
  -- Spectral decomposition: M = U * diag(eigenvalues) * Uᵀ
  have hspec : M = U * diagonal ev * star U := by
    have := hH.spectral_theorem
    simp only [Unitary.conjStarAlgAut_apply] at this; convert this using 2
  have hU_unit : IsUnit U :=
    ⟨⟨U, star U, hH.eigenvectorUnitary.prop.2, hH.eigenvectorUnitary.prop.1⟩, rfl⟩
  have hU_inv : U⁻¹ = star U := inv_eq_left_inv hH.eigenvectorUnitary.prop.1
  have hstarU_inv : (star U)⁻¹ = U := inv_eq_left_inv hH.eigenvectorUnitary.prop.2
  -- Summand: f k t = U(x,k) * exp(-t * λ_k) * U(y,k)
  set f : n → ℝ → ℝ := fun k t => U x k * Real.exp (-t * ev k) * U y k
  -- Step 1: exp(-t•M)(x,y) = ∑ k, f k t (via spectral decomposition + exp_conj)
  have exp_sum : ∀ t : ℝ, (exp ((-t) • M)) x y = ∑ k, f k t := by
    intro t; rw [hspec]
    conv_lhs => rw [show (-t) • (U * diagonal ev * star U) =
      U * ((-t) • diagonal ev) * star U from by simp]
    rw [show U * ((-t) • diagonal ev) * star U =
      U * ((-t) • diagonal ev) * U⁻¹ from by rw [hU_inv]]
    rw [Matrix.exp_conj U _ hU_unit, hU_inv, ← diagonal_smul, Matrix.exp_diagonal,
        mul_diagonal_star_entry_lt]
    congr 1; ext k; congr 1; congr 1
    rw [Pi.coe_exp, Real.exp_eq_exp_ℝ]; simp [Pi.smul_apply, smul_eq_mul]
  -- Step 2: Each summand is integrable on (0,∞)
  have hint : ∀ k ∈ Finset.univ,
      Integrable (f k) (volume.restrict (Set.Ioi (0 : ℝ))) := by
    intro k _
    show IntegrableOn (f k) (Set.Ioi 0)
    have : f k = fun t => (U x k * U y k) * Real.exp (-(ev k) * t) := by
      ext t; simp [f]; ring
    rw [this]
    exact (integrableOn_exp_mul_Ioi (by linarith [hev_pos k]) 0).const_mul _
  -- Step 3: Each integral evaluates to U(x,k) * (λ_k)⁻¹ * U(y,k)
  have hint_eval : ∀ k, ∫ t in Set.Ioi (0 : ℝ), f k t =
      U x k * (ev k)⁻¹ * U y k := by
    intro k
    have h : ∀ t, f k t = (U x k * U y k) * Real.exp (-(ev k) * t) := by
      intro t; simp [f]; ring
    simp_rw [h]
    rw [integral_const_mul, integral_exp_neg_pos_lt (ev k) (hev_pos k)]; ring
  -- Step 4: RHS = ∑ k, U(x,k) * (λ_k)⁻¹ * U(y,k)
  have rhs_eq : (∫ t in Set.Ioi (0 : ℝ), (exp ((-t) • M)) x y) =
      ∑ k, U x k * (ev k)⁻¹ * U y k := by
    simp_rw [exp_sum]
    rw [integral_finset_sum Finset.univ hint]
    congr 1; ext k; exact hint_eval k
  -- Step 5: LHS = ∑ k, U(x,k) * (λ_k)⁻¹ * U(y,k) (via M⁻¹ = U * D⁻¹ * Uᵀ)
  have lhs_eq : M⁻¹ x y = ∑ k, U x k * (ev k)⁻¹ * U y k := by
    rw [hspec, mul_inv_rev (U * diagonal ev) (star U), mul_inv_rev U (diagonal ev)]
    rw [hU_inv, hstarU_inv, ← mul_assoc, inv_diagonal, mul_diagonal_star_entry_lt]
    congr 1; ext k; congr 1; congr 1
    have hunit : IsUnit ev :=
      Pi.isUnit_iff.mpr (fun i => isUnit_iff_ne_zero.mpr (ne_of_gt (hev_pos i)))
    conv_lhs => rw [← IsUnit.unit_spec hunit]
    rw [Ring.inverse_unit, Units.val_inv_eq_inv_val, Pi.inv_apply, IsUnit.unit_spec]
  rw [lhs_eq, rhs_eq]

/-- **Derivative of the antiderivative** for the complex Laplace transform.

For A = M + iV with M positive definite:
  d/dt[-(exp(-tA) · A⁻¹)(x,y)] = (exp(-tA))(x,y)

This follows from d/dt[exp(t·(-A))] = exp(t·(-A))·(-A)
(`hasDerivAt_exp_smul_const` in Mathlib) and (-A)·A⁻¹ = -I.
The entry-wise derivative follows because for finite-dimensional spaces,
the linftyOp and product topologies agree (`hasDerivAt_pi`). -/
private lemma hasDerivAt_laplace_antideriv
    (M V : Matrix n n ℝ) (hM : M.PosDef) (x y : n) (t : ℝ) :
    HasDerivAt
      (fun s => -((exp ((-s) • (M.map ((↑) : ℝ → ℂ) + (V.map ((↑) : ℝ → ℂ)).map (· * I))) *
        (M.map ((↑) : ℝ → ℂ) + (V.map ((↑) : ℝ → ℂ)).map (· * I))⁻¹) x y))
      ((exp ((-t) • (M.map ((↑) : ℝ → ℂ) + (V.map ((↑) : ℝ → ℂ)).map (· * I)))) x y)
      t := by
  -- Proof sketch: Matrix-level derivative via hasDerivAt_exp_smul_const with linftyOp norm,
  -- then extract entries. Both norms give the same topology on finite-dim Matrix n n ℂ.
  -- d/dt[exp(t·(-A))] = exp(t·(-A))·(-A), so d/dt[-exp(t·(-A))·A⁻¹] = exp(t·(-A))·A·A⁻¹ = exp(t·(-A))
  sorry

/-- **Integrability** of exp(-tA)(x,y) on (0,∞) for A = M + iV.

Follows from the **logarithmic norm bound** (Dahlquist/Coppel inequality):
  ‖exp(-tA)‖ ≤ exp(-t · λ_min(M))
where λ_min(M) > 0 is the minimum eigenvalue of M. Each entry is bounded
by the operator norm, giving ‖exp(-tA)(x,y)‖ ≤ exp(-t · λ_min(M)),
which is integrable on (0,∞).

References: Söderlind, BIT 46 (2006); Coppel (1965). -/
private lemma integrableOn_laplace_integrand
    (M V : Matrix n n ℝ) (hM : M.PosDef) (x y : n) :
    IntegrableOn
      (fun t : ℝ => (exp ((-t) • (M.map ((↑) : ℝ → ℂ) + (V.map ((↑) : ℝ → ℂ)).map (· * I)))) x y)
      (Set.Ioi 0) volume := by
  sorry

/-- **Limit to zero** of the antiderivative as t → ∞.

Since ‖exp(-tA)‖ ≤ exp(-t · λ_min(M)) → 0 as t → ∞, we have
exp(-tA) → 0, hence exp(-tA) · A⁻¹ → 0, hence the negation → 0. -/
private lemma tendsto_laplace_antideriv
    (M V : Matrix n n ℝ) (hM : M.PosDef) (x y : n) :
    Filter.Tendsto
      (fun t : ℝ => -((exp ((-t) • (M.map ((↑) : ℝ → ℂ) + (V.map ((↑) : ℝ → ℂ)).map (· * I))) *
        (M.map ((↑) : ℝ → ℂ) + (V.map ((↑) : ℝ → ℂ)).map (· * I))⁻¹) x y))
      Filter.atTop (nhds 0) := by
  sorry

/-- **Complex Laplace transform for M + iV** (entry-wise):

For M positive definite and V real:
  (M + iV)⁻¹(x,y) = ∫₀^∞ exp(-t(M + iV))(x,y) dt

Proof via the fundamental theorem of calculus for improper integrals
(Mathlib: integral_Ioi_of_hasDerivAt_of_tendsto).

Define f(t) = -(exp(-tA)*A⁻¹)(x,y) (antiderivative) and g(t) = (exp(-tA))(x,y)
(integrand), where A = M + iV. Then:
- f'(t) = g(t), from d/dt exp(t*(-A)) = exp(t*(-A))*(-A) and A*A⁻¹ = I
- f(0) = -(A⁻¹)(x,y), from exp(0) = I
- f(t) tends to 0 as t tends to infinity, from the logarithmic norm bound

The FTC gives: integral of g = lim f - f(0) = 0 - (-(A⁻¹)(x,y)) = A⁻¹(x,y).

References:
- Reed-Simon I, Theorem VI.4 (Hille-Yosida)
- Kato, Perturbation Theory, Ch. IX -/
theorem laplace_transform_inverse_complex
    (M V : Matrix n n ℝ) (hM : M.PosDef) (x y : n) :
    (M.map ((↑) : ℝ → ℂ) + (V.map ((↑) : ℝ → ℂ)).map (· * I))⁻¹ x y =
      ∫ t in Set.Ioi (0 : ℝ),
        (exp ((-t) • (M.map ((↑) : ℝ → ℂ) + (V.map ((↑) : ℝ → ℂ)).map (· * I)))) x y := by
  set A := M.map ((↑) : ℝ → ℂ) + (V.map ((↑) : ℝ → ℂ)).map (· * I)
  -- Apply the fundamental theorem of calculus for improper integrals
  have hftc := integral_Ioi_of_hasDerivAt_of_tendsto'
    (f := fun t => -((exp ((-t) • A) * A⁻¹) x y))
    (f' := fun t => (exp ((-t) • A)) x y)
    (a := 0) (m := 0)
    (fun t _ht => hasDerivAt_laplace_antideriv M V hM x y t)
    (integrableOn_laplace_integrand M V hM x y)
    (tendsto_laplace_antideriv M V hM x y)
  -- Simplify f(0): exp(-0·A) = exp(0) = I, so f(0) = -(I·A⁻¹)(x,y) = -(A⁻¹)(x,y)
  simp only at hftc
  have hexp0 : exp ((-(0 : ℝ)) • A) = (1 : Matrix n n ℂ) := by
    have : (-(0 : ℝ)) • A = (0 : Matrix n n ℂ) := by ext i j; simp
    rw [this]; exact NormedSpace.exp_zero
  rw [hftc, hexp0, one_mul]; ring

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
theorem m_matrix_inverse_nonneg (M : Matrix n n ℝ)
    (hM : M.PosDef)
    (hoff : ∀ i j, i ≠ j → M i j ≤ 0)
    (x y : n) : 0 ≤ M⁻¹ x y := by
  rw [laplace_transform_inverse M hM x y]
  apply MeasureTheory.setIntegral_nonneg measurableSet_Ioi
  intro t ht
  exact heat_kernel_entrywise_nonneg M hoff t (le_of_lt (Set.mem_Ioi.mp ht)) x y

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
    simp only [Matrix.diagonal_apply_eq, one_div]
    -- Goal: ‖Ring.inverse(f) x‖ ≤ (eigvals x)⁻¹
    -- where f = fun j => ↑(eigvals j) + ↑(v j) * I
    -- Step 1: f is a unit in (n → ℂ) since each f j ≠ 0
    let f := fun j => (↑(eigvals j) : ℂ) + ↑(v j) * I
    have hf_ne : ∀ j, f j ≠ 0 := fun j => by
      intro heq; have := congr_arg Complex.re heq
      simp [Complex.add_re, Complex.ofReal_re, Complex.mul_re,
            Complex.ofReal_im, Complex.I_re, f] at this
      linarith [h_pos j]
    -- Ring.inverse on (n → ℂ) where each entry is nonzero:
    -- For a DivisionRing, Ring.inverse a = a⁻¹ when a ≠ 0.
    -- For Pi types, Ring.inverse = pointwise when IsUnit.
    -- We use Ring.inverse_eq_inv' (for GroupWithZero = field ℂ)
    -- applied pointwise.
    -- Step 2: unfold Ring.inverse to pointwise inverse
    -- For ℂ (a GroupWithZero), Ring.inverse a = a⁻¹ when a ≠ 0
    -- For Pi (n → ℂ), IsUnit f → Ring.inverse f = ↑(f.unit⁻¹)
    -- We need: Ring.inverse(f)(x) = (f x)⁻¹
    -- Use: Ring.inverse_eq_inv' for each component
    have hf_unit : IsUnit f := Pi.isUnit_iff.mpr (fun j =>
      IsUnit.mk0 _ (hf_ne j))
    -- Use Ring.inverse_unit to unfold, then Pi.inv_apply
    conv_lhs => rw [show Ring.inverse f = (↑hf_unit.unit⁻¹ : n → ℂ) from by
      have := Ring.inverse_unit hf_unit.unit
      rwa [IsUnit.unit_spec] at this]
    rw [Units.val_inv_eq_inv_val, Pi.inv_apply, IsUnit.unit_spec]
    -- Goal: ‖(f x)⁻¹‖ ≤ (eigvals x)⁻¹
    -- Goal should be: ‖(f x)⁻¹‖ ≤ (eigvals x)⁻¹
    -- = ‖(↑(eigvals x) + ↑(v x) * I)⁻¹‖ ≤ (eigvals x)⁻¹
    simp only [norm_inv, f]
    exact inv_anti₀ (h_pos x) (real_le_norm_add_mul_I _ _ (h_pos x))
  · simp only [Matrix.diagonal_apply_ne _ h]
    simp

/-! ## Summary of axiom dependencies

The full proof of the diamagnetic inequality requires 3 axioms:

1. `trotter_product_matrix` — Lie-Trotter product formula
   (BCH series convergence for bounded operators)

2. `diamagnetic_inequality` — the assembled result

3. `heat_kernel_entrywise_nonneg` — exp(-tM) >= 0 entrywise
   (proved in markov-semigroups via Metzler shift)

Plus `m_matrix_inverse_nonneg` for the FK bound connection.

The PROVED components are:
- `laplace_transform_inverse` — M⁻¹ = integral of exp(-tM) dt
  (spectral theorem + scalar Laplace transform)
- `laplace_transform_inverse_complex` — (M+iV)⁻¹ = integral of exp(-t(M+iV)) dt
  (FTC for improper integrals, with 3 helper sorries for: derivative, integrability,
  and limit-to-zero of matrix exponential entries)
- `exp_imaginary_diagonal_entries` — |exp(iV)(x,y)| = delta_{xy}
- `diagonal_mul_entry_norm_le` / `mul_diagonal_entry_norm_le` —
  diagonal contractions
- `sandwich_diagonal_unitary_norm` — U*A*U* preserves norms
- `matrix_mul_entry_norm_le` — entry-wise triangle inequality

**Potential simplification**: In the simultaneously-diagonal case
(after conjugating M to diagonal form), the proof reduces to
a 1D inequality |1/(lambda+iv)| <= 1/lambda, which needs NO axioms beyond
the spectral theorem (already in Mathlib). The gap is proving
that conjugation preserves the entry-wise bound, which requires
heat kernel positivity of M in its ORIGINAL basis. -/

end Pphi2N

end

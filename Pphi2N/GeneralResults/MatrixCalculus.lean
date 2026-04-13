/-
Copyright (c) 2026 Michael R. Douglas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Matrix Calculus: Smoothness of Inverse and log∘det

General results about the differentiability of matrix operations.

## Main results (proved, 0 sorries)

- `contDiffAt_ring_inverse` — Ring.inverse is C∞ at units
- `contDiff_matrix_det` — det is C∞ (from Leibniz formula)
- `contDiffAt_log_det` — log∘det is C∞ at det > 0

## Axioms (2, for derivative formulas)

- `fderiv_log_det` — d(log det A)/dA · H = Tr(A⁻¹H)
- `hessian_log_det` — d²(log det A) · (H,K) = -Tr(A⁻¹HA⁻¹K)

## References

- Mathlib: `analyticAt_inverse`, `AnalyticAt.contDiffAt`
- Magnus-Neudecker, *Matrix Differential Calculus* (2019)
-/

import Mathlib.Analysis.Analytic.Constructions
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.Matrix.Normed
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Pphi2N.GeneralResults.DetContDiff

noncomputable section

namespace MatrixCalculus

variable {n : Type*} [Fintype n] [DecidableEq n]

-- Matrix norm instance (not global in Mathlib — multiple choices exist)
attribute [local instance] Matrix.linftyOpNormedAddCommGroup
attribute [local instance] Matrix.linftyOpNormedRing
attribute [local instance] Matrix.linftyOpNormedAlgebra

/-! ## Ring.inverse is C∞ at units -/

/-- **Ring.inverse is C∞ at any unit in a complete normed algebra.**
Proof: `analyticAt_inverse` (Neumann series) → `AnalyticAt.contDiffAt`. -/
theorem contDiffAt_ring_inverse {𝕜 : Type*} [NontriviallyNormedField 𝕜]
    {A : Type*} [NormedRing A] [NormedAlgebra 𝕜 A] [CompleteSpace A]
    (z : Aˣ) :
    ContDiffAt 𝕜 ⊤ Ring.inverse (z : A) :=
  (analyticAt_inverse z).contDiffAt

/-! ## det is C∞ -/

/-- Each matrix entry is bounded by the linftyOp norm: |A i j| ≤ ‖A‖. -/
private theorem matrix_entry_le_linftyOp (A : Matrix n n ℝ) (i j : n) : ‖A i j‖ ≤ ‖A‖ := by
  simp only [Matrix.linfty_opNorm_def]
  have h1 : ‖A i j‖₊ ≤ ∑ j' : n, ‖A i j'‖₊ :=
    Finset.single_le_sum (f := fun j' => ‖A i j'‖₊) (fun _ _ => zero_le _) (Finset.mem_univ j)
  have h2 : (∑ j' : n, ‖A i j'‖₊) ≤ Finset.univ.sup (fun i' : n => ∑ j' : n, ‖A i' j'‖₊) := by
    apply Finset.le_sup (f := fun i' : n => ∑ j' : n, ‖A i' j'‖₊); exact Finset.mem_univ i
  calc (‖A i j‖ : ℝ) = ↑‖A i j‖₊ := (coe_nnnorm _).symm
    _ ≤ ↑(∑ j' : n, ‖A i j'‖₊) := by exact_mod_cast h1
    _ ≤ ↑(Finset.univ.sup fun i' => ∑ j', ‖A i' j'‖₊) := by exact_mod_cast h2

/-- **The determinant is C∞** with the linftyOp norm.

Proof: Leibniz formula expresses det as a polynomial in matrix entries.
Each entry A(σ(i), i) is a bounded linear functional (norm ≤ 1 by linftyOp),
hence C∞. Products and sums of C∞ functions are C∞. -/
set_option maxHeartbeats 800000 in
theorem contDiff_matrix_det :
    ContDiff ℝ ⊤ (Matrix.det : Matrix n n ℝ → ℝ) := by
  have hdet : (Matrix.det : Matrix n n ℝ → ℝ) = fun A =>
      ∑ σ : Equiv.Perm n, Equiv.Perm.sign σ • ∏ i ∈ Finset.univ, A (σ i) i := by
    ext A; simp [Matrix.det_apply]
  rw [hdet]
  apply ContDiff.sum; intro σ _
  apply ContDiff.const_smul
  apply contDiff_prod; intro i _
  apply IsBoundedLinearMap.contDiff
  exact {
    map_add := fun _ _ => rfl
    map_smul := fun _ _ => rfl
    bound := ⟨1, zero_lt_one, fun A => by
      simp only [one_mul]; exact matrix_entry_le_linftyOp A _ _⟩
  }

/-! ## log ∘ det is C∞ -/

/-- **log ∘ det is C∞ at matrices with positive determinant.** -/
theorem contDiffAt_log_det (A : Matrix n n ℝ) (hA : 0 < A.det) :
    ContDiffAt ℝ ⊤ (fun M : Matrix n n ℝ => Real.log M.det) A :=
  (Real.contDiffAt_log.mpr (ne_of_gt hA)).comp A contDiff_matrix_det.contDiffAt

/-! ## Derivative formulas (Jacobi's formula)

These are standard matrix calculus results. The proofs require
computing fderiv of det (cofactor expansion) and fderiv of A⁻¹
(from the analytic inverse). We axiomatize them for now.

For the σ-effective action: A(σ) = -Δ + diag(σ), so
  dA/dσ_x = E_{xx} (elementary matrix)
  d/dσ_x [½ log det A] = ½ A⁻¹_{xx} = ½ G_{xx}
  d²/dσ_x dσ_y [½ log det A] = -½ (A⁻¹)²_{xy} = -½ G²_{xy}
-/

/-- **Jacobi's formula:** d(log det A) · H = Tr(A⁻¹ H).

Mathematical content: chain rule + cofactor expansion of d(det).
Reference: Magnus-Neudecker (2019), Theorem 8.3. -/
axiom fderiv_log_det (A : Matrix n n ℝ) (hA : 0 < A.det) (H : Matrix n n ℝ) :
    fderiv ℝ (fun M : Matrix n n ℝ => Real.log M.det) A H =
      Matrix.trace (A⁻¹ * H)

/-- **Hessian of log det:** d²(log det A) · (H, K) = -Tr(A⁻¹ H A⁻¹ K).

Mathematical content: differentiate Tr(A⁻¹ H) using d(A⁻¹) = -A⁻¹ · (·) · A⁻¹.
Reference: Magnus-Neudecker (2019), Theorem 8.6. -/
axiom hessian_log_det (A : Matrix n n ℝ) (hA : 0 < A.det) (H K : Matrix n n ℝ) :
    fderiv ℝ (fun M => fderiv ℝ (fun M' : Matrix n n ℝ => Real.log M'.det) M H) A K =
      -Matrix.trace (A⁻¹ * H * A⁻¹ * K)

end MatrixCalculus

end

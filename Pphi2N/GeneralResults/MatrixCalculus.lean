/-
Copyright (c) 2026 Michael R. Douglas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Matrix Calculus: Smoothness of Inverse and log∘det

General results about the differentiability of matrix operations.

## Main results (proved, 0 sorries, 0 axioms)

- `contDiffAt_ring_inverse` — Ring.inverse is C∞ at units
- `contDiff_matrix_det` — det is C∞ (from Leibniz formula)
- `contDiffAt_log_det` — log∘det is C∞ at det > 0
- `fderiv_log_det` — d(log det A)/dA · H = Tr(A⁻¹H) (Jacobi's formula)
- `hessian_log_det` — d²(log det A) · (H,K) = -Tr(A⁻¹HA⁻¹K)

## References

- Mathlib: `analyticAt_inverse`, `AnalyticAt.contDiffAt`
- Magnus-Neudecker, *Matrix Differential Calculus* (2019)
-/

import Mathlib.Analysis.Analytic.Constructions
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.FDeriv.ContinuousAlternatingMap
import Mathlib.Analysis.Calculus.FDeriv.Comp
import Mathlib.Analysis.Calculus.FDeriv.Congr
import Mathlib.Analysis.Calculus.FDeriv.Linear
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.Calculus.LineDeriv.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.Matrix.Normed
import Mathlib.LinearAlgebra.FreeModule.Finite.Matrix
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Matrix.Trace
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

set_option maxHeartbeats 800000 in
/-- **The determinant is C∞** with the linftyOp norm.

Proof: Leibniz formula expresses det as a polynomial in matrix entries.
Each entry A(σ(i), i) is a bounded linear functional (norm ≤ 1 by linftyOp),
hence C∞. Products and sums of C∞ functions are C∞. -/
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

/-! ### Auxiliary lemmas for Jacobi's formula -/

/-- Leibniz bound: |det m| ≤ n! × ∏_i ‖row_i‖ (Pi norm). -/
private lemma det_bound (m : n → n → ℝ) :
    ‖(Matrix.detRowAlternating (n := n) (R := ℝ)) m‖ ≤
      ↑(Fintype.card (Equiv.Perm n)) * ∏ i : n, ‖m i‖ := by
  simp only [Real.norm_eq_abs]
  rw [show (Matrix.detRowAlternating (n := n) (R := ℝ)) m = Matrix.det (m : Matrix n n ℝ) from rfl,
    Matrix.det_apply]
  calc |∑ σ : Equiv.Perm n, Equiv.Perm.sign σ • ∏ i, m (σ i) i|
      ≤ ∑ σ, |Equiv.Perm.sign σ • ∏ i, m (σ i) i| := by
        exact_mod_cast Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _ : Equiv.Perm n, ∏ i : n, ‖m i‖ := by
        apply Finset.sum_le_sum; intro σ _
        have : |Equiv.Perm.sign σ • ∏ i, m (σ i) i| = |∏ i, m (σ i) i| := by
          simp [Units.smul_def, abs_mul]
          rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with h | h <;> simp [h]
        rw [this, Finset.abs_prod]
        calc ∏ i, |m (σ i) i| ≤ ∏ i, ‖m (σ i)‖ :=
              Finset.prod_le_prod (fun _ _ => abs_nonneg _)
                (fun i _ => norm_le_pi_norm (m (σ i)) i)
          _ = ∏ i, ‖m i‖ := Fintype.prod_equiv σ _ _ (fun _ => rfl)
    _ = ↑(Fintype.card (Equiv.Perm n)) * ∏ i : n, ‖m i‖ := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]

/-- det as a ContinuousAlternatingMap (with Pi norm on rows). -/
private def det_cam : (n → ℝ) [⋀^n]→L[ℝ] ℝ :=
  AlternatingMap.mkContinuous _ _ det_bound

/-- Row-linearity of det: det(A.updateRow k v) = ∑_m v_m × adj(A)_{mk}. -/
private lemma det_updateRow_eq_sum_adjugate (A : Matrix n n ℝ) (k : n) (v : n → ℝ) :
    (A.updateRow k v).det = ∑ m : n, v m * A.adjugate m k := by
  change (Matrix.detRowAlternating (n := n) (R := ℝ)).toMultilinearMap
    (Function.update A k v) = _
  conv_lhs => rw [show v = ∑ m ∈ Finset.univ, v m • (Pi.single m (1 : ℝ) : n → ℝ) from by
    ext j; simp [Finset.sum_apply, Pi.single_apply]]
  rw [(Matrix.detRowAlternating (n := n) (R := ℝ)).toMultilinearMap.map_update_sum]
  congr 1; ext m
  rw [(Matrix.detRowAlternating (n := n) (R := ℝ)).toMultilinearMap.map_update_smul]
  have : (Matrix.detRowAlternating (n := n) (R := ℝ)).toMultilinearMap
    (Function.update A k (Pi.single m 1)) = A.adjugate m k := by
    show (A.updateRow k (Pi.single m 1)).det = _
    exact (Matrix.adjugate_apply A m k).symm
  simp [this]

/-- ∑_k det(A.updateRow k (H k)) = Tr(adj(A) × H). -/
private lemma sum_det_updateRow_eq_trace (A H : Matrix n n ℝ) :
    ∑ k : n, (A.updateRow k (H k)).det = Matrix.trace (A.adjugate * H) := by
  simp_rw [det_updateRow_eq_sum_adjugate]
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply]
  rw [Finset.sum_comm]
  congr 1; ext k; congr 1; ext m; ring

/-- HasDerivAt for det(A + tH) at t=0, via multilinear (alternating map) derivative. -/
private lemma det_hasDerivAt_line (A H : Matrix n n ℝ) :
    HasDerivAt (fun t : ℝ => (A + t • H).det)
      (∑ k : n, (A.updateRow k (H k)).det) 0 := by
  have hfda := det_cam.hasFDerivAt (show n → n → ℝ from A)
  have hla := hfda.hasLineDerivAt (show n → n → ℝ from H)
  have hld : (det_cam.linearDeriv (show n → n → ℝ from A) (show n → n → ℝ from H) : ℝ) =
      ∑ k : n, (A.updateRow k (H k)).det := by
    show det_cam.toContinuousMultilinearMap.linearDeriv A H = _
    rw [ContinuousMultilinearMap.linearDeriv_apply]; rfl
  simp only [HasLineDerivAt] at hla
  rw [hld] at hla
  convert hla using 1

/-- Tr(adj(A) × H) / det A = Tr(A⁻¹ × H) when det A > 0. -/
private lemma trace_adjugate_div_det (A H : Matrix n n ℝ) (hA : 0 < A.det) :
    (A.adjugate * H).trace / A.det = (A⁻¹ * H).trace := by
  rw [Matrix.inv_def, smul_mul_assoc, Matrix.trace_smul, Ring.inverse_eq_inv, smul_eq_mul]
  field_simp

/-- **Jacobi's formula:** d(log det A) · H = Tr(A⁻¹ H).

Proof: chain rule (log ∘ det) + multilinear derivative of det + cofactor expansion.
Reference: Magnus-Neudecker (2019), Theorem 8.3. -/
theorem fderiv_log_det (A : Matrix n n ℝ) (hA : 0 < A.det) (H : Matrix n n ℝ) :
    fderiv ℝ (fun M : Matrix n n ℝ => Real.log M.det) A H =
      Matrix.trace (A⁻¹ * H) := by
  -- fderiv = lineDeriv (since log ∘ det is C∞ at det > 0)
  have hdiff : DifferentiableAt ℝ (fun M : Matrix n n ℝ => Real.log M.det) A :=
    (contDiffAt_log_det A hA).differentiableAt (by simp)
  rw [← hdiff.lineDeriv_eq_fderiv]
  simp only [lineDeriv]
  -- Chain rule: deriv (log ∘ det along line) = (deriv det) / det A
  have hdet := det_hasDerivAt_line A H
  have hne : (A + (0 : ℝ) • H).det ≠ 0 := by simp; exact ne_of_gt hA
  have hlog := hdet.log hne
  rw [hlog.deriv]
  -- Simplify and use Tr(adj A * H) / det A = Tr(A⁻¹ * H)
  simp only [zero_smul, add_zero]
  rw [sum_det_updateRow_eq_trace A H]
  exact trace_adjugate_div_det A H hA

/-! ### Auxiliary CLMs for Hessian computation -/

/-- Trace as a continuous linear map (finite-dimensional, hence bounded). -/
private def traceCLM : Matrix n n ℝ →L[ℝ] ℝ :=
  { Matrix.traceLinearMap n ℝ ℝ with
    cont := LinearMap.continuous_of_finiteDimensional _ }

/-- Right-multiplication by H as a continuous linear map. -/
private def mulRightCLM (H : Matrix n n ℝ) : Matrix n n ℝ →L[ℝ] Matrix n n ℝ :=
  (ContinuousLinearMap.mul ℝ (Matrix n n ℝ)).flip H

set_option maxHeartbeats 400000 in
/-- **Hessian of log det:** d²(log det A) · (H, K) = -Tr(A⁻¹ H A⁻¹ K).

Proof: The first derivative is Tr(A⁻¹ H) by `fderiv_log_det`. We show
M ↦ fderiv(log∘det)(M)(H) agrees with M ↦ Tr(M⁻¹ H) in a neighborhood of A
(where det > 0), then differentiate the latter using the chain rule:
- Ring.inverse is analytic at units, with fderiv K ↦ -A⁻¹ K A⁻¹ (`fderiv_inverse`)
- Right-multiplication by H and trace are CLMs (fderiv = identity)
- Trace cyclicity: Tr(A⁻¹ K A⁻¹ H) = Tr(A⁻¹ H A⁻¹ K).

Reference: Magnus-Neudecker (2019), Theorem 8.6. -/
theorem hessian_log_det (A : Matrix n n ℝ) (hA : 0 < A.det) (H K : Matrix n n ℝ) :
    fderiv ℝ (fun M => fderiv ℝ (fun M' : Matrix n n ℝ => Real.log M'.det) M H) A K =
      -Matrix.trace (A⁻¹ * H * A⁻¹ * K) := by
  -- Step 1: {M | det M > 0} is an open neighborhood of A; fderiv_log_det applies there
  have hdet_cont : Continuous (Matrix.det : Matrix n n ℝ → ℝ) :=
    contDiff_matrix_det.continuous
  have hnh : ∀ᶠ M in nhds A, (0 : ℝ) < M.det :=
    hdet_cont.continuousAt.eventually (IsOpen.eventually_mem isOpen_Ioi hA)
  have heq : (fun M => (fderiv ℝ (fun M' => Real.log M'.det) M) H) =ᶠ[nhds A]
      (fun M => Matrix.trace (M⁻¹ * H)) :=
    hnh.mono (fun M hM => fderiv_log_det M hM H)
  -- Step 2: Replace outer fderiv target using EventuallyEq
  rw [Filter.EventuallyEq.fderiv_eq heq]
  -- Step 3: Rewrite M⁻¹ as Ring.inverse M (needed for fderiv_inverse)
  have hinv_eq : (fun M : Matrix n n ℝ => Matrix.trace (M⁻¹ * H)) =
      (fun M => Matrix.trace (Ring.inverse M * H)) := by
    ext M; rw [Matrix.nonsing_inv_eq_ringInverse]
  rw [hinv_eq]
  -- Step 4: Decompose as CLM ∘ Ring.inverse
  have hU : IsUnit A := (Matrix.isUnit_iff_isUnit_det A).mpr (isUnit_iff_ne_zero.mpr hA.ne')
  let u := hU.unit
  have hAu : (↑u : Matrix n n ℝ) = A := by simp [u]
  let L := traceCLM.comp (mulRightCLM H)
  have hfun : (fun M => Matrix.trace (Ring.inverse M * H)) = (↑L) ∘ Ring.inverse := by
    ext M
    simp only [L, ContinuousLinearMap.comp_apply, traceCLM, ContinuousLinearMap.coe_mk',
      Matrix.traceLinearMap_apply, mulRightCLM, ContinuousLinearMap.flip_apply,
      ContinuousLinearMap.mul_apply', Function.comp_def]
  rw [hfun]
  have hdiff_inv : DifferentiableAt ℝ Ring.inverse A := by
    rw [← hAu]; exact (analyticAt_inverse u).differentiableAt
  -- Step 5: Chain rule + CLM fderiv
  rw [fderiv_comp A L.differentiableAt hdiff_inv, ContinuousLinearMap.fderiv L]
  simp only [ContinuousLinearMap.comp_apply]
  -- Step 6: Derivative of Ring.inverse at A
  rw [← hAu, fderiv_inverse u, ContinuousLinearMap.neg_apply,
    ContinuousLinearMap.mulLeftRight_apply]
  have huinv : (↑u⁻¹ : Matrix n n ℝ) = A⁻¹ := by
    rw [← Ring.inverse_unit u, ← Matrix.nonsing_inv_eq_ringInverse, hAu]
  -- Step 7: Unfold L and simplify
  simp only [L, ContinuousLinearMap.comp_apply, traceCLM, ContinuousLinearMap.coe_mk',
    Matrix.traceLinearMap_apply, mulRightCLM, ContinuousLinearMap.flip_apply,
    ContinuousLinearMap.mul_apply', map_neg]
  rw [show (↑u : Matrix n n ℝ)⁻¹ = A⁻¹ from by rw [hAu], huinv]
  -- Step 8: Trace cyclicity: Tr(A⁻¹KA⁻¹H) = Tr(A⁻¹HA⁻¹K)
  congr 1
  rw [Matrix.mul_assoc (A⁻¹ * K) A⁻¹ H, Matrix.mul_assoc (A⁻¹ * H) A⁻¹ K]
  exact Matrix.trace_mul_comm (A⁻¹ * K) (A⁻¹ * H)

end MatrixCalculus

end

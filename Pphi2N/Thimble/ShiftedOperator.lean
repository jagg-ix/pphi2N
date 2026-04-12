/-
Copyright (c) 2026 Michael R. Douglas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# The Shifted Operator on the Thimble

On the shifted contour σ = u + iv_*, the φ-operator decomposes as:
  -Δ + 2iσz = (-Δ + m₀²) + 2iuz
where -2v_*z = m₀² (the gap equation). The real part -Δ + m₀²
is positive definite with spectral gap m₀², enabling the FK bound.

## Main results

- `ShiftedOperatorData` — bundles the operator decomposition
- `real_part_psd` — Re(-Δ + m₀² + 2iuz) = -Δ + m₀² ≥ m₀²
- `spectral_gap` — ⟨w, (-Δ+m₀²)w⟩ ≥ m₀²‖w‖² (from LatticeOperator)

## References

- docs/mass-gap-v3.tex, Section 8.2 (operator on the shifted contour)
-/

import Pphi2N.Thimble.GapEquation
import Pphi2N.MassGap.LatticeOperator

noncomputable section

open Matrix Finset

namespace Pphi2N

/-! ## The shifted operator decomposition

On the shifted contour σ(x) = u(x) + iv_*, the HS operator is:
  -Δ + 2i(u + iv_*)z = -Δ + 2iuz - 2v_*z = -Δ + m₀² + 2iuz
The real part M = -Δ + m₀² has spectral gap m₀² > 0.
The imaginary part V = 2uz is a real diagonal perturbation. -/

/-- Data for the shifted operator on a finite lattice.

Bundles the lattice Laplacian, gap equation, and the decomposition
of the operator into real (M) and imaginary (V) parts. -/
structure ShiftedOperatorData (Λ : Type*) [Fintype Λ] [DecidableEq Λ] where
  /-- Gap equation data -/
  gap : GapEquationData
  /-- The lattice Laplacian (as a PSD matrix) -/
  laplacian : Matrix Λ Λ ℝ
  /-- Laplacian is PSD -/
  laplacian_psd : laplacian.PosSemidef

namespace ShiftedOperatorData

variable {Λ : Type*} [Fintype Λ] [DecidableEq Λ]
variable (D : ShiftedOperatorData Λ)

/-- The real part of the shifted operator: M = -Δ + m₀²I -/
def realPart : Matrix Λ Λ ℝ :=
  D.laplacian + D.gap.m0_sq • (1 : Matrix Λ Λ ℝ)

/-- **Spectral gap of the real part**: ⟨w, Mw⟩ ≥ m₀²‖w‖².

This is the key bound enabling the FK estimate: the operator
M = -Δ + m₀² has positive real part with gap m₀² > 0. -/
theorem realPart_spectral_gap (w : Λ → ℝ) :
    D.gap.m0_sq * (w ⬝ᵥ w) ≤ w ⬝ᵥ (D.realPart *ᵥ w) := by
  unfold realPart
  -- M = Δ + m₀²·I, so ⟨w, Mw⟩ = ⟨w, Δw⟩ + m₀²⟨w,w⟩ ≥ m₀²⟨w,w⟩
  -- since ⟨w, Δw⟩ ≥ 0 (Laplacian PSD)
  -- This is psd_add_scalar_bound from LatticeOperator.lean
  exact psd_add_scalar_bound D.laplacian D.laplacian_psd D.gap.m0_sq D.gap.hm0_sq_pos w

/-- The real part is positive definite (has positive spectral gap). -/
-- Helper: w ≠ 0 implies w ⬝ᵥ w > 0 for functions on a Fintype.
private theorem dotProduct_self_pos_of_ne_zero [Nonempty Λ]
    (w : Λ → ℝ) (hw : w ≠ 0) :
    0 < w ⬝ᵥ w := by
  simp only [dotProduct]
  -- w ≠ 0 means ∃ i, w i ≠ 0
  have ⟨i, hi⟩ : ∃ i, w i ≠ 0 := by
    by_contra h
    push_neg at h
    exact hw (funext h)
  calc 0 < w i * w i := mul_self_pos.mpr hi
    _ ≤ ∑ j ∈ Finset.univ, w j * w j :=
        Finset.single_le_sum (fun j _ => mul_self_nonneg (w j))
          (Finset.mem_univ i)

theorem realPart_pos_def [Nonempty Λ] (w : Λ → ℝ) (hw : w ≠ 0) :
    0 < w ⬝ᵥ (D.realPart *ᵥ w) := by
  have h_gap := D.realPart_spectral_gap w
  have h_dot_pos := dotProduct_self_pos_of_ne_zero w hw
  linarith [mul_pos D.gap.hm0_sq_pos h_dot_pos]

/-- The imaginary part of the shifted operator: V(u) = diag(2u/√N).
This is a real diagonal matrix (multiplication by 2u(x)/√N). -/
def imaginaryPart (u : Λ → ℝ) : Matrix Λ Λ ℝ :=
  Matrix.diagonal (fun x => 2 * u x * D.gap.z)

/-- The full shifted operator as a complex matrix:
  A(u) = M + iV(u) = (-Δ + m₀²) + i·diag(2u/√N) -/
def shiftedOperator (u : Λ → ℝ) : Matrix Λ Λ ℂ :=
  D.realPart.map (↑· : ℝ → ℂ) +
  Complex.I • (D.imaginaryPart u).map (↑· : ℝ → ℂ)

/-- The FK bound structure: for each u, the shifted operator has
real part M ≥ m₀² and imaginary part V = 2uz.

This is the data needed by the resolvent_complex_bound axiom
to conclude |A⁻¹(x,y)| ≤ M⁻¹(x,y). -/
theorem shifted_operator_has_gap (u : Λ → ℝ) :
    -- The real part of the shifted operator has spectral gap m₀²
    ∀ w : Λ → ℝ, D.gap.m0_sq * (w ⬝ᵥ w) ≤ w ⬝ᵥ (D.realPart *ᵥ w) :=
  D.realPart_spectral_gap

end ShiftedOperatorData

end Pphi2N

end

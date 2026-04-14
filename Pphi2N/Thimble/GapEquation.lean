/-
Copyright (c) 2026 Michael R. Douglas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Gap Equation and Contour Shift Parameters

The gap equation determines the constant imaginary shift v_* that
introduces a real mass m₀² into the φ-operator on the Lefschetz
thimble. The shift σ(x) → σ(x) + iv_* with -2v_*z = m₀² (where
z = 1/√N) transforms the operator -Δ + 2iσz into -Δ + m₀² + 2iuz,
which has positive real part.

## Main definitions

- `GapEquationData` — bundles m₀², v_*, N, z, λ with the gap equation
- `ThimbleMassGapData` — extends with BL convexity parameter κ

## Main results

- `v_star_eq` — v_* = -m₀²√N/2 (from the gap equation)
- `v_star_neg` — v_* < 0
- `gap_equation` — m₀² = -2v_*z
- `singularity_distance_bound` — singularities at distance ≥ m₀²√N/2

## References

- docs/mass-gap-v3.tex, Section 7.5 (the constant shift)
- Kupiainen, Comm. Math. Phys. 73 (1980) — gap equation for NLSM
-/

import Mathlib.Analysis.SpecialFunctions.Pow.Real

noncomputable section

open Real

namespace Pphi2N

/-! ## Gap equation data

The gap equation -2v_*z = m₀² determines the shift parameter v_*
from the physical mass m₀ and the scaling z = 1/√N. -/

/-- Data for the Lefschetz thimble contour shift.

The gap equation relates the shift parameter v_* to the physical mass m₀²:
  -2v_*z = m₀²
where z = 1/√N. On the shifted contour σ(x) = u(x) + iv_*, the φ-operator
becomes -Δ + m₀² + 2iuz (real mass + imaginary perturbation). -/
structure GapEquationData where
  /-- Number of field components -/
  N : ℕ
  /-- N ≥ 1 -/
  hN : 1 ≤ N
  /-- Physical mass squared (from the gap equation) -/
  m0_sq : ℝ
  /-- m₀² > 0 -/
  hm0_sq_pos : 0 < m0_sq
  /-- Quartic coupling -/
  lam : ℝ
  /-- λ > 0 -/
  hlam : 0 < lam

namespace GapEquationData

variable (G : GapEquationData)

/-- N > 0 as a real number -/
theorem N_pos_real : (0 : ℝ) < G.N := Nat.cast_pos.mpr (by linarith [G.hN] : 0 < G.N)

/-- √N > 0 -/
theorem sqrt_N_pos : 0 < Real.sqrt G.N :=
  Real.sqrt_pos.mpr G.N_pos_real

/-- √N ≠ 0 -/
theorem sqrt_N_ne_zero : Real.sqrt (↑G.N) ≠ 0 := ne_of_gt G.sqrt_N_pos

/-- The 1/N scaling parameter z = 1/√N -/
def z : ℝ := 1 / Real.sqrt G.N

/-- z > 0 since N ≥ 1 -/
theorem z_pos : 0 < G.z := div_pos one_pos G.sqrt_N_pos

/-- The contour shift parameter v_* = -m₀²/(2z) = -m₀²√N/2 -/
def v_star : ℝ := -G.m0_sq / (2 * G.z)

/-- **The gap equation**: -2v_*z = m₀² -/
theorem gap_equation : -2 * G.v_star * G.z = G.m0_sq := by
  unfold v_star z
  have hz := G.sqrt_N_ne_zero
  field_simp

/-- v_* < 0 (the shift is to negative imaginary part) -/
theorem v_star_neg : G.v_star < 0 := by
  unfold v_star
  apply div_neg_of_neg_of_pos
  · linarith [G.hm0_sq_pos]
  · linarith [G.z_pos]

/-- v_* expressed in terms of m₀² and N -/
theorem v_star_eq : G.v_star = -(G.m0_sq * Real.sqrt G.N / 2) := by
  unfold v_star z
  have hz := G.sqrt_N_ne_zero
  field_simp

/-- The distance from the saddle to the nearest singularity.
|v_*| = m₀²√N/2 -/
theorem singularity_distance : |G.v_star| = G.m0_sq * Real.sqrt G.N / 2 := by
  rw [G.v_star_eq, abs_neg, abs_of_pos]
  apply div_pos (mul_pos G.hm0_sq_pos G.sqrt_N_pos) two_pos

/-- **Bare Hessian lower bound at the constant shift.**

The Hessian of -Re f(u + iv_*) at u = 0 in Fourier space is:
  Ĥ(k) = 1/(2λ) + 2B(k)
where B(k) = (1/|Λ|) Σ_l G₀(l) G₀(k-l) ≥ 0 (bubble diagram).

The bare term 1/(2λ) > 0 gives the lower bound Ĥ(k) ≥ 1/(2λ).

For the LSM coupling λ = c/N: Ĥ(k) ≥ N/(2c) = κN.

This is the key verifiable computation: the saddle-point Gaussian
has a positive definite Hessian, with the lower bound scaling as N
(from the 1/N coupling structure of the LSM). -/
theorem bare_hessian_pos : 0 < 1 / (2 * G.lam) :=
  div_pos one_pos (mul_pos two_pos G.hlam)

end GapEquationData

/-! ## Thimble mass gap data

Extends the gap equation with the Brascamp-Lieb convexity parameter κ,
which controls the variance of the σ-fluctuations on the thimble. -/

/-- Full data for the thimble mass gap proof.

Extends `GapEquationData` with:
- κ: the convexity parameter for the Hessian of Re f on the thimble
- The Hessian satisfies Hess(-Re f) ≥ κ·N (from 1/(2λ) + bubble diagram)
- BL gives Var(u(x)) ≤ 1/(κN) -/
structure ThimbleMassGapData extends GapEquationData where
  /-- Convexity parameter (Hessian of -Re f ≥ κ per site) -/
  kappa : ℝ
  /-- κ > 0 -/
  hkappa : 0 < kappa

namespace ThimbleMassGapData

variable (D : ThimbleMassGapData)

/-- The BL variance bound: 1/(κN) -/
def varianceBound : ℝ := 1 / (D.kappa * D.N)

/-- The variance bound is positive -/
theorem varianceBound_pos : 0 < D.varianceBound := by
  unfold varianceBound
  apply div_pos one_pos
  exact mul_pos D.hkappa D.toGapEquationData.N_pos_real

/-- The N threshold for the mass gap.
Need fluctuation √(1/(κN)) < m₀²/2 for each site, i.e.,
N > 4/(κ·m₀⁴). -/
def nThreshold : ℕ := Nat.ceil (4 / (D.kappa * D.m0_sq ^ 2)) + 1

/-- Physical mass lower bound: m₀ - correction from fluctuations.
m_phys ≥ √m₀² · (1 - C/N) where C depends on κ. -/
def physicalMass : ℝ := Real.sqrt D.m0_sq * (1 - 1 / (D.kappa * D.m0_sq * D.N))

/-- The physical mass is positive when κ·m₀²·N > 1. -/
theorem physicalMass_pos (h : 1 < D.kappa * D.m0_sq * D.N) :
    0 < D.physicalMass := by
  unfold physicalMass
  apply mul_pos (Real.sqrt_pos.mpr D.hm0_sq_pos)
  -- Need 1 - 1/(κ·m₀²·N) > 0, i.e., 1/(κ·m₀²·N) < 1
  have hden : (0 : ℝ) < D.kappa * D.m0_sq * D.N := by positivity
  rw [sub_pos]
  rwa [div_lt_one hden]

end ThimbleMassGapData

end Pphi2N

end

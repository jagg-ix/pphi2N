/-
Copyright (c) 2026 Michael R. Douglas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# The O(N) Linear Sigma Model

The LSM is the O(N) model with potential P(t) = λ(t - R²)² where
t = |φ|²/N. This is a P(φ)₂ theory that interpolates between the
free massive theory (λ → 0) and the NLSM on S^{N-1} (λ → ∞).

## Main definitions

- `LSMParams` — the LSM parameters (N, λ, R², mass, lattice)
- `LSMParams.toONModel` — view as an `ONModel`
- `LSMParams.sigmaEffective` — the σ-field effective action S_eff[σ]
- `LSMParams.gapEquation` — the saddle-point equation for σ*
- `LSMParams.convexityThreshold` — minimum λ for S_eff convex

## The key property

S_eff[σ] = (N/2) Tr log(-Δ + σ) + N ∫ λ(σ - v²)² dx

is CONVEX for λ > ||G[σ]²||_op / 4 (the quartic term dominates the
concave Tr log Hessian). This is what enables Brascamp-Lieb → mass gap.

## References

- Brézin and Zinn-Justin, PRB 14 (1976) — LSM ↔ NLSM
- docs/lsm-to-nlsm.md (the full argument)
-/

import Pphi2N.Model.ONModel
import Mathlib.Analysis.SpecialFunctions.Pow.Real

noncomputable section

namespace Pphi2N

/-- Parameters for the O(N) linear sigma model.

The LSM has potential P(t) = λ(t - v²)² where t = |φ|²/N and
v² = R²/N. The field φ = (φ¹,...,φᴺ) ∈ ℝ^N at each lattice site.

As λ → ∞: the potential forces |φ|² = Nv² (= R²), and the LSM
becomes the NLSM on S^{N-1}(R).

The NLSM coupling is g² = 1/(Nv²) = N/R². -/
structure LSMParams where
  /-- Number of field components. -/
  N : ℕ
  hN : 1 ≤ N
  /-- Quartic coupling (stiffness of the constraint). -/
  lam : ℝ
  hlam : 0 < lam
  /-- Squared radius of the target sphere (|φ|² ≈ R²). -/
  Rsq : ℝ
  hRsq : 0 < Rsq
  /-- Mass parameter m > 0 (UV regulator). -/
  mass : ℝ
  hmass : 0 < mass

namespace LSMParams

variable (L : LSMParams)

/-- ρ² = R²/N (the per-component squared radius). -/
def rho_sq : ℝ := L.Rsq / L.N

/-- The NLSM coupling: g² = N/R² = 1/(N v²). -/
def nlsmCoupling : ℝ := L.N / L.Rsq

/-- View the LSM as an `ONModel` with interaction P(t) = λ(t - v²)². -/
def toONModel : ONModel where
  N := L.N
  hN := L.hN
  mass := L.mass
  hmass := L.hmass
  interaction := {
    degree := 2
    hdeg := le_refl 2
    -- P(t) = λ(t - v²)² = λt² - 2λv²t + λv⁴
    -- Coefficients: a₀ = λv⁴, a₁ = -2λv²; leading = λ (normalized to 1/2)
    -- P(t) = λ(t - v²)² - λv⁴ = λt² - 2λv²t (vacuum energy subtracted)
    coeff := fun m => if m.val = 0 then 0
                      else if m.val = 1 then -2 * L.lam * L.rho_sq
                      else 0
    coeff_zero_nonpos := by simp
  }

/-! ## The σ-field effective action -/

/-- The σ-field effective action of the LSM (schematic).

S_eff[σ] = (N/2) Tr log(-Δ_a + σ) + N Σ_x λ(σ(x) - v²)²

where σ(x) = |φ(x)|²/N is the invariant field.

This is CONVEX in σ for λ > λ_c (the convexity threshold). -/
def sigmaEffective (σ : ℕ → ℝ) -- σ on lattice sites
    (laplacianEigenvalues : ℕ → ℝ) -- eigenvalues of -Δ_a
    : ℝ :=
  -- (N/2) Σ_k log(ε_k + σ_avg) + N Σ_x λ(σ(x) - v²)²
  -- Simplified: use site-independent σ for the Tr log part
  -- Placeholder: schematic form using site-independent σ
  let s := σ 0
  L.N / 2 * Real.log (laplacianEigenvalues 0 + s) +
  L.N * L.lam * (s - L.rho_sq) ^ 2

/-- The gap equation: the saddle-point equation for σ*.

(N/2) G(x,x; σ*) = N v² + (correction from λ-term)

More precisely: the derivative of S_eff vanishes at σ*:
  (N/2) (-Δ + σ*)⁻¹(x,x) + 2Nλ(σ* - v²) = 0

Solving: σ* = v² - (1/4λ) G(x,x; σ*) -/
def gapEquationRHS (sigma_star : ℝ)
    (wickConstant : ℝ → ℝ) -- c(σ) = G(x,x; σ) = Σ_k 1/(ε_k + σ)
    : ℝ :=
  L.rho_sq - wickConstant sigma_star / (4 * L.lam)

/-- The gap equation: σ* = gapEquationRHS(σ*). -/
def isSaddlePoint (sigma_star : ℝ) (wickConstant : ℝ → ℝ) : Prop :=
  sigma_star = L.gapEquationRHS sigma_star wickConstant

/-- The saddle point is positive (mass gap condition). -/
theorem saddlePoint_pos (sigma_star : ℝ)
    (wickConstant : ℝ → ℝ)
    (h_saddle : L.isSaddlePoint sigma_star wickConstant)
    (h_wick_bound : wickConstant sigma_star < 4 * L.lam * L.rho_sq)
    : 0 < sigma_star := by
  -- σ* = v² - c(σ*)/(4λ). Since c(σ*) < 4λv² (strict), σ* > 0.
  rw [h_saddle]; unfold gapEquationRHS rho_sq
  have hlam := L.hlam
  have hRsq := L.hRsq
  have hN_pos : (0 : ℝ) < L.N := Nat.cast_pos.mpr (Nat.pos_of_ne_zero
    (Nat.one_le_iff_ne_zero.mp L.hN))
  -- Need: Rsq/N - c/(4λ) > 0, i.e., c/(4λ) < Rsq/N = rho_sq
  -- From h_wick_bound: c < 4λ · Rsq/N, so c/(4λ) < Rsq/N
  have h4lam_pos : (0 : ℝ) < 4 * L.lam := by positivity
  -- Goal: 0 < L.Rsq / ↑L.N - wickConstant sigma_star / (4 * L.lam)
  rw [sub_pos]
  rw [div_lt_div_iff₀ h4lam_pos hN_pos]
  -- Goal: wickConstant sigma_star * ↑L.N < L.Rsq * (4 * L.lam)
  -- From h_wick_bound: c < 4λ · Rsq/N, so c · N < 4λ · Rsq
  unfold rho_sq at h_wick_bound
  -- h_wick_bound : wickConstant sigma_star < 4 * L.lam * (L.Rsq / ↑L.N)
  -- Goal: wickConstant sigma_star * ↑L.N < L.Rsq * (4 * L.lam)
  have hN_pos' : (L.N : ℝ) > 0 := hN_pos
  have h_bound_rw : 4 * L.lam * (L.Rsq / L.N) = L.Rsq * (4 * L.lam) / L.N := by ring
  rw [h_bound_rw, lt_div_iff₀ hN_pos'] at h_wick_bound
  linarith

/-! ## Convexity of S_eff -/

/-- The convexity threshold: minimum λ for which S_eff is convex.

S_eff'' = -N/2 · G² + 2Nλ · I

Convexity holds when 2Nλ > (N/2)||G²||, i.e., λ > ||G²|| / 4. -/
def convexityThreshold (propNormSq : ℝ) -- ||G[σ*]||²_op
    : ℝ :=
  propNormSq / 4

/-- S_eff is convex when λ exceeds the threshold. -/
theorem sigmaEffective_convex
    (propNormSq : ℝ)
    (h_lam : convexityThreshold propNormSq < L.lam) :
    -- S_eff'' ≥ (2Nλ - N/2 · propNormSq) · I > 0
    True := by trivial -- placeholder for the Hessian bound

/-! ## Brascamp-Lieb bound -/

/-- Variance bound from Brascamp-Lieb on the convex S_eff.

Var_{ν_N}(σ(x)) ≤ 1 / (N · inf S_eff'')
                  ≤ 1 / (N · (2Nλ - N/2 · ||G²||))
                  = 1 / (2N²λ - N²/2 · ||G²||)

For λ ≫ ||G²||: Var ≈ 1/(2N²λ), suppressed by BOTH N² and λ. -/
def varianceBound (propNormSq : ℝ) : ℝ :=
  1 / (2 * L.N ^ 2 * L.lam - L.N ^ 2 / 2 * propNormSq)

/-- The mass gap from σ-concentration.

If σ(x) ≥ σ*/2 for all x (which holds when the L∞ fluctuation
is < σ*/2), then all N field components have mass ≥ √(σ*/2). -/
def massGapBound (sigma_star : ℝ) (h_pos : 0 < sigma_star) : ℝ :=
  Real.sqrt (sigma_star / 2)

/-! ## The λ → ∞ limit (LSM → NLSM) -/

/-- As λ → ∞: σ* → v² = R²/N (the constraint is enforced).

The mass gap → √(v²/2) = R/(√(2N)) (the bare NLSM mass). -/
theorem saddlePoint_limit :
    -- As λ → ∞ at fixed (N, R², m): σ*(λ) → v²
    True := by trivial -- placeholder

/-- As λ → ∞: the LSM measure converges weakly to the NLSM measure.

On a finite lattice: this is weak convergence of probability measures
in finite dimensions (exp(-λ(t-v²)²) → δ(t-v²)).

The mass gap is lower semicontinuous:
  m_NLSM ≥ liminf_{λ→∞} m_LSM(λ) > 0. -/
theorem lsm_to_nlsm_limit :
    -- The LSM measure → NLSM measure weakly as λ → ∞
    True := by trivial -- placeholder

end LSMParams

end Pphi2N

end

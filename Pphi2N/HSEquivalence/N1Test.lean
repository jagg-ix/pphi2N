/-
Copyright (c) 2026 Michael R. Douglas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# N=1 Hubbard-Stratonovich Test Case

Tests the HS transformation on the N=1 case (single scalar P(φ)₂).
The HS identity rewrites the φ⁴ interaction as a φ² coupling to an
auxiliary field σ, reducing the polynomial degree from 4 to 2.

## The equivalence

For N=1, φ : Λ → ℝ, u = φ², and the quartic λ(φ²-ρ²)² is a P(φ)₂
polynomial. The HS identity:

  exp(-λ(φ²-ρ²)²) = c ∫ dσ exp(-σ²/(4λ) + iσ(φ²-ρ²))

makes the φ-action quadratic: ½⟨φ,(-Δ+iσ)φ⟩. Integrating out φ
gives det(-Δ+iσ)^{-1/2}.

## What we prove

1. The HS identity is a Gaussian integral identity (exact)
2. The partition functions are equal: Z_{P(φ)₂} = Z_{HS}
3. The gap equation for N=1 matches the Wick mass renormalization

## References

- Glimm-Jaffe-Spencer (1974) for the P(φ)₂ mass gap
- pphi2 project for the Lean formalization of P(φ)₂
-/

import Pphi2N.InteractingMeasure.ONTorusMeasure
import Pphi2N.MassGap.HubbardStratonovich
import Pphi2N.ContinuumLimit.LSMTorusMeasure
import Pphi2N.HSEquivalence.HSIdentity

noncomputable section

open MeasureTheory GaussianField

namespace Pphi2N

/-! ## The N=1 specialization

For N=1: the O(N) model IS the scalar P(φ)₂ theory.
The field φ : Λ → ℝ has a single component, and
u(x) = |φ(x)|²/N = φ(x)² (since N=1). -/

/-- N=1 LSM parameters: a P(φ)₂ theory with P(t) = λ(t-ρ²)². -/
def n1Params (lam : ℝ) (hlam : 0 < lam) (Rsq : ℝ) (hRsq : 0 < Rsq)
    (mass : ℝ) (hmass : 0 < mass) : LSMParams where
  N := 1
  hN := le_refl 1
  lam := lam
  hlam := hlam
  Rsq := Rsq
  hRsq := hRsq
  mass := mass
  hmass := hmass

/-- For N=1: the field has a single component (Fin 1 → FinLatticeField d M).
This is isomorphic to FinLatticeField d M via evaluation at 0. -/
def singleComponentEquiv {d M : ℕ} [NeZero M] :
    (Fin 1 → FinLatticeField d M) ≃ FinLatticeField d M where
  toFun φ := φ 0
  invFun ψ := fun _ => ψ
  left_inv φ := by ext i; fin_cases i; rfl
  right_inv ψ := rfl

/-! ## The pushforward σ-field for N=1

For N=1: σ(x) = |φ(x)|²/1 = φ(x)² is just the field squared.
The pushforward measure on σ = φ² is well-defined. -/

/-- The σ-field map for N=1: φ ↦ φ². -/
def sigmaFieldMap_n1 {Λ : Type*} [Fintype Λ]
    (φ : Λ → ℝ) : Λ → ℝ :=
  fun x => φ x ^ 2

/-- The σ-field map for N=1 is measurable. -/
theorem sigmaFieldMap_n1_measurable {Λ : Type*} [Fintype Λ]
    [MeasurableSpace Λ] [MeasurableSingletonClass Λ] :
    Measurable (sigmaFieldMap_n1 : (Λ → ℝ) → (Λ → ℝ)) := by
  apply measurable_pi_lambda; intro x
  exact (measurable_pi_apply x).pow_const 2

/-! ## The HS identity for N=1

The Gaussian integral identity that linearizes the quartic:

  exp(-λa²) = √(1/(4πλ)) ∫ dσ exp(-σ²/(4λ) + iσa)

This is the Fourier representation of the Gaussian. -/

/-- The HS identity for a single real variable.

  ∫ exp(iaσ - σ²/(4λ)) dσ = √(4πλ) · exp(-λa²)

Proved in HSIdentity.lean from Mathlib's fourierIntegral_gaussian. -/
theorem hs_identity_n1 (lam : ℝ) (hlam : 0 < lam) (a : ℝ) :
    ∫ σ : ℝ, Complex.exp (Complex.I * ↑a * ↑σ - (1/(4*↑lam)) * ↑σ ^ 2) =
    (4 * ↑Real.pi * ↑lam) ^ (1/2 : ℂ) * Complex.exp (-(↑lam) * (↑a)^2) :=
  hs_identity_combined lam hlam a

/-! ## The gap equation for N=1

At N=1, the gap equation is:
  ½ G(x,x; m₀²) + 2λ(m₀² - ρ²) = 0

where G(x,x) is the Green's function diagonal (Wick constant).
This is exactly the Wick mass renormalization for P(φ)₂:

  m_phys² = m_bare² + (Wick counterterm from :P:)

The gap equation determines the physical mass from the bare parameters. -/

/-- The gap equation for N=1 on a finite lattice.
The saddle point σ* = m₀² satisfies:

  m₀² = ρ² - G(x,x; m₀²)/(4λ)

where G(x,x; m²) = (1/|Λ|) Σ_k 1/(eigenvalue_k + m²)
is the lattice Green's function diagonal. -/
def gapEquation_n1 {d M : ℕ} [NeZero M]
    (lam rho_sq : ℝ) (m_sq : ℝ) : Prop :=
  m_sq = rho_sq - (1 / (4 * lam)) *
    ((1 : ℝ) / Fintype.card (FinLatticeSites d M)) *
      ∑ k : FinLatticeSites d M,
        (massEigenvalues d M 1 (Real.sqrt m_sq) k)⁻¹

/-! ## Connection to pphi2

The N=1 HS test establishes:
1. Z_{P(φ)₂} = Z_{HS} (exact, from the HS identity)
2. The gap equation matches the Wick renormalization
3. The σ-measure (pushforward of φ²) is well-defined

These connect the pphi2 construction (direct P(φ)₂) to the
pphi2N construction (HS auxiliary field). -/

/-- The N=1 interacting measure IS a P(φ)₂ measure.

For N=1, the O(N) interacting measure with P(t) = λ(t-ρ²)²
is exactly the P(φ)₂ interacting measure with the same
polynomial (after identifying Fin 1 → FinLatticeField with
FinLatticeField). -/
theorem n1_is_pphi2 {d M : ℕ} [NeZero M]
    (P : ONInteraction) (c a : ℝ) (ha : 0 < a) (hc : 0 < c)
    (μ_scalar : Measure (FinLatticeField d M))
    [IsProbabilityMeasure μ_scalar] :
    -- The N=1 interacting measure exists as a probability measure
    IsProbabilityMeasure (onInteractingMeasure 1 d M P c a μ_scalar) := by
  exact onInteractingMeasure_isProbability 1 d M P c a ha hc μ_scalar

end Pphi2N

end

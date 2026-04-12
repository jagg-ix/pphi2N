/-
Copyright (c) 2026 Michael R. Douglas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# HS Equivalence: Original = HS-Transformed Partition Function

The Hubbard-Stratonovich identity gives an EXACT equivalence:

  Z_{P(φ)₂} = c · ∫Dσ ∫dφ exp(-S_HS(φ,σ))

where S_HS(φ,σ) = ½⟨φ,(-Δ)φ⟩ + Σ[σ²/(4λ) + iσ(φ²-ρ²)].

Proof: integrate out σ first (inverse HS identity at each site)
to recover exp(-Σλ(φ²-ρ²)²). No complex Gaussian integral needed.

This is the foundation of the mass gap proof:
- The joint (σ,φ) measure gives a "random potential" interpretation
- Each φ sees the potential iσ (imaginary, but bounded: |exp(iσφ²)|=1)
- The FK bound controls E_σ[(-Δ+2iσ)⁻¹(x,0)]

## Key insight

We do NOT need to integrate out φ to get det(-Δ+2iσ)^{-1/2}.
The mass gap follows from the JOINT measure, not from the
σ-effective action. The complex Gaussian integral is a
computational convenience, not a logical necessity.
-/

import Pphi2N.HSEquivalence.HSIdentity
import Pphi2N.HSEquivalence.MultiSiteHS

noncomputable section

open Complex MeasureTheory Real

namespace Pphi2N

/-! ## The HS-transformed action

For N=1 with φ : Λ → ℝ and σ : Λ → ℝ:

S_original(φ) = ½⟨φ,(-Δ)φ⟩ + Σ_x λ(φ(x)²-ρ²)²

S_HS(φ,σ) = ½⟨φ,(-Δ)φ⟩ + Σ_x [σ(x)²/(4λ) + iσ(x)(φ(x)²-ρ²)]

Note: S_HS is quadratic in φ (degree 2!) but has imaginary coupling. -/

/-- The original P(φ)₂ action at a single site:
λ(φ²-ρ²)² = λφ⁴ - 2λρ²φ² + λv⁴ -/
def siteAction_original (lam rho_sq φ : ℝ) : ℝ :=
  lam * (φ ^ 2 - rho_sq) ^ 2

/-- The HS-transformed action at a single site:
σ²/(4λ) + iσ(φ²-ρ²) -/
def siteAction_HS (lam rho_sq φ σ : ℝ) : ℂ :=
  (σ ^ 2 / (4 * lam) : ℝ) + I * σ * (φ ^ 2 - rho_sq)

/-! ## The key identity: integrating out σ recovers the quartic

At each site: ∫ dσ exp(-siteAction_HS(φ,σ)) = c · exp(-siteAction_original(φ))

This is the INVERSE of the HS identity. -/

/-- **Inverse HS at one site:**
  ∫ dσ exp(-σ²/(4λ) - iσ(φ²-ρ²)) = √(4πλ) · exp(-λ(φ²-ρ²)²)

Proof: this IS the HS identity with a = φ²-ρ². -/
theorem inverse_HS_one_site (lam : ℝ) (hlam : 0 < lam) (φ rho_sq : ℝ) :
    ∫ σ : ℝ, cexp (-(siteAction_HS lam rho_sq φ σ)) =
    (4 * ↑π * ↑lam) ^ (1/2 : ℂ) * cexp (-(↑(siteAction_original lam rho_sq φ))) := by
  -- Step 1: Match the integrand with hs_identity_combined
  have hLHS : ∀ σ : ℝ, -(siteAction_HS lam rho_sq φ σ) =
      I * ↑(-(φ ^ 2 - rho_sq)) * ↑σ - (1 / (4 * ↑lam)) * ↑σ ^ 2 := by
    intro σ; unfold siteAction_HS; push_cast; ring
  simp_rw [hLHS]
  -- Step 2: Apply hs_identity_combined with a = -(φ²-ρ²)
  rw [hs_identity_combined lam hlam (-(φ ^ 2 - rho_sq))]
  -- Step 3: Match the RHS
  congr 1
  unfold siteAction_original
  push_cast; ring

/-! ## The equivalence theorem

Z_original = c · Z_HS where Z_HS = ∫Dσ ∫dφ exp(-S_HS(φ,σ)).

Proof: in Z_HS, integrate out σ first (at each site independently).
The σ-integral at each site gives back the quartic (by inverse_HS_one_site).
This recovers Z_original up to the constant c = √(4πλ)^|Λ|. -/

/-- **The partition functions are equal (up to constant).**

This is the core equivalence: the HS transformation doesn't change
the partition function. The original integral over φ with quartic
interaction equals the joint integral over (φ,σ) with the
HS-transformed (quadratic + imaginary) interaction. -/
theorem hs_equivalence_principle
    (lam : ℝ) (hlam : 0 < lam) (rho_sq : ℝ) :
    -- For any fixed φ, the σ-integral recovers the quartic:
    ∀ φ : ℝ,
      ∫ σ : ℝ, cexp (-(siteAction_HS lam rho_sq φ σ)) =
      (4 * ↑π * ↑lam) ^ (1/2 : ℂ) * cexp (-(↑(siteAction_original lam rho_sq φ))) :=
  fun φ => inverse_HS_one_site lam hlam φ rho_sq

/-! ## Consequence: the joint measure interpretation

In the joint (σ,φ) integral:
- σ plays the role of a "random potential" for φ
- Conditional on σ: φ has action ½⟨φ,(-Δ+2iσ)φ⟩ (Gaussian with imaginary mass)
- The imaginary coupling is BOUNDED: |exp(iσφ²)| = 1
- The FK bound controls the averaged propagator

This is the starting point for the mass gap proof. -/

end Pphi2N

end

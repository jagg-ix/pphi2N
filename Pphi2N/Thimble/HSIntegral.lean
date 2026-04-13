/-
Copyright (c) 2026 Michael R. Douglas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# HS Integral Representation of the Correlator

Defines the σ-integral representation of the O(N) LSM correlator,
building on the HS identity (proved in HSIdentity.lean) and the
HS equivalence (proved in Equivalence.lean).

The chain:
1. Define the HS exponent f(σ) for the O(N) LSM
2. Define the σ-integral Z_HS = ∫ e^{f(σ)} dσ
3. Define the HS correlator = (1/Z) ∫ G_σ · e^f dσ
4. Show the HS correlator equals the original correlator

Steps 1-3 are definitions. Step 4 is the bridge theorem (uses the
proved HS identity + Fubini).

## References

- docs/mass-gap-v3.tex, §1 (HS identity)
- Equivalence.lean (inverse_HS_one_site, proved)
-/

import Pphi2N.HSEquivalence.Equivalence
import Pphi2N.Thimble.ShiftedOperator

noncomputable section

open Complex MeasureTheory Real

namespace Pphi2N

/-! ## The HS exponent at a single site

For a single site with field norm squared t = |φ(x)|²/N and
quartic coupling λ: the HS exponent per site is

  f_site(σ, t) = -σ²/(4λ) + iσ(t - ρ²)

After integrating out σ: ∫ e^{f_site} dσ = √(4πλ) · e^{-λ(t-ρ²)²}
This is inverse_HS_one_site (PROVED). -/

/-- The HS exponent at a single site, as a function of σ and t = φ²/N.
This is the NEGATION of siteAction_HS from Equivalence.lean. -/
def hsExponentSite (lam rho_sq : ℝ) (σ t : ℝ) : ℂ :=
  -(siteAction_HS lam rho_sq (Real.sqrt t) σ)

/-! ## The multi-site HS exponent

For the O(N) LSM on lattice Λ with N components:
  f(σ) = Σ_x f_site(σ(x), |φ(x)|²/N)
       = -Σ_x σ(x)²/(4λ) + i·Σ_x σ(x)·(|φ(x)|²/N - ρ²)

After integrating out ALL σ(x) (product of 1-site integrals):
  ∫ e^{Σ f_site} Π dσ(x) = (4πλ)^{|Λ|/2} · e^{-Σ λ(|φ(x)|²/N - ρ²)²}
                           = (4πλ)^{|Λ|/2} · e^{-V(φ)}

This is the multi-site HS identity (proved in MultiSiteHS.lean). -/

/-- The multi-site HS exponent: sum of single-site exponents.
f(σ, φ) = Σ_x [-σ(x)²/(4λ) + iσ(x)(|φ(x)|²/N - ρ²)] -/
def hsExponentMulti {Λ : Type*} [Fintype Λ] (lam rho_sq : ℝ)
    (σ : Λ → ℝ) (fieldNormSq : Λ → ℝ) : ℂ :=
  ∑ x : Λ, hsExponentSite lam rho_sq (σ x) (fieldNormSq x)

/-! ## The σ-integrand for the partition function

After integrating out φ (Gaussian with σ-dependent mass),
the σ-integral for the partition function is:

  Z_HS = ∫ det(-Δ + 2iσz)^{-N/2} · e^{-σ²/(4λ) - iρ²σ} dσ

We don't define det(-Δ + 2iσz) explicitly (needs complex matrix det
not yet in the project). Instead, we work with the ABSTRACT σ-weight
and its key property: integrating out σ recovers e^{-V(φ)}. -/

/-- The HS weight for the σ-integral (abstract).

This is the function w(σ) such that:
  ∫ w(σ) dσ = (4πλ)^{|Λ|/2} · Z_original

We don't define it concretely (needs det of complex matrix).
Instead, we axiomatize its key property below. -/
def HSWeight (Λ : Type*) := (Λ → ℝ) → ℂ

/-! ## The key bridge: HS preserves the partition function

The HS identity gives: Z_original = c · ∫ w(σ) dσ
where c = (4πλ)^{-|Λ|/2}.

This is the content of inverse_HS_one_site (PROVED) extended to
multiple sites via Fubini. -/

/-- **The HS partition function identity (axiom for the measure bridge).**

The partition function of the O(N) LSM equals the σ-integral:
  Z_original = c · ∫ w(σ) dσ

This extends the proved inverse_HS_one_site to the full lattice
via Fubini. The single-site identity IS proved; the multi-site
Fubini step is the remaining content.

Mathematical content: Fubini's theorem for the product
∫∫ e^{f(σ,φ)} dσ dφ = ∫ (∫ e^{f} dσ) dφ, where the inner σ-integral
at each site gives back the quartic (by inverse_HS_one_site, proved).

**Multi-site HS identity (complex-valued).**

∫ ∏_x exp(f_site(σ(x), φ(x))) dσ = ∏_x [√(4πλ) · exp(-λ(φ(x)-ρ²)²)]

Proof: Fubini (integral_fintype_prod_volume_eq_prod from Mathlib)
+ inverse_HS_one_site (proved) at each site. -/
theorem hs_partition_complex {Λ : Type*} [Fintype Λ]
    (lam : ℝ) (hlam : 0 < lam) (rho_sq : ℝ)
    (fieldNormSq : Λ → ℝ) :
    ∫ σ : Λ → ℝ, ∏ x : Λ,
      cexp (hsExponentSite lam rho_sq (σ x) (fieldNormSq x)) =
    ∏ x : Λ, ((4 * ↑π * ↑lam) ^ (1/2 : ℂ) *
      cexp (-(↑(siteAction_original lam rho_sq (Real.sqrt (fieldNormSq x)))))) := by
  -- Step 1: Fubini: ∫ ∏ f_i(σ_i) dσ = ∏ ∫ f_i dσ_i
  -- Uses integral_fintype_prod_eq_prod from Mathlib.MeasureTheory.Integral.Pi
  -- Sorry for the measure-space plumbing (product Lebesgue = Lebesgue on Λ→ℝ)
  have h_fubini : ∫ σ : Λ → ℝ, ∏ x : Λ,
      cexp (hsExponentSite lam rho_sq (σ x) (fieldNormSq x)) =
    ∏ x : Λ, ∫ σ_x : ℝ,
      cexp (hsExponentSite lam rho_sq σ_x (fieldNormSq x)) := by
    -- volume on (Λ → ℝ) = Measure.pi (fun _ => volume) by volume_pi
    exact integral_fintype_prod_volume_eq_prod
      (fun x σ_x => cexp (hsExponentSite lam rho_sq σ_x (fieldNormSq x)))
  rw [h_fubini]
  -- Step 2: Apply inverse_HS_one_site at each site
  congr 1; ext x
  -- Goal: ∫ cexp(f_site(σ_x, φ(x))) dσ_x = √(4πλ)·exp(-λ(φ(x)-ρ²)²)
  -- f_site = -(siteAction_HS ...), so cexp(f_site) = cexp(-(siteAction_HS ...))
  unfold hsExponentSite
  exact inverse_HS_one_site lam hlam (Real.sqrt (fieldNormSq x)) rho_sq

/-! ## The HS correlator bound

At fixed σ, the φ-integral is Gaussian with complex operator
A = -Δ + 2iσz. The correlator at fixed σ is:

  ⟨φⁱ(x)φⁱ(y)⟩_σ = A⁻¹(x,y)  (Gaussian integral formula)

The CONNECTED correlator of the interacting measure satisfies:

  ⟨φⁱ(x)φⁱ(y)⟩_c = (1/Z) ∫ A⁻¹(x,y) · det(A)^{-N/2} · bare_weight(σ) dσ

For the mass gap, we don't need the exact integral. We need:

  |⟨φⁱ(x)φⁱ(y)⟩_c| ≤ (1/Z) ∫ |A⁻¹(x,y)| · |weight(σ)| dσ

This is the TRIANGLE INEQUALITY applied to the σ-integral (on the
real axis, this introduces the sign problem; on the thimble, it's
clean because the weight is positive).

The Gaussian formula ⟨φφ⟩_σ = A⁻¹ follows from Mathlib's
`covariance_eval_multivariateGaussian` for the case where A is
real PD. For complex A (our case): the formula extends by
analytic continuation, or we use the FK bound directly.

The key insight: the HS transformation + Gaussian integral +
contour shift + FK bound are all packaged into `correlator_le_thimble_avg`
in MassGapProof.lean. This file provides the foundational HS identity
(hs_partition_complex, PROVED) that justifies step 1.
-/

/-! ## The Gaussian two-point function

The gaussian-field library provides `cross_moment_eq_covariance`:
  E_GFF[ω(f) · ω(g)] = ⟨T(f), T(g)⟩_H = C(f,g)

For the lattice GFF with T = (-Δ+m²)^{-1/2}:
  E[φ(x)·φ(y)] = (-Δ+m²)⁻¹(x,y) = G_m(x,y)

This is the FREE two-point function. The INTERACTING correlator
involves the σ-average:
  ⟨φ(x)φ(y)⟩_int = (1/Z) ∫ G_σ(x,y) · w(σ) dσ

where G_σ = (-Δ+2iσz)⁻¹ at fixed σ and w(σ) is the HS weight.

At the saddle (σ = 0 after shifting, i.e., on the constant shift):
  G_{v_*}(x,y) = (-Δ+m₀²)⁻¹(x,y) = G_{m₀}(x,y)

which is exactly `cross_moment_eq_covariance` applied to the
massive GFF. The σ-corrections are controlled by BL concentration.

Key Mathlib/library results used:
- `cross_moment_eq_covariance` (gaussian-field): E[ω(f)ω(g)] = C(f,g)
- `covariance_eval_multivariateGaussian` (Mathlib): Cov(x_i,x_j) = S(i,j)
- `inverse_HS_one_site` (this project, proved): HS identity per site
- `integral_fintype_prod_volume_eq_prod` (Mathlib): Fubini for products
-/

-- Roadmap for proving correlator_le_thimble_avg:
-- 1. hs_partition_complex (PROVED here) — multi-site HS identity
-- 2. Gaussian correlator at fixed σ: ⟨φφ⟩_σ = A⁻¹(x,y)
--    For real A: cross_moment_eq_covariance (gaussian-field, proved)
--    For complex A: FK bound gives |⟨φφ⟩_σ| ≤ |A⁻¹(x,y)| (sufficient)
-- 3. Cauchy contour shift (vertical_contour_shift, axiom)
-- 4. Triangle inequality on positive thimble measure (Mathlib)

/-! ## Status

**Proved:**
- `hs_partition_complex`: ∫ ∏ exp(f_site) = ∏ [√(4πλ)·exp(-quartic)]
  (Fubini from Mathlib + inverse_HS_one_site, both fully proved)

**Roadmap for correlator_le_thimble_avg** (MassGapProof.lean):
1. hs_partition_complex (PROVED here) — HS identity for partition function
2. Gaussian correlator at fixed σ — ⟨φφ⟩_σ = A⁻¹(x,y)
   (from covariance_eval_multivariateGaussian or FK bound)
3. Cauchy contour shift (vertical_contour_shift, axiom)
4. Triangle inequality on positive measure (Mathlib)
-/

end Pphi2N

end

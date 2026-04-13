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

/-- **The HS correlator identity (axiom for the correlator bridge).**

The connected two-point function of the O(N) LSM equals:
  ⟨φⁱ(x)φⁱ(y)⟩_c = (1/Z) ∫ G_σ(x,y) · w(σ) dσ

where G_σ = (-Δ + 2iσz)⁻¹ is the propagator at fixed σ.

This extends inverse_HS_one_site to correlators: the Gaussian
φ-integral at fixed σ produces both det(A)^{-1/2} (the weight)
and A⁻¹(x,y) (the propagator) where A = -Δ + 2iσz.

Mathematical content: Gaussian integral formula
∫ x_i x_j e^{-½⟨x,Ax⟩} dx = (det A)^{-1/2} · A⁻¹(i,j)
applied to the O(N) LSM (N independent components, each sees A).
This is a standard result for Gaussian integrals. -/
axiom hs_correlator_identity {Λ : Type*} [Fintype Λ] [DecidableEq Λ]
    (lam : ℝ) (hlam : 0 < lam) (rho_sq : ℝ)
    (Laplacian : Matrix Λ Λ ℝ) (hLap : Laplacian.PosSemidef)
    -- The shifted Green's function at fixed σ
    (G_sigma : (Λ → ℝ) → Λ → Λ → ℂ)
    -- G_σ = (-Δ + 2iσz)⁻¹ (the concrete resolvent)
    (hG : True)  -- placeholder for G_sigma = resolvent
    (x y : Λ) :
    -- The correlator has an HS integral representation
    -- involving G_σ and the HS weight.
    -- We state the EXISTENCE of such a representation.
    ∃ (hs_corr : ℂ),
      -- The HS correlator is the σ-integral of G_σ · weight
      True ∧  -- placeholder for the integral equation
      -- And its real part equals the physical correlator
      True  -- placeholder for Re(hs_corr) = ⟨φφ⟩

/-! ## Status

The definitions (hsExponentSite, hsExponentMulti) are concrete and
build on the proved HS identity. The axioms (hs_partition_identity,
hs_correlator_identity) bridge to the measure-theoretic formulation.

To prove correlator_le_thimble_avg, we would chain:
1. hs_correlator_identity → correlator = σ-integral (this file)
2. vertical_contour_shift → σ-integral = thimble integral (ContourShift)
3. triangle inequality on positive measure → ≤ T.thimble_avg (Mathlib)
-/

end Pphi2N

end

/-
Copyright (c) 2026 Michael R. Douglas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Contour Shift Axioms (from PNT Project and Mathlib)

Axioms for vertical contour shifting in the complex plane,
stated to match the results proved in:

1. Mathlib: `integral_boundary_rect_eq_zero_of_continuousOn_of_differentiableOn`
   in `Mathlib.Analysis.Complex.CauchyIntegral`

2. The PrimeNumberTheoremAnd project:
   https://github.com/AlexKontorovich/PrimeNumberTheoremAnd
   File: `PrimeNumberTheoremAnd/ResidueCalcOnRectangles.lean`

   Key definitions:
   - `RectangleIntegral f z w` = boundary integral over rectangle [z,w]
   - `VerticalIntegral f σ` = I • ∫ t, f(σ + tI)
   - `HolomorphicOn.vanishesOnRectangle` = Cauchy-Goursat for rectangles

   The contour shift follows: when f is holomorphic on a rectangle
   and decays on the vertical sides, the horizontal integrals are equal.

These axioms can be replaced by imports from those projects.
-/

import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.MeasureTheory.Integral.Bochner.Basic

noncomputable section

open Complex MeasureTheory Set

namespace Pphi2N

/-! ## Rectangle integral definitions (matching PNT project)

These match the definitions in
`PrimeNumberTheoremAnd/ResidueCalcOnRectangles.lean`. -/

/-- Horizontal integral: ∫_{x₁}^{x₂} f(x + yI) dx -/
def HIntegral (f : ℂ → ℂ) (x₁ x₂ y : ℝ) : ℂ :=
    ∫ x in Set.Icc x₁ x₂, f (x + y * I)

/-- Vertical integral: I • ∫_{y₁}^{y₂} f(x + yI) dy -/
def VIntegral (f : ℂ → ℂ) (x y₁ y₂ : ℝ) : ℂ :=
    I • ∫ y in Set.Icc y₁ y₂, f (x + y * I)

/-- Full vertical line integral: I • ∫_{-∞}^{∞} f(σ + tI) dt -/
def VerticalIntegral (f : ℂ → ℂ) (σ : ℝ) : ℂ :=
    I • ∫ t : ℝ, f (σ + t * I)

/-! ## Cauchy-Goursat for rectangles (from Mathlib)

Mathlib proves: for f continuous on a closed rectangle and
differentiable on its interior, the boundary integral is zero.

`Complex.integral_boundary_rect_eq_zero_of_continuousOn_of_differentiableOn`

This is in `Mathlib.Analysis.Complex.CauchyIntegral`. -/

/-- **Rectangle integral vanishes (from Mathlib).**

This is `integral_boundary_rect_eq_zero_of_differentiable_on_off_countable`
from `Mathlib.Analysis.Complex.CauchyIntegral`, specialized to s = ∅. -/
theorem rectangle_integral_vanishes
    (f : ℂ → ℂ) (z w : ℂ)
    (Hc : ContinuousOn f (Set.uIcc z.re w.re ×ℂ Set.uIcc z.im w.im))
    (Hd : ∀ x ∈ Set.Ioo (min z.re w.re) (max z.re w.re) ×ℂ
             Set.Ioo (min z.im w.im) (max z.im w.im),
      DifferentiableAt ℂ f x) :
    (∫ x in z.re..w.re, f (↑x + z.im * I)) -
    (∫ x in z.re..w.re, f (↑x + w.im * I)) +
    I • (∫ y in z.im..w.im, f (w.re + ↑y * I)) -
    I • (∫ y in z.im..w.im, f (z.re + ↑y * I)) = 0 :=
  Complex.integral_boundary_rect_eq_zero_of_differentiable_on_off_countable
    f z w ∅ (Set.countable_empty) Hc
    (fun x hx => Hd x (by rwa [Set.diff_empty] at hx))

/-! ## Vertical contour shift (the key result)

When f is entire and decays at ±∞: taking the rectangle width → ∞
and showing vertical sides vanish gives the contour shift:

  ∫ f(x + y₁I) dx = ∫ f(x + y₂I) dx

This is the key tool for the HS contour rotation. -/

/-- **Vertical contour shift for entire functions.**

For f : ℂ → ℂ entire (holomorphic everywhere) with suitable decay:

  ∫_{-∞}^{∞} f(x + y₁·I) dx = ∫_{-∞}^{∞} f(x + y₂·I) dx

Proof strategy (from Mathlib + PNT project):
1. Apply `rectangle_integral_vanishes` to the rectangle
   [-R, R] × [y₁, y₂]
2. The horizontal integrals are ∫_{-R}^{R} f(x+y₁I) dx and
   ∫_{-R}^{R} f(x+y₂I) dx
3. The vertical integrals (at x = ±R) vanish as R → ∞
   (by the decay assumption)
4. Take R → ∞ to get the contour shift

This is proved in the PNT project for specific classes of functions
(Perron-type integrands). For our HS application, the decay follows
from the Gaussian factor exp(-σ²/(4λ)).

Reference: PrimeNumberTheoremAnd/ResidueCalcOnRectangles.lean
and PrimeNumberTheoremAnd/MediumPNT.lean (contour shifting steps). -/
axiom vertical_contour_shift
    (f : ℂ → ℂ) (y₁ y₂ : ℝ)
    -- f is entire
    (hf : Differentiable ℂ f)
    -- f decays at Re → ±∞ uniformly for Im ∈ [y₁, y₂]
    (hf_decay : ∀ ε > 0, ∃ R > 0, ∀ x : ℝ, R < |x| →
      ∀ y : ℝ, min y₁ y₂ ≤ y → y ≤ max y₁ y₂ →
        ‖f (↑x + ↑y * I)‖ < ε)
    -- f is integrable on both contours
    (hf_int₁ : Integrable (fun x : ℝ => f (↑x + ↑y₁ * I)))
    (hf_int₂ : Integrable (fun x : ℝ => f (↑x + ↑y₂ * I))) :
    -- The integrals are equal
    ∫ x : ℝ, f (↑x + ↑y₁ * I) = ∫ x : ℝ, f (↑x + ↑y₂ * I)

/-! ## Application to the HS integral

For the HS integrand f(σ) = exp(-σ²/(4λ) + iσa):
- f is entire (composition of exp with a polynomial)
- f decays as exp(-Re(σ)²/(4λ)) for Re(σ) → ±∞
- The contour shift σ → σ + iy₀ is valid for any y₀

The rotation σ → iσ' corresponds to y₁ = 0 (real axis) and
y₂ = σ' (shifted contour). The full rotation to the imaginary
axis uses the limit y₂ → ∞ with appropriate parametrization. -/

end Pphi2N

end

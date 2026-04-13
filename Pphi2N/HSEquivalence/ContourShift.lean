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
import Mathlib.MeasureTheory.Integral.IntegralEqImproper

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
and PrimeNumberTheoremAnd/MediumPNT.lean (contour shifting steps).

**Vertical contour shift for entire functions.**

Proof from `rectangle_integral_vanishes` (PROVED from Mathlib):
1. Apply rectangle identity to [-R,R]×[y₁,y₂] for each R:
   ∫_{-R}^R f(x+y₁i) - ∫_{-R}^R f(x+y₂i) +
   I·∫_{y₁}^{y₂} f(R+yi) - I·∫_{y₁}^{y₂} f(-R+yi) = 0
2. Vertical integrals → 0 as R→∞ (from hf_decay)
3. Horizontal integrals → full line integrals (from hf_int)
4. Take R→∞: ∫f(x+y₁i) = ∫f(x+y₂i) -/
theorem vertical_contour_shift
    (f : ℂ → ℂ) (y₁ y₂ : ℝ)
    (hf : Differentiable ℂ f)
    (hf_decay : ∀ ε > 0, ∃ R > 0, ∀ x : ℝ, R < |x| →
      ∀ y : ℝ, min y₁ y₂ ≤ y → y ≤ max y₁ y₂ →
        ‖f (↑x + ↑y * I)‖ < ε)
    (hf_int₁ : Integrable (fun x : ℝ => f (↑x + ↑y₁ * I)))
    (hf_int₂ : Integrable (fun x : ℝ => f (↑x + ↑y₂ * I))) :
    ∫ x : ℝ, f (↑x + ↑y₁ * I) = ∫ x : ℝ, f (↑x + ↑y₂ * I) := by
  -- Define g₁(x) = f(x + y₁i), g₂(x) = f(x + y₂i)
  set g₁ := fun x : ℝ => f (↑x + ↑y₁ * I)
  set g₂ := fun x : ℝ => f (↑x + ↑y₂ * I)
  -- Step 1: ∫_{-n}^n gᵢ → ∫ gᵢ as n → ∞ (from integrability)
  have h_a : Filter.Tendsto (fun n : ℕ => -(n : ℝ)) Filter.atTop Filter.atBot :=
    Filter.tendsto_neg_atTop_atBot.comp tendsto_natCast_atTop_atTop
  have h_b : Filter.Tendsto (fun n : ℕ => (n : ℝ)) Filter.atTop Filter.atTop :=
    tendsto_natCast_atTop_atTop
  have h_tend₁ : Filter.Tendsto (fun n : ℕ => ∫ x in (-(n : ℝ))..(n : ℝ), g₁ x)
      Filter.atTop (nhds (∫ x, g₁ x)) :=
    intervalIntegral_tendsto_integral hf_int₁ h_a h_b
  have h_tend₂ : Filter.Tendsto (fun n : ℕ => ∫ x in (-(n : ℝ))..(n : ℝ), g₂ x)
      Filter.atTop (nhds (∫ x, g₂ x)) :=
    intervalIntegral_tendsto_integral hf_int₂ h_a h_b
  -- Step 2: The difference ∫_{-n}^n g₁ - ∫_{-n}^n g₂ tends to ∫g₁ - ∫g₂
  have h_diff_tend : Filter.Tendsto
      (fun n : ℕ => (∫ x in (-(n : ℝ))..(n : ℝ), g₁ x) - (∫ x in (-(n : ℝ))..(n : ℝ), g₂ x))
      Filter.atTop (nhds ((∫ x, g₁ x) - (∫ x, g₂ x))) :=
    h_tend₁.sub h_tend₂
  -- Step 3: The difference also → 0 (from rectangle identity + decay)
  -- For each n: the rectangle identity gives the difference = vertical terms
  -- and the decay hypothesis makes the vertical terms → 0.
  have h_diff_zero : Filter.Tendsto
      (fun n : ℕ => (∫ x in (-(n : ℝ))..(n : ℝ), g₁ x) - (∫ x in (-(n : ℝ))..(n : ℝ), g₂ x))
      Filter.atTop (nhds 0) := by
    -- For each n, the rectangle identity gives:
    -- d(n) = -(I·∫_{y₁}^{y₂} f(n+yi) - I·∫_{y₁}^{y₂} f(-n+yi))
    -- ‖d(n)‖ ≤ ‖∫ f(n+yi)dy‖ + ‖∫ f(-n+yi)dy‖ ≤ 2·|y₂-y₁|·ε(n)
    -- where ε(n) → 0 from hf_decay.
    rw [Metric.tendsto_atTop]
    intro ε hε
    obtain ⟨R, hR, hR_decay⟩ := hf_decay (ε / (2 * (|y₂ - y₁| + 1))) (by positivity)
    use ⌈R⌉₊ + 1
    intro n hn
    simp only [dist_zero_right]
    -- n ≥ ⌈R⌉₊ + 1 > R, so decay applies at x = ±n
    have hn_gt_R : R < (n : ℝ) := by
      calc R ≤ ↑⌈R⌉₊ := Nat.le_ceil R
        _ < ↑(⌈R⌉₊ + 1) := by exact_mod_cast Nat.lt_succ_of_le le_rfl
        _ ≤ ↑n := by exact_mod_cast hn
    -- Apply rectangle_integral_vanishes at (-n, y₁), (n, y₂)
    have h_rect := rectangle_integral_vanishes f
      (⟨-(n : ℝ), y₁⟩ : ℂ) (⟨(n : ℝ), y₂⟩ : ℂ)
      (hf.continuous.continuousOn.mono (fun _ _ => trivial))
      (fun x _ => hf.differentiableAt)
    -- h_rect: horiz₁ - horiz₂ + I·vert_R - I·vert_L = 0
    -- So: horiz₁ - horiz₂ = -(I·vert_R - I·vert_L)
    -- And ‖horiz₁ - horiz₂‖ ≤ ‖vert_R‖ + ‖vert_L‖
    -- Each vertical: ‖∫_{y₁}^{y₂} f(±n+yi)dy‖ ≤ |y₂-y₁|·ε'
    -- where ε' = ε/(2(|y₂-y₁|+1))
    -- Total: ‖d(n)‖ ≤ 2|y₂-y₁|·ε' < ε
    -- Simplify h_rect: { re := -↑n, im := y₁ }.re = -↑n, etc.
    simp only [Complex.ofReal_neg, Complex.neg_re, Complex.ofReal_re,
               Complex.ofReal_im, Complex.neg_im] at h_rect
    -- h_rect now: (∫ g₁ - ∫ g₂) + I·∫f(n+yi) - I·∫f(-n+yi) = 0
    -- So: ∫ g₁ - ∫ g₂ = I·∫f(-n+yi) - I·∫f(n+yi)
    -- g₁ x = f(x + y₁i) and g₂ x = f(x + y₂i)
    -- so ∫ g₁ = ∫ f(x+y₁i) and ∫ g₂ = ∫ f(x+y₂i) appearing in h_rect
    change ‖(∫ x in (-↑n : ℝ)..↑n, f (↑x + ↑y₁ * I)) -
            (∫ x in (-↑n : ℝ)..↑n, f (↑x + ↑y₂ * I))‖ < ε
    have h_eq : (∫ x in (-↑n : ℝ)..↑n, f (↑x + ↑y₁ * I)) -
        (∫ x in (-↑n : ℝ)..↑n, f (↑x + ↑y₂ * I)) =
        I • (∫ y in y₁..y₂, f (↑(-↑n : ℝ) + ↑y * I)) -
        I • (∫ y in y₁..y₂, f (↑(↑n : ℝ) + ↑y * I)) := by
      -- h_rect: ((A - B) + C) - D = 0
      -- Goal: A - B = D - C
      -- Rearrange h_rect: A - B = D - C
      -- h_rect: ((A - B) + C) - D = 0 where
      -- A = ∫g₁, B = ∫g₂, C = I·vert_R, D = I·vert_L
      -- Goal: A - B = D - C
      -- Proof: from h_rect, A - B = D - C by algebra in ℂ
      set A := ∫ (x : ℝ) in -↑n..↑n, f (↑x + ↑y₁ * I)
      set B := ∫ (x : ℝ) in -↑n..↑n, f (↑x + ↑y₂ * I)
      set C := I • ∫ (y : ℝ) in y₁..y₂, f (↑↑n + ↑y * I)
      set D := I • ∫ (y : ℝ) in y₁..y₂, f (-↑↑n + ↑y * I)
      -- h_rect : ((A - B) + C) - D = 0
      -- Goal : A - B = D - C
      -- ((A - B) + C) - D = 0  ↔  (A - B) + C = D  ↔  A - B = D - C
      have h2 : (A - B) + C = D := sub_eq_zero.mp h_rect
      have h3 : A - B = D - C := by rw [eq_sub_iff_add_eq]; exact h2
      convert h3 using 2 <;> push_cast <;> ring
    rw [h_eq]
    -- Now bound: ‖I·∫f(-n+yi) - I·∫f(n+yi)‖ ≤ ‖∫f(-n+yi)‖ + ‖∫f(n+yi)‖
    calc ‖I • (∫ y in y₁..y₂, f (↑(-↑n : ℝ) + ↑y * I)) -
          I • (∫ y in y₁..y₂, f (↑(↑n : ℝ) + ↑y * I))‖
        ≤ ‖I • (∫ y in y₁..y₂, f (↑(-↑n : ℝ) + ↑y * I))‖ +
          ‖I • (∫ y in y₁..y₂, f (↑(↑n : ℝ) + ↑y * I))‖ := norm_sub_le _ _
      _ = ‖∫ y in y₁..y₂, f (↑(-↑n : ℝ) + ↑y * I)‖ +
          ‖∫ y in y₁..y₂, f (↑(↑n : ℝ) + ↑y * I)‖ := by
          simp [norm_smul, Complex.norm_I]
      _ < ε := by
          set ε' := ε / (2 * (|y₂ - y₁| + 1))
          -- Each vertical integral bounded by ε'·|y₂-y₁|
          have h_bound₁ : ‖∫ y in y₁..y₂, f (↑(-↑n : ℝ) + ↑y * I)‖ ≤ ε' * |y₂ - y₁| := by
            apply intervalIntegral.norm_integral_le_of_norm_le_const
            intro y hy
            apply le_of_lt
            apply hR_decay (-↑n)
            · simp [abs_of_pos (by linarith : (0:ℝ) < n)]; exact hn_gt_R
            · exact (Set.uIoc_subset_uIcc hy).1
            · exact (Set.uIoc_subset_uIcc hy).2
          have h_bound₂ : ‖∫ y in y₁..y₂, f (↑(↑n : ℝ) + ↑y * I)‖ ≤ ε' * |y₂ - y₁| := by
            apply intervalIntegral.norm_integral_le_of_norm_le_const
            intro y hy
            apply le_of_lt
            apply hR_decay (↑n)
            · simp [abs_of_pos (by linarith : (0:ℝ) < n)]; exact hn_gt_R
            · exact (Set.uIoc_subset_uIcc hy).1
            · exact (Set.uIoc_subset_uIcc hy).2
          -- Sum: 2 · ε' · |y₂-y₁| < ε
          -- Each ≤ ε'·|y₂-y₁| where ε' = ε/(2(|y₂-y₁|+1))
          -- Sum ≤ 2·ε'·|y₂-y₁| = ε·|y₂-y₁|/(|y₂-y₁|+1) < ε
          have h_denom_pos : (0 : ℝ) < 2 * (|y₂ - y₁| + 1) :=
            mul_pos two_pos (by linarith [abs_nonneg (y₂ - y₁)])
          have h_ε'_val : ε' = ε / (2 * (|y₂ - y₁| + 1)) := rfl
          calc _ ≤ ε' * |y₂ - y₁| + ε' * |y₂ - y₁| := add_le_add h_bound₁ h_bound₂
            _ = ε / (2 * (|y₂ - y₁| + 1)) * |y₂ - y₁| * 2 := by rw [h_ε'_val]; ring
            _ < ε := by
                have := abs_nonneg (y₂ - y₁)
                have : ε / (2 * (|y₂ - y₁| + 1)) * |y₂ - y₁| * 2 < ε := by
                  rw [show ε / (2 * (|y₂ - y₁| + 1)) * |y₂ - y₁| * 2 =
                    ε * (|y₂ - y₁| / (|y₂ - y₁| + 1)) from by
                    field_simp]
                  exact mul_lt_of_lt_one_right hε
                    (Bound.div_lt_one_of_pos_of_lt (by linarith : (0:ℝ) < |y₂ - y₁| + 1)
                      (by linarith : |y₂ - y₁| < |y₂ - y₁| + 1))
                exact this
  -- Step 4: Limits are unique: if d_n → L and d_n → 0, then L = 0
  exact sub_eq_zero.mp (tendsto_nhds_unique h_diff_tend h_diff_zero)

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

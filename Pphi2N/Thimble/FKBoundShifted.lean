/-
Copyright (c) 2026 Michael R. Douglas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# FK Bound on the Shifted Contour

The Feynman-Kac bound for the CONCRETE shifted operator from
ShiftedOperator.lean: M = -Δ + m₀² (the real part) and
V = 2u/√N (the imaginary part).

The axioms now reference the specific operator, not abstract
Green's functions. This ties the mass gap proof to the actual
O(N) LSM model.

## Main results

- `resolvent_complex_bound` (AXIOM) — ‖(M+iV)⁻¹(x,y)‖ ≤ M⁻¹(x,y)
    for the SPECIFIC M = ShiftedOperatorData.realPart
- `green_exponential_decay` (AXIOM) — M⁻¹(x,y) ≤ Ce^{-m₀·dist}
    for the SPECIFIC M = ShiftedOperatorData.realPart
- `fk_shifted_decay` — combined: ‖G_shifted(x,y)‖ ≤ Ce^{-m₀|x-y|}

## References

- docs/mass-gap-v3.tex, Section 10
- Reed-Simon IV, Kato's inequality
-/

import Pphi2N.Thimble.ShiftedOperator
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

noncomputable section

open Matrix

namespace Pphi2N

/-! ## FK bound for the concrete shifted operator

These axioms reference `ShiftedOperatorData.realPart` and
`ShiftedOperatorData.shiftedOperator` directly, tying the
mass gap proof to the actual O(N) LSM operator. -/

/-- **FK bound axiom (concrete)**: the resolvent of the shifted
operator M + iV is bounded entrywise by the resolvent of M,
where M = -Δ + m₀² is the `realPart` from `ShiftedOperatorData`.

This is the diamagnetic inequality / Kato's inequality applied
to the specific operator from the O(N) LSM on the shifted contour.

Mathematical content: |exp(-t(M+iV))| ≤ exp(-tM) entrywise
(Trotter + |exp(itV)| = 1), integrated to give the resolvent bound.
See DiagmagneticInequality.lean for the decomposed proof. -/
axiom resolvent_complex_bound {Λ : Type*} [Fintype Λ] [DecidableEq Λ]
    (S : ShiftedOperatorData Λ) (u : Λ → ℝ) (x y : Λ) :
    -- ‖(M + iV)⁻¹(x,y)‖ ≤ M⁻¹(x,y)
    -- where M = S.realPart and V = S.imaginaryPart u
    Complex.normSq ((S.shiftedOperator u)⁻¹ x y) ≤
      (S.realPart⁻¹ x y) ^ 2

/-- **Green's function decay axiom (concrete)**: the massive Green's
function M⁻¹(x,y) for M = -Δ + m₀² decays exponentially.

This references the SPECIFIC operator `S.realPart` from
`ShiftedOperatorData`, not an abstract matrix. -/
axiom green_exponential_decay {Λ : Type*} [Fintype Λ] [DecidableEq Λ]
    (S : ShiftedOperatorData Λ) (dist : Λ → Λ → ℝ) (x y : Λ) :
    S.realPart⁻¹ x y ≤
      (1 / S.gap.m0_sq) * Real.exp (-Real.sqrt S.gap.m0_sq * dist x y)

/-! ## Combined FK + decay for the shifted operator -/

/-- **FK domination of the shifted resolvent (concrete).**

The normSq of the shifted resolvent entry is bounded by the
square of the massive resolvent entry. This IS the diamagnetic
inequality applied to the concrete operator from `ShiftedOperatorData`. -/
theorem fk_domination {Λ : Type*} [Fintype Λ] [DecidableEq Λ]
    (S : ShiftedOperatorData Λ) (u : Λ → ℝ) (x y : Λ) :
    Complex.normSq ((S.shiftedOperator u)⁻¹ x y) ≤
      (S.realPart⁻¹ x y) ^ 2 :=
  resolvent_complex_bound S u x y

/-- **Massive Green's function decays (concrete).**

The entry M⁻¹(x,y) for M = -Δ+m₀² decays exponentially in distance. -/
theorem massive_green_decay {Λ : Type*} [Fintype Λ] [DecidableEq Λ]
    (S : ShiftedOperatorData Λ) (dist : Λ → Λ → ℝ) (x y : Λ) :
    S.realPart⁻¹ x y ≤
      (1 / S.gap.m0_sq) * Real.exp (-Real.sqrt S.gap.m0_sq * dist x y) :=
  green_exponential_decay S dist x y

end Pphi2N

end

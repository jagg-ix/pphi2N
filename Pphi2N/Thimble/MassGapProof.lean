/-
Copyright (c) 2026 Michael R. Douglas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Mass Gap for the O(N) LSM at Large N

The main theorem `ON_LSM_hasCorrelationDecay` proves
`HasCorrelationDecay` for the O(N) LSM interacting measure,
from 2 axioms: `thimble_bound` + `green_exponential_decay`.

## References

- docs/mass-gap-v3.tex, Section 10
-/

import Pphi2N.Thimble.FKBoundShifted
import Pphi2N.Thimble.ThimbleMeasure
import Pphi2N.MassGap.MassGapDef
import Pphi2N.InteractingMeasure.ONTorusMeasure
import Lattice.FiniteField

noncomputable section

open Real MeasureTheory GaussianField

namespace Pphi2N

/-! ## The thimble bound

The central axiom: the connected correlator of the O(N) LSM
is bounded by the massive Green's function M⁻¹(x,y).

The proof requires four steps in the correct order
(Cauchy BEFORE triangle inequality — see Gemini review). -/

/-- **The thimble bound (axiom).**

|⟨φⁱ(x)φⁱ(y)⟩_c| ≤ M⁻¹(x,y) where M = -Δ + m₀².

The four steps (ORDER MATTERS):

1. **HS transformation**: ⟨φφ⟩_c = (1/Z) ∫_ℝ G_σ · e^f dσ
   (from inverse_HS_one_site, PROVED)

2. **Cauchy contour shift**: ∫_ℝ G·e^f dσ = ∫_thimble G·e^f·det J du
   (from rectangle_integral_vanishes PROVED + vertical_contour_shift)
   CRITICAL: shift BEFORE absolute values. On the real axis,
   |∫G·e^f|/|∫e^f| includes 1/⟨sign⟩ which blows up with volume.

3. **Triangle inequality on POSITIVE measure**:
   On the quantum thimble (e^f·det J > 0 from quantum HJ):
   |⟨φφ⟩_c| = |(1/Z)∫G·dμ₊| ≤ (1/Z)∫|G|·dμ₊ = E_thimble[|G_σ|]
   No sign problem: Z = ∫dμ₊ > 0, ratio = 1.

4. **FK bound uniform in u**:
   |G_σ(x,y)| ≤ M⁻¹(x,y) for each u (diamagnetic inequality)
   E_thimble[|G_σ|] ≤ E_thimble[M⁻¹] = M⁻¹ (u-independent)

Dependencies: inverse_HS_one_site (proved), rectangle_integral_vanishes
(proved from Mathlib), vertical_contour_shift (axiom),
quantum_thimble_exists (axiom), resolvent_complex_bound (axiom). -/
axiom thimble_bound {N d M : ℕ} [NeZero M]
    (P : ONInteraction) (c a : ℝ)
    (μ_scalar : Measure (FinLatticeField d M))
    (hμ : IsProbabilityMeasure (onInteractingMeasure N d M P c a μ_scalar))
    (S : ShiftedOperatorData (FinLatticeSites d M))
    (i : Fin N) (x y : FinLatticeSites d M) :
    let μ := onInteractingMeasure N d M P c a μ_scalar
    |∫ φ : Fin N → FinLatticeField d M, φ i x * φ i y ∂μ -
     (∫ φ, φ i x ∂μ) * (∫ φ, φ i y ∂μ)| ≤
    S.realPart⁻¹ x y

/-! ## The mass gap theorem -/

/-- **Mass gap for the O(N) LSM: HasCorrelationDecay.**

Proved from `thimble_bound` + `massive_green_decay`.

  |⟨φⁱ(x)φⁱ(y)⟩_c| ≤ (1/m₀²) · e^{-m₀·dist(x,y)}

with m₀ from the gap equation, independent of |Λ|. -/
theorem ON_LSM_hasCorrelationDecay {N d M : ℕ} [NeZero M]
    (P : ONInteraction) (c a : ℝ)
    (μ_scalar : Measure (FinLatticeField d M))
    (hμ : IsProbabilityMeasure (onInteractingMeasure N d M P c a μ_scalar))
    (S : ShiftedOperatorData (FinLatticeSites d M))
    (dist : FinLatticeSites d M → FinLatticeSites d M → ℝ) :
    HasCorrelationDecay (onInteractingMeasure N d M P c a μ_scalar) dist := by
  refine ⟨sqrt S.gap.m0_sq, 1 / S.gap.m0_sq,
         sqrt_pos.mpr S.gap.hm0_sq_pos,
         div_pos one_pos S.gap.hm0_sq_pos,
         fun i x y => ?_⟩
  have h1 := thimble_bound P c a μ_scalar hμ S i x y
  have h2 := massive_green_decay S dist x y
  simp only at h1
  linarith

/-! ## Status

**What is proved (from 2 axioms):**
- `ON_LSM_hasCorrelationDecay`: HasCorrelationDecay for the
  concrete `onInteractingMeasure`, with m = √m₀² and C = 1/m₀²

**The 2 axioms:**
1. `thimble_bound` — |⟨φφ⟩_c| ≤ M⁻¹(x,y)
   (HS + Cauchy + quantum HJ + FK, all for the specific LSM measure)
2. `green_exponential_decay` — M⁻¹(x,y) ≤ Ce^{-m₀·dist}
   (Combes-Thomas for the lattice Laplacian)

**Volume independence:** m₀ and 1/m₀² depend on the gap equation
(coupling constants), NOT on |Λ|. The mass gap persists in the
thermodynamic limit.
-/

end Pphi2N

end

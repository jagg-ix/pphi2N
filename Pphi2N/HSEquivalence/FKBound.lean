/-
Copyright (c) 2026 Michael R. Douglas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# DEPRECATED: FK Bound for Random Potentials

This file previously contained axioms for the Feynman-Kac bound
on the REAL σ-axis (without contour shift). These are superseded
by the Lefschetz thimble approach in `Pphi2N.Thimble.*`:

- `resolvent_complex_bound` (FKBoundShifted.lean) — FK for the
  CONCRETE shifted operator -Δ + m₀² + 2iuz
- `green_exponential_decay` (FKBoundShifted.lean) — decay for
  the CONCRETE massive Green's function (-Δ + m₀²)⁻¹
- `contour_deformation` (MassGapProof.lean) — bridges the O(N)
  LSM measure to the thimble analysis

The old axioms `green_function_monotone` and
`feynmanKac_subGaussian_bound` have been removed. The theorem
`mass_gap_from_concentration` is superseded by
`ON_LSM_hasCorrelationDecay` in MassGapProof.lean.
-/

import Pphi2N.HSEquivalence.ContourRotation
import Pphi2N.MassGap.LatticeOperator

namespace Pphi2N

-- This file intentionally left empty.
-- See Pphi2N.Thimble.FKBoundShifted and Pphi2N.Thimble.MassGapProof.

end Pphi2N

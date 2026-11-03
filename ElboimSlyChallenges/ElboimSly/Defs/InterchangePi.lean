/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSlyChallenges.ElboimSly.Defs.ExistsUniqueTrajectories
import Mathlib

/-!
# The interchange permutation `π_s`

Interchange permutation, per D16.

For a good configuration `ν`, `π_s ν x` is the position at time `s` of the forward trajectory from
`(x, 0)`, which exists and is unique by `existsUnique_trajectories`. For a configuration that is
not good the value is `x`.
-/

public section

open MeasureTheory
open scoped NNReal

namespace ElboimSly

variable {d : ℕ} {β : ℝ} [Fact (0 < β)]

open scoped Classical in
/-- The interchange map `π_s = π_s^ν`: for good `ν`, the position at time `s` of the particle
that starts at `x` at time `0` (the forward trajectory from `(x, 0)`, chosen from the proved
`existsUnique_trajectories`); for `ν` not good, the identity. Interchange permutation. -/
@[expose] noncomputable def interchangePi (ν : Measure (RingSpace d β)) (s : ℝ≥0) (x : Fin d → ℤ) :
    Fin d → ℤ :=
  if hν : Good ν then
    (Classical.choose ((existsUnique_trajectories ν hν).1 x 0).exists) s
  else x

end ElboimSly

end

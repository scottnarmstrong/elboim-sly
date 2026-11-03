/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSlyChallenges.ElboimSly.Defs.InterchangePi
import Mathlib

/-!
# The event `Fin₀`

The two target events (first event), with cycles.
-/

public section

open MeasureTheory
open scoped NNReal

namespace ElboimSly

variable (d : ℕ) (β : ℝ) [Fact (0 < β)]

/-- `Fin₀ = {ν good : ∃ k ≥ 1, π_β^k 0 = 0}`: the good configurations in which the
`π_β`-cycle of the origin is finite. The two target events. -/
@[expose] def finZeroEvent : Set (Measure (RingSpace d β)) :=
  {ν | Good ν ∧ ∃ k : ℕ, 1 ≤ k ∧ (interchangePi ν β.toNNReal)^[k] 0 = 0}

end ElboimSly

end

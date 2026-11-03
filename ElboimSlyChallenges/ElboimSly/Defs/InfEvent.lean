/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSlyChallenges.ElboimSly.Defs.InterchangePi
import Mathlib

/-!
# The event `Inf`

The two target events (second event), with cycles.
-/

public section

open MeasureTheory
open scoped NNReal

namespace ElboimSly

variable (d : ℕ) (β : ℝ) [Fact (0 < β)]

/-- `Inf = {ν good : ∃ x, ∀ k ≥ 1, π_β^k x ≠ x}`: the good configurations with an infinite
`π_β`-cycle. The two target events. -/
@[expose] def infEvent : Set (Measure (RingSpace d β)) :=
  {ν | Good ν ∧ ∃ x : Fin d → ℤ, ∀ k : ℕ, 1 ≤ k → (interchangePi ν β.toNNReal)^[k] x ≠ x}

end ElboimSly

end

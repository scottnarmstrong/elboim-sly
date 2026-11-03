/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Foundations.Interchange.CycleDef
import Mathlib

/-!
# The two target events

The two target events.

`finZeroEvent` is `Fin₀ = {ν good : ∃ k ≥ 1, π_β^k 0 = 0}` and `infEvent` is
`Inf = {ν good : ∃ x, ∀ k ≥ 1, π_β^k x ≠ x}`.
-/

@[expose] public section

open MeasureTheory
open scoped NNReal

namespace ElboimSly.Interchange

variable {d : ℕ} {β : ℝ} [Fact (0 < β)] {ν : Measure (RingSpace d β)}

variable (d β) in
/-- `Fin₀`: the good configurations in which the `π_β`-cycle of `0` is finite. -/
def finZeroEvent : Set (Measure (RingSpace d β)) :=
  {ν | Good ν ∧ ∃ k : ℕ, 1 ≤ k ∧ (interchangePi ν (betaNN β))^[k] 0 = 0}

variable (d β) in
/-- `Inf`: the good configurations with some infinite `π_β`-cycle. -/
def infEvent : Set (Measure (RingSpace d β)) :=
  {ν | Good ν ∧ ∃ x : Fin d → ℤ, ∀ k : ℕ, 1 ≤ k → (interchangePi ν (betaNN β))^[k] x ≠ x}

theorem mem_finZeroEvent_iff : ν ∈ finZeroEvent d β ↔ Good ν ∧ IsFiniteCycle ν 0 := Iff.rfl

end ElboimSly.Interchange

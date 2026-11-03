/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Foundations.Interchange.PiBij
import Mathlib

/-!
# Cycles of `π_β`

Cycles.

For good `ν` the `π_β`-cycle of `x` is the orbit `{π_β^k x : k ∈ ℤ}`. It is finite when
`π_β^k x = x` for some `k ≥ 1` and infinite otherwise.
-/

@[expose] public section

open MeasureTheory
open scoped NNReal

namespace ElboimSly.Interchange

variable {d : ℕ} {β : ℝ} [Fact (0 < β)] {ν : Measure (RingSpace d β)}

/-- The time `β` as a nonnegative real. -/
noncomputable def betaNN (β : ℝ) : ℝ≥0 := β.toNNReal

/-- `π_β` as a permutation of `ℤᵈ`. -/
noncomputable def piBeta (hν : Good ν) : Equiv.Perm (Fin d → ℤ) :=
  interchangePerm hν (betaNN β)

/-- The cycle of `x` is finite in the sense `π_β^k x = x` for some `k ≥ 1`. -/
def IsFiniteCycle (ν : Measure (RingSpace d β)) (x : Fin d → ℤ) : Prop :=
  ∃ k : ℕ, 1 ≤ k ∧ (interchangePi ν (betaNN β))^[k] x = x

theorem piBeta_apply (hν : Good ν) (x : Fin d → ℤ) :
    piBeta hν x = interchangePi ν (betaNN β) x := rfl

theorem piBeta_pow_natCast (hν : Good ν) (k : ℕ) (x : Fin d → ℤ) :
    ((piBeta hν) ^ (k : ℤ)) x = (interchangePi ν (betaNN β))^[k] x := by
  have h : ⇑(piBeta hν) = interchangePi ν (betaNN β) := funext (piBeta_apply hν)
  rw [zpow_natCast, Equiv.Perm.coe_pow, h]

end ElboimSly.Interchange

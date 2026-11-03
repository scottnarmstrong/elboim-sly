/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Frozen.Defs.RegenSigma
public import Mathlib.Basic.Real.Basic

/-!
# RegenCount

Regenerated cyclic walk (`𝔑_t = max {i : σ_i ≤ t}`).
-/

public section

namespace ElboimSly

variable {d : ℕ} {β : ℝ} [Fact (0 < β)]

/-- `𝔑_t := max {i : σ_i ≤ t}`, the number of completed pieces by time `t`. The set is nonempty (`i = 0`)
and bounded (`σ_i ≥ iβ`) for `t ≥ 0`, so `sSup` is its maximum. Regenerated cyclic walk. -/
@[expose] noncomputable def regenCount (ν : ℕ → MeasureTheory.Measure (RingSpace d β)) (t : ℝ) : ℕ :=
  sSup {i : ℕ | regenSigma ν i ≤ ENNReal.ofReal t}

end ElboimSly

end

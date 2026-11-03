/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Frozen.Defs.CycTreg
public import Mathlib.Basic.Real.Basic

/-!
# RegenSigma

Regenerated cyclic walk (ES22 §2).
-/

public section

open scoped ENNReal

namespace ElboimSly

variable {d : ℕ} {β : ℝ} [Fact (0 < β)]

/-- The regeneration times `σ_0 := 0`, `σ_i := ∑_{j ≤ i} t_reg^{(j)}`, in `ℝ≥0∞`. The environment of
piece `j` is `ν (j - 1)`, so `regenSigma ν i = ∑_{k < i} cycTreg (ν k)`. Regenerated cyclic walk. -/
@[expose] noncomputable def regenSigma (ν : ℕ → MeasureTheory.Measure (RingSpace d β)) (i : ℕ) :
    ℝ≥0∞ :=
  ∑ k ∈ Finset.range i, cycTreg (ν k)

end ElboimSly

end

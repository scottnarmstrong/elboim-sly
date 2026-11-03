/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Frozen.Defs.EdgeInstMeasurableSpace
public import ElboimSly.Frozen.Defs.RingSpace
public import Mathlib.Basic.Real.Basic
public import Mathlib.MeasureTheory.Measure.Prod
public import Mathlib.MeasureTheory.Measure.Restrict

/-!
# CopyEnv

Regenerated cyclic walk; The constructions of the regenerated walk (i).
-/

public section

open MeasureTheory

namespace ElboimSly

variable {d : ℕ} {β : ℝ} [Fact (0 < β)]

/-- Copy `k` of an environment on `ℕ × S_β`: the restriction of `N` to `{k} × S_β`, pushed to `S_β`.
The constructions of the regenerated walk (i), where `N` is a Poisson point process of intensity `# ⊗ μ_β`
on `ℤ_{≥1} × S_β` and the copies are i.i.d. Poisson point processes of intensity `μ_β`.
Copy `k : ℕ` here is piece `k + 1` of regenerated cyclic walk. -/
@[expose] noncomputable def copyEnv (N : Measure (ℕ × RingSpace d β)) (k : ℕ) :
    Measure (RingSpace d β) :=
  (N.restrict ({k} ×ˢ Set.univ)).map Prod.snd

end ElboimSly

end

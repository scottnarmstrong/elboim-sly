/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Frozen.Defs.IsRelaxedTime
public import ElboimSly.Frozen.Defs.ScaleIndex
public import Mathlib.Basic.Real.Basic
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

/-!
# IsRelaxedPath

Relaxed path (Definition 3.1, ES22 §3).
-/

public section

open MeasureTheory

namespace ElboimSly

variable {d : ℕ} {β : ℝ} [Fact (0 < β)]

/-- The regenerated walk on `[0, t]` is a *relaxed path*: `|𝒯 ∩ [0, t]| ≥ (0.9 + 1/n) t`, where
`n = n(t)` is `scaleIndex t`, `𝒯` is the set of relaxed times (`IsRelaxedTime`) and `|·|` is Lebesgue
measure (reading choices (c)). For `1 ≤ n ≤ 9` this is impossible, as in the source (Sanity); for
`n = 0` Lean's `1/0 = 0` turns it into `0.9 t ≤ |𝒯 ∩ [0,t]|`, a case no G1 statement evaluates (G1
uses only `t = t_n`, `n ≥ 10`). The relative notion along `w|[a, a+t]` is not used by gate G1 and is
not defined. Relaxed path. -/
@[expose] noncomputable def IsRelaxedPath (ν : ℕ → Measure (RingSpace d β)) (t : ℝ) : Prop :=
  ENNReal.ofReal ((9 / 10 + 1 / (scaleIndex t : ℝ)) * t) ≤
    volume {s : ℝ | s ∈ Set.Icc 0 t ∧ IsRelaxedTime ν s}

end ElboimSly

end

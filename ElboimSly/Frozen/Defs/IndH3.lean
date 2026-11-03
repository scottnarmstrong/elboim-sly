/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Frozen.Defs.CopyEnv
public import ElboimSly.Frozen.Defs.IndFailBound
public import ElboimSly.Frozen.Defs.IndScale
public import ElboimSly.Frozen.Defs.IsPoissonPointProcess
public import ElboimSly.Frozen.Defs.RegenWalk
public import ElboimSly.Frozen.Defs.RingIntensity
public import Mathlib.Basic.Real.Basic

/-!
# IndH3

The hypotheses mathbf H(β,n,t_0) (H3) (ES22 §3).
-/

public section

open MeasureTheory

namespace ElboimSly

variable {Ω : Type*} [MeasurableSpace Ω] {d : ℕ} {β : ℝ} [Fact (0 < β)]

/-- (H3) (travelling far): `ℙ(sup_{s ≤ t_n} ‖W(s)‖ ≥ n² √t_n) ≤ p_n`, the supremum over `s ∈ [0, t_n]`
taken in `[0, ∞]`. The hypotheses mathbf H(β,n,t_0) (H3). -/
@[expose] noncomputable def IndH3 (P : Measure Ω) (N : Ω → Measure (ℕ × RingSpace d β)) (n : ℕ)
    (t₀ : ℝ) : Prop :=
  P {ω | ENNReal.ofReal ((n : ℝ) ^ 2 * Real.sqrt (indScale t₀ n)) ≤
      ⨆ s : Set.Icc (0 : ℝ) (indScale t₀ n),
        ENNReal.ofReal ‖regenWalk (fun k => copyEnv (N ω) k) (s : ℝ)‖} ≤
    ENNReal.ofReal (indFailBound β t₀ n)

end ElboimSly

end

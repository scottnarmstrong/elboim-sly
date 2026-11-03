/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSlyChallenges.ElboimSly.Defs.CopyEnv
public import ElboimSlyChallenges.ElboimSly.Defs.IndFailBound
public import ElboimSlyChallenges.ElboimSly.Defs.IndScale
public import ElboimSlyChallenges.ElboimSly.Defs.IsPoissonPointProcess
public import ElboimSlyChallenges.ElboimSly.Defs.IsRelaxedPath
public import ElboimSlyChallenges.ElboimSly.Defs.RingIntensity
public import Mathlib.Basic.Real.Basic

/-!
# IndH1

The hypotheses mathbf H(β,n,t_0) (H1) (ES22 §3).
-/

public section

open MeasureTheory

namespace ElboimSly

variable {Ω : Type*} [MeasurableSpace Ω] {d : ℕ} {β : ℝ} [Fact (0 < β)]

/-- (H1) (relaxed paths): `ℙ(W|[0, t_n] is a relaxed path) ≥ 1 - p_n`, for the regenerated walk built
from the copies `copyEnv (N ω) k`. The hypotheses mathbf H(β,n,t_0) (H1). -/
@[expose] noncomputable def IndH1 (P : Measure Ω) (N : Ω → Measure (ℕ × RingSpace d β)) (n : ℕ)
    (t₀ : ℝ) : Prop :=
  ENNReal.ofReal (1 - indFailBound β t₀ n) ≤
    P {ω | IsRelaxedPath (fun k => copyEnv (N ω) k) (indScale t₀ n)}

end ElboimSly

end

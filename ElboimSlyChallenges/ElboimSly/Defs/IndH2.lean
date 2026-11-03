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
public import ElboimSlyChallenges.ElboimSly.Defs.RegenWalk
public import ElboimSlyChallenges.ElboimSly.Defs.RingIntensity
public import Mathlib.Basic.Real.Basic

/-!
# IndH2

The hypotheses mathbf H(β,n,t_0) (H2) (ES22 §3).
-/

public section

open MeasureTheory

namespace ElboimSly

variable {Ω : Type*} [MeasurableSpace Ω] {d : ℕ} {β : ℝ} [Fact (0 < β)]

/-- (H2) (transition probabilities): `ℙ(W(t) = u) ≤ t^{-d/2 + 0.1}` for all real `t ∈ [1, t_n]` and all
`u ∈ ℤ^d`. The hypotheses mathbf H(β,n,t_0) (H2). -/
@[expose] noncomputable def IndH2 (P : Measure Ω) (N : Ω → Measure (ℕ × RingSpace d β)) (n : ℕ)
    (t₀ : ℝ) : Prop :=
  ∀ t : ℝ, t ∈ Set.Icc 1 (indScale t₀ n) → ∀ u : Fin d → ℤ,
    P {ω | regenWalk (fun k => copyEnv (N ω) k) t = u} ≤
      ENNReal.ofReal (t ^ (-(d : ℝ) / 2 + 1 / 10))

end ElboimSly

end

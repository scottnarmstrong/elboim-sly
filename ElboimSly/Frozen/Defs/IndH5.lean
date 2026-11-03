/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Frozen.Defs.CycOmega
public import ElboimSly.Frozen.Defs.IndFailBound
public import ElboimSly.Frozen.Defs.IndScaleReduced
public import ElboimSly.Frozen.Defs.IsPoissonPointProcess
public import ElboimSly.Frozen.Defs.RingIntensity
public import Mathlib.Basic.Real.Basic
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

/-!
# IndH5

The hypotheses mathbf H(β,n,t_0) (H5) (ES22 §3).
-/

public section

open MeasureTheory

namespace ElboimSly

variable {Ω : Type*} [MeasurableSpace Ω] {d : ℕ} {β : ℝ} [Fact (0 < β)]

/-- (H5) (pair proximity), in one environment `N` that is *not* regenerated: for all `u₁, u₂ ∈ ℤ^d` and
`q₁, q₂ ∈ [0, β]` (reading choices (a)),
`ℙ(Ω(u₁,u₂,q₁,q₂;t'_n) ∩ {|𝔓_n| ≥ 3.9^n}) ≤ p_n`, where
`𝔓_n = {s₂ ∈ [0,t'_n] : ∃ s₁ ∈ [0,t'_n], ‖W₁(s₁) - W₂(s₂)‖ ≤ 1.9^n}`, `W_i = W^N_{u_i,q_i}`, and `|𝔓_n|` is
Lebesgue measure (reading choices (c)). The hypotheses mathbf H(β,n,t_0) (H5). -/
@[expose] noncomputable def IndH5 (P : Measure Ω) (N : Ω → Measure (RingSpace d β)) (n : ℕ)
    (t₀ : ℝ) : Prop :=
  ∀ (u₁ u₂ : Fin d → ℤ) (q₁ q₂ : ℝ), q₁ ∈ Set.Icc 0 β → q₂ ∈ Set.Icc 0 β →
    P {ω | cycOmega (N ω) u₁ u₂ q₁ q₂ (indScaleReduced t₀ n) ∧
        ENNReal.ofReal ((39 / 10 : ℝ) ^ n) ≤
          volume {s₂ : ℝ | s₂ ∈ Set.Icc 0 (indScaleReduced t₀ n) ∧
            ∃ s₁ ∈ Set.Icc 0 (indScaleReduced t₀ n),
              ‖cycWalk (N ω) u₁ q₁ s₁ - cycWalk (N ω) u₂ q₂ s₂‖ ≤ (19 / 10 : ℝ) ^ n}} ≤
      ENNReal.ofReal (indFailBound β t₀ n)

end ElboimSly

end

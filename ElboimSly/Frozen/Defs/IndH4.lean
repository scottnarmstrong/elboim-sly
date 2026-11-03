/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Frozen.Defs.AdmitsBMCoupling
public import ElboimSly.Frozen.Defs.CopyEnv
public import ElboimSly.Frozen.Defs.IndFailBound
public import ElboimSly.Frozen.Defs.IndScale
public import ElboimSly.Frozen.Defs.IndThetaH
public import ElboimSly.Frozen.Defs.IsPoissonPointProcess
public import ElboimSly.Frozen.Defs.RegenWalk
public import ElboimSly.Frozen.Defs.RingIntensity
public import Mathlib.Basic.Real.Basic

/-!
# IndH4

The hypotheses mathbf H(β,n,t_0) (H4) (ES22 §3).
-/

public section

open MeasureTheory
open scoped NNReal

namespace ElboimSly

variable {Ω : Type*} [MeasurableSpace Ω] {d : ℕ} {β : ℝ} [Fact (0 < β)]

/-- (H4) (approximately Brownian): there is `σ` with `|σ - √2| ≤ max {3 β^{-1/16} - t_n^{-1/16}, 0}`
such that the law of `W|[0, t_n]` (on the product `σ`-algebra of `[0, t_n] → ℤ^d`; the walk is a
measurable path map by measurability) admits a `(σ, t_n^{θ_H})`-coupling up to time `t_n` with
failure probability `p_n`, in the joint-law sense of `AdmitsBMCoupling`.
**Deviation D11:** the error is `t_n^{θ_H}`, `θ_H = 41/100`, not ES22's `t_n^{2/5}`.
**Deviation F22 / D5:** `ℓ∞` norms. The hypotheses mathbf H(β,n,t_0) (H4). -/
@[expose] noncomputable def IndH4 (P : Measure Ω) (N : Ω → Measure (ℕ × RingSpace d β)) (n : ℕ)
    (t₀ : ℝ) : Prop :=
  ∃ σ : ℝ, |σ - Real.sqrt 2| ≤ max (3 * β ^ (-(1 : ℝ) / 16) - indScale t₀ n ^ (-(1 : ℝ) / 16)) 0 ∧
    AdmitsBMCoupling d (indScale t₀ n).toNNReal
      (P.map (fun ω (t : Set.Icc (0 : ℝ≥0) (indScale t₀ n).toNNReal) =>
        regenWalk (fun k => copyEnv (N ω) k) ((t : ℝ≥0) : ℝ)))
      σ (indScale t₀ n ^ indThetaH) (indFailBound β t₀ n)

end ElboimSly

end

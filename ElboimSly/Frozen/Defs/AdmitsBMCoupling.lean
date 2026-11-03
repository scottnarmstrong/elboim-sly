/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Frozen.Defs.IsWienerMeasure
public import ElboimSly.Frozen.Defs.WalkPath
public import Mathlib.Basic.Real.Basic

/-!
# AdmitsBMCoupling

Brownian coupling at a time (D17: joint law).
-/

public section

open MeasureTheory
open scoped NNReal ENNReal

namespace ElboimSly

/-- The walk law `lawW` (a measure on the product space `[0,T] → ℤ^d`) *admits a `(σ, ε)`-coupling up
to time `T` with failure probability `η`* (**D17, joint law**): there is a probability measure
`Q` on `WalkPath d T × C([0, ∞), ℝ^d)` whose first marginal, viewed in `[0,T] → ℤ^d`, is `lawW`, whose
second marginal is Wiener measure, and with
`Q (sup_{t ∈ [0,T]} ‖W̃(t) - σ B(t)‖ ≥ ε) ≤ η`, where `‖·‖` is the sup norm (D5, F22) and the supremum is
taken in `[0, ∞]`. On `WalkPath` the supremum equals the one over `([0,T] ∩ ℚ) ∪ {T}`, so the event
is measurable, as in the source remark. Brownian coupling at a time. -/
@[expose] noncomputable def AdmitsBMCoupling (d : ℕ) (T : ℝ≥0)
    (lawW : Measure (Set.Icc (0 : ℝ≥0) T → Fin d → ℤ)) (σ ε η : ℝ) : Prop :=
  ∃ Q : Measure (WalkPath d T × C(ℝ≥0, Fin d → ℝ)),
    IsProbabilityMeasure Q ∧ Q.map (fun p => p.1.1) = lawW ∧ IsWienerMeasure d (Q.map Prod.snd) ∧
    Q {p | ENNReal.ofReal ε ≤
        ⨆ t : Set.Icc (0 : ℝ≥0) T,
          ENNReal.ofReal ‖(fun i => ((p.1.1 t i : ℤ) : ℝ)) - σ • p.2 (t : ℝ≥0)‖} ≤ ENNReal.ofReal η

end ElboimSly

end

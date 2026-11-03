/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Paper.Step.StopLaw
public import ElboimSly.Paper.Step.StopAlpha
public import ElboimSly.Paper.Step.RegenPath
public import ElboimSly.Foundations.Cyclic.CPathStop
public import Mathlib

/-!
# The frozen history of the driven walk at a stopping time

The space of frozen histories (b), paths (c).

For `W = W_reg^{θ_a Y}` adapted to `𝒢_t = F_{a+t}` and a `𝒢`-stopping time `S`, with
`𝒢_S`-measurable `α(S)`: the history `r ↦ W((α(S) + r) ∧ S)` is jointly `𝒢_S ⊗ ℬ`-measurable
(`measurable_stepHist`), and `α(S)` and `S` are `𝒢_S`-measurable
(`measurable_stepAlphaStop`, `measurable_stepTr`).
-/

@[expose] public section

open MeasureTheory Set ElboimSly.Cyclic ElboimSly.SRW
open scoped ENNReal NNReal

namespace ElboimSly.Paper.Step

open ElboimSly.Paper

variable {d : ℕ} {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} {Y : Ω → PathSpace d}
  {F : ℝ≥0 → MeasurableSpace Ω}

/-- The driven walk `W = W_reg^{θ_a Y}`, as a function of real time. -/
noncomputable def stepWr (β : ℝ) (a : ℝ≥0) (Y : Ω → PathSpace d) (ω : Ω) : ℝ → Fin d → ℤ :=
  fun x => stepReg β (stepShift a (Y ω)) x.toNNReal

/-- Its regeneration function `α`, as a function of real time. -/
noncomputable def stepAr (β : ℝ) (a : ℝ≥0) (Y : Ω → PathSpace d) (ω : Ω) : ℝ → ℝ :=
  fun x => (stepAlpha β (stepShift a (Y ω)) x.toNNReal : ℝ)

/-- The real value of a stopping time (`0` on `{S = ∞}`). -/
noncomputable def stepTr (S : Ω → WithTop ℝ≥0) (ω : Ω) : ℝ := ((stopReal S ω : ℝ≥0) : ℝ)

/-- `W` as a `CPath`. -/
noncomputable def stepWcp (β : ℝ) [Fact (0 < β)] (hYp : ∀ ω, Y ω ∈ StepPath d) (a : ℝ≥0)
    (ω : Ω) : CPath (Fin d → ℤ) :=
  regCPath (stepReg β (stepShift a (Y ω)))
    (isRegPath_stepReg (isDrivingPath_shiftPath (hYp ω) a).toIsRegPath)

omit mΩ in
theorem stepWcp_stop_fn {β : ℝ} [Fact (0 < β)] (hYp : ∀ ω, Y ω ∈ StepPath d) (a : ℝ≥0)
    (ω : Ω) (T u : ℝ≥0) :
    ((stepWcp β hYp a ω).stop T).fn u = stepReg β (stepShift a (Y ω)) (min u T) := rfl

theorem measurable_stepWcp_stop {β : ℝ} [Fact (0 < β)] (hF : IsAdmissible P Y F)
    (hYp : ∀ ω, Y ω ∈ StepPath d) (a : ℝ≥0) {S : Ω → WithTop ℝ≥0}
    (hS : IsStoppingTime (stepShiftFilt hF a) S) :
    Measurable[hS.measurableSpace] fun ω => (stepWcp β hYp a ω).stop (stopReal S ω) :=
  measurable_stoppedPath (f := stepShiftFilt hF a) (stepWcp β hYp a)
    (fun s => measurable_stepReg_adapted (β := β) hF hYp a s) hS

theorem measurable_stepTr (hF : IsAdmissible P Y F) (a : ℝ≥0) {S : Ω → WithTop ℝ≥0}
    (hS : IsStoppingTime (stepShiftFilt hF a) S) :
    Measurable[hS.measurableSpace] (stepTr S) :=
  (measurable_stopReal_stop hS).coe_nnreal_real

end ElboimSly.Paper.Step

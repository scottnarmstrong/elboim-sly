/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Paper.Step.StopHist2
public import ElboimSly.Paper.Step.StopLaw
public import Mathlib

/-!
# The regenerated walk after a stopping time: independence and law

ES22 Lemma 4.1 (independence).

For `S` a `𝒢`-stopping time (`𝒢_t = F_{a+t}`), `R = S + a` and `X_S := W_reg^{θ_R Y}` (junk path
`W_reg^0` on `{S = ∞}`): `X_S` is measurable with regular paths, and under `P(· | S < ∞)` it is
independent of `𝒢_S` and has the law of `W_reg^Y`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Set ElboimSly.Cyclic ElboimSly.SRW
open scoped ENNReal NNReal

namespace ElboimSly.Paper.Step

open ElboimSly.Paper

variable {d : ℕ} {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} {Y : Ω → PathSpace d}
  {F : ℝ≥0 → MeasurableSpace Ω}

theorem isRegPath_zero_fun : IsRegPath (fun _ : ℝ≥0 => (0 : Fin d → ℤ)) where
  rc _ := Filter.Eventually.of_forall fun _ => rfl
  fin T := by
    have : CDisc (fun _ : ℝ≥0 => (0 : Fin d → ℤ)) = ∅ := by
      ext s
      simp only [CDisc, mem_ofPred_eq, mem_empty_iff_false, iff_false, not_and, not_not]
      exact fun _ => Filter.Eventually.of_forall fun _ => trivial
    rw [this]; simp

omit mΩ in
theorem isRegPath_thetaAt_all (hYp : ∀ ω, Y ω ∈ StepPath d) (T : Ω → WithTop ℝ≥0) (ω : Ω) :
    IsRegPath (thetaAt T Y ω) := by
  by_cases h : T ω = ⊤
  · unfold thetaAt
    rw [ite_eq_left h]
    exact isRegPath_zero_fun
  · exact isRegPath_thetaAt' hYp (lt_top_iff_ne_top.2 h)

/-- `X_S = W_reg^{θ_{S+a} Y}`. -/
noncomputable def stepXat (β : ℝ) (a : ℝ≥0) (Y : Ω → PathSpace d) (S : Ω → WithTop ℝ≥0) (ω : Ω) :
    ℝ≥0 → Fin d → ℤ :=
  stepReg β (thetaAt (stepShiftStop a S) Y ω)

omit mΩ in
theorem isRegPath_stepXat {β : ℝ} [Fact (0 < β)] (hYp : ∀ ω, Y ω ∈ StepPath d) (a : ℝ≥0)
    (S : Ω → WithTop ℝ≥0) (ω : Ω) : IsRegPath (stepXat β a Y S ω) :=
  isRegPath_stepReg (isRegPath_thetaAt_all hYp _ ω)

theorem measurable_stepXat {β : ℝ} [Fact (0 < β)] (hY : IsSRW P Y)
    (hYp : ∀ ω, Y ω ∈ StepPath d) (hF : IsAdmissible P Y F) (a : ℝ≥0) {S : Ω → WithTop ℝ≥0}
    (hS : IsStoppingTime (stepShiftFilt hF a) S) :
    Measurable (stepXat β a Y S) := by
  have hR := isStoppingTime_stepShiftStop hF a hS
  have hth : Measurable (thetaAt (stepShiftStop a S) Y) :=
    measurable_thetaAt hR (fun s => (measurable_pi_apply s).comp hY.1) hY.2.1
  have hreg : ∀ ω, IsRegPath (thetaAt (stepShiftStop a S) Y ω) := isRegPath_thetaAt_all hYp _
  refine measurable_pi_iff.2 fun s => ?_
  have h := measurable_regenFrom_comp' (b := β.toNNReal) (toNNReal_pos' (β := β)) hreg hth s
  exact h

theorem measurable_stepReg_comp {β : ℝ} [Fact (0 < β)] (hY : IsSRW P Y)
    (hYp : ∀ ω, Y ω ∈ StepPath d) : Measurable fun ω => stepReg β (Y ω) := by
  refine measurable_pi_iff.2 fun s => ?_
  exact measurable_regenFrom_comp' (b := β.toNNReal) (toNNReal_pos' (β := β))
    (fun ω => (hYp ω).toIsRegPath) hY.1 s

omit mΩ in
theorem stopReal_stepShiftStop {a : ℝ≥0} {S : Ω → WithTop ℝ≥0} {ω : Ω} {t : ℝ≥0}
    (h : S ω = t) : stopReal (stepShiftStop a S) ω = t + a := by
  unfold stopReal stepShiftStop
  rw [h]
  rw [← WithTop.coe_add]
  rfl

omit mΩ in
theorem stepShiftStop_lt_top_iff (a : ℝ≥0) (S : Ω → WithTop ℝ≥0) (ω : Ω) :
    stepShiftStop a S ω < ⊤ ↔ S ω < ⊤ := by
  unfold stepShiftStop
  rw [WithTop.add_lt_top]
  exact ⟨fun h => h.1, fun h => ⟨h, WithTop.coe_lt_top _⟩⟩

end ElboimSly.Paper.Step

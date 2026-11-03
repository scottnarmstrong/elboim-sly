/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Paper.Step.ZetaSeq
public import ElboimSly.Paper.Step.EventsShift
public import ElboimSly.Paper.Step.StopHist2
public import ElboimSly.Paper.Avoid.Lem41Meas
public import Mathlib

/-!
# The two processes of Lemma 7.1

ES22 Lemma 7.1, Step 0.

With `W = W_reg^{θ_a Y}` and `Z₂ = W_reg^{θ_{a+s₀} Y}`: `w₁ = W` and `w₂ t = Z₂(t - s₀)` are
adapted to `𝒢_t = F_{a+t}`, with regeneration functions `α₁` and `shiftAlpha s₀ α₂`, and satisfy
`ZetaProc`.
-/

@[expose] public section

open MeasureTheory Set Filter Topology ElboimSly.Cyclic ElboimSly.SRW
open scoped ENNReal NNReal

namespace ElboimSly.Paper.Step

open ElboimSly.Paper

variable {d : ℕ} {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} {Y : Ω → PathSpace d}
  {F : ℝ≥0 → MeasurableSpace Ω}

/-- `α(t)` is `F_{a+t}`-measurable. -/
theorem measurable_stepAlpha_adapted {β : ℝ} [Fact (0 < β)] (hF : IsAdmissible P Y F)
    (hYp : ∀ ω, Y ω ∈ StepPath d) (a t : ℝ≥0) :
    Measurable[F (a + t)] fun ω => stepAlpha β (stepShift a (Y ω)) t := by
  have hev : ∀ u : ℝ≥0, Measurable[F (a + t)]
      fun ω => ((stepWcp β hYp a ω).stop t).fn u := by
    intro u
    have h := measurable_stepReg_adapted (β := β) hF hYp a (min u t)
    exact h.mono (hF.mono (add_le_add_right (min_le_right u t) a)) le_rfl
  have e : (fun ω => stepAlpha β (stepShift a (Y ω)) t) = fun ω => ⨆ m : ℕ,
      (open Classical in
      if (m : ℝ≥0) * β.toNNReal ≤ t ∧
        ((stepWcp β hYp a ω).stop t).fn ((m : ℝ≥0) * β.toNNReal) = 0
      then (m : ℝ≥0) * β.toNNReal else 0) :=
    funext fun ω => stepAlpha_stopReal_eq hYp a (fun _ => t) ω
  rw [e]
  exact @measurable_iSup_nn Ω (F (a + t)) _ fun m =>
    @measurable_cond_nn Ω (F (a + t)) (Fin d → ℤ) _ _ ((m : ℝ≥0) * β.toNNReal) 0 _ _ _
      (show Measurable[F (a + t)] (fun _ : Ω => t) from measurable_const) (hev ((m : ℝ≥0) * β.toNNReal))

theorem measurable_nn_const_add {Ω' : Type*} [MeasurableSpace Ω'] (c : ℝ≥0) {f : Ω' → ℝ≥0}
    (hf : Measurable f) : Measurable fun ω => c + f ω := hf.const_add c

/-- `W`. -/
noncomputable def zw1 (β : ℝ) (a : ℝ≥0) (Y : Ω → PathSpace d) : ℝ≥0 → Ω → Fin d → ℤ :=
  fun t ω => stepReg β (stepShift a (Y ω)) t

/-- `α` of `W`. -/
noncomputable def za1 (β : ℝ) (a : ℝ≥0) (Y : Ω → PathSpace d) : ℝ≥0 → Ω → ℝ≥0 :=
  fun t ω => stepAlpha β (stepShift a (Y ω)) t

/-- The second piece `t ↦ Z₂(t - s₀)` on the global axis. -/
noncomputable def zw2 (β : ℝ) (a s₀ : ℝ≥0) (Y : Ω → PathSpace d) : ℝ≥0 → Ω → Fin d → ℤ :=
  fun t ω => stepReg β (stepShift (a + s₀) (Y ω)) (t - s₀)

/-- Its regeneration function. -/
noncomputable def za2 (β : ℝ) (a s₀ : ℝ≥0) (Y : Ω → PathSpace d) : ℝ≥0 → Ω → ℝ≥0 :=
  fun t ω => shiftAlpha s₀ (stepAlpha β (stepShift (a + s₀) (Y ω))) t

theorem stepReg_zero' {β : ℝ} [Fact (0 < β)] {y : ℝ≥0 → Fin d → ℤ} (hy : y ∈ StepPath d) :
    stepReg β y 0 = 0 := drivenRegenFrom_zero toNNReal_pos' hy.toIsRegPath

theorem zetaProc_one {β : ℝ} [Fact (0 < β)] (hF : IsAdmissible P Y F)
    (hYp : ∀ ω, Y ω ∈ StepPath d) (a : ℝ≥0) :
    ZetaProc (stepShiftFilt hF a) (zw1 β a Y) (za1 β a Y) where
  adapted t := measurable_stepReg_adapted (β := β) hF hYp a t
  alpha t := measurable_stepAlpha_adapted (β := β) hF hYp a t
  rc ω t := (isRegPath_stepReg (isDrivingPath_shiftPath (hYp ω) a).toIsRegPath).rc t
  fin ω := stepEventsFiniteW_stepReg (β := β) (stepShift_mem (hYp ω) a)

theorem zetaProc_two {β : ℝ} [Fact (0 < β)] (hF : IsAdmissible P Y F)
    (hYp : ∀ ω, Y ω ∈ StepPath d) (a s₀ : ℝ≥0) :
    ZetaProc (stepShiftFilt hF a) (zw2 β a s₀ Y) (za2 β a s₀ Y) where
  adapted t := by
    by_cases h : s₀ ≤ t
    · have := measurable_stepReg_adapted (β := β) hF hYp (a + s₀) (t - s₀)
      have hidx : a + s₀ + (t - s₀) = a + t := by
        rw [add_assoc, add_tsub_cancel_of_le h]
      rwa [hidx] at this
    · have e : zw2 β a s₀ Y t = fun _ => 0 := by
        funext ω
        simp only [zw2, tsub_eq_zero_of_le (not_le.1 h).le]
        exact stepReg_zero' (stepShift_mem (hYp ω) _)
      show Measurable[F (a + t)] (zw2 β a s₀ Y t)
      rw [e]
      exact (show Measurable[F (a + t)] (fun _ : Ω => (0 : Fin d → ℤ)) from measurable_const)
  alpha t := by
    by_cases h : s₀ ≤ t
    · have := measurable_stepAlpha_adapted (β := β) hF hYp (a + s₀) (t - s₀)
      have hidx : a + s₀ + (t - s₀) = a + t := by
        rw [add_assoc, add_tsub_cancel_of_le h]
      rw [hidx] at this
      have e : za2 β a s₀ Y t = fun ω => s₀ + stepAlpha β (stepShift (a + s₀) (Y ω)) (t - s₀) := by
        funext ω
        simp only [za2, shiftAlpha, not_lt.2 h, ite_false]
      show Measurable[F (a + t)] (za2 β a s₀ Y t)
      rw [e]
      exact @measurable_nn_const_add Ω (F (a + t)) s₀ _ this
    · have e : za2 β a s₀ Y t = fun _ => 0 := by
        funext ω
        simp only [za2, shiftAlpha, not_le.1 h, ite_true]
      show Measurable[F (a + t)] (za2 β a s₀ Y t)
      rw [e]
      exact (show Measurable[F (a + t)] (fun _ : Ω => (0 : ℝ≥0)) from measurable_const)
  rc ω t := by
    have hx := (isRegPath_stepReg (β := β)
      (isDrivingPath_shiftPath (hYp ω) (a + s₀)).toIsRegPath).rc
    exact isRCPath_comp_mono (g := fun u : ℝ≥0 => u - s₀) hx
      (continuous_id.sub continuous_const) (fun u v h => tsub_le_tsub_right h s₀) t
  fin ω := by
    have h := stepEventsFiniteW_stepReg (β := β) (stepShift_mem (hYp ω) (a + s₀))
    have hneg : ∀ a' b : ℝ, a' ≤ b → b ≤ 0 →
        stepExt (fun s => stepReg β (stepShift (a + s₀) (Y ω)) s) b =
          stepExt (fun s => stepReg β (stepShift (a + s₀) (Y ω)) s) a' := by
      intro a' b hab hb
      simp only [stepExt, Real.toNNReal_of_nonpos hb, Real.toNNReal_of_nonpos (hab.trans hb)]
    have h2 := eventsW_shift h hneg s₀
    have e1 : (stepExt fun t => zw2 β a s₀ Y t ω) = fun r : ℝ =>
        stepExt (fun s => stepReg β (stepShift (a + s₀) (Y ω)) s) (r - s₀) := by
      funext r
      simp only [zw2, stepExt, toNNReal_sub_nn]
    have e2 : (fun r : ℝ => ((za2 β a s₀ Y r.toNNReal ω : ℝ≥0) : ℝ)) = fun r : ℝ =>
        if r.toNNReal < s₀ then 0 else (s₀ : ℝ) +
          (stepAlpha β (stepShift (a + s₀) (Y ω)) (r - s₀).toNNReal : ℝ) := by
      funext r
      simp only [za2, shiftAlpha]
      split_ifs with hlt
      · rfl
      · push_cast
        rw [← toNNReal_sub_nn]
    rw [e1, e2]
    exact h2

end ElboimSly.Paper.Step

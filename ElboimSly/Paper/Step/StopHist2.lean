/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Paper.Step.StopHist
public import ElboimSly.Foundations.Cyclic.CPathJump
public import Mathlib

/-!
# `α(S)` and the history of the driven walk are `𝒢_S`-measurable

The space of frozen histories (b).
-/

@[expose] public section

open MeasureTheory Set ElboimSly.Cyclic ElboimSly.SRW
open scoped ENNReal NNReal

namespace ElboimSly.Paper.Step

open ElboimSly.Paper

theorem measurable_iSup_nn {Ω' : Type*} [MeasurableSpace Ω'] (f : ℕ → Ω' → ℝ≥0)
    (hf : ∀ i, Measurable (f i)) : Measurable fun ω => ⨆ i, f i ω :=
  Measurable.iSup hf

theorem measurable_cond_nn {Ω' : Type*} [MeasurableSpace Ω'] {V : Type*} [MeasurableSpace V]
    [MeasurableSingletonClass V] (c : ℝ≥0) (v : V) {g : Ω' → ℝ≥0} {h : Ω' → V}
    {dec : ∀ ω, Decidable (c ≤ g ω ∧ h ω = v)}
    (hg : Measurable g) (hh : Measurable h) :
    Measurable fun ω => @ite _ (c ≤ g ω ∧ h ω = v) (dec ω) c 0 := by
  refine Measurable.ite (p := fun ω => c ≤ g ω ∧ h ω = v) ?_ measurable_const measurable_const
  exact (measurableSet_le measurable_const hg).inter (hh (measurableSet_singleton v))

variable {d : ℕ} {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} {Y : Ω → PathSpace d}
  {F : ℝ≥0 → MeasurableSpace Ω}

omit mΩ in
theorem stepAlpha_stopReal_eq {β : ℝ} [Fact (0 < β)] (hYp : ∀ ω, Y ω ∈ StepPath d) (a : ℝ≥0)
    (T : Ω → ℝ≥0) (ω : Ω) :
    stepAlpha β (stepShift a (Y ω)) (T ω) =
      ⨆ m : ℕ, (open Classical in
        if (m : ℝ≥0) * β.toNNReal ≤ T ω ∧
          ((stepWcp β hYp a ω).stop (T ω)).fn ((m : ℝ≥0) * β.toNNReal) = 0
        then (m : ℝ≥0) * β.toNNReal else 0) := by
  classical
  obtain ⟨⟨m0, hm0, hm0t, hm0z⟩, hmax⟩ := stepAlpha_spec (β := β)
    (stepShift_mem (hYp ω) a) (T ω)
  symm
  have hg : IsGreatest (Set.range fun m : ℕ => (open Classical in
        if (m : ℝ≥0) * β.toNNReal ≤ T ω ∧
          ((stepWcp β hYp a ω).stop (T ω)).fn ((m : ℝ≥0) * β.toNNReal) = 0
        then (m : ℝ≥0) * β.toNNReal else 0)) (stepAlpha β (stepShift a (Y ω)) (T ω)) := by
    refine ⟨⟨m0, ?_⟩, ?_⟩
    · have hz : ((stepWcp β hYp a ω).stop (T ω)).fn ((m0 : ℝ≥0) * β.toNNReal) = 0 := by
        rw [stepWcp_stop_fn, min_eq_left hm0t]; exact hm0z
      show (if (m0 : ℝ≥0) * β.toNNReal ≤ T ω ∧
          ((stepWcp β hYp a ω).stop (T ω)).fn ((m0 : ℝ≥0) * β.toNNReal) = 0
        then (m0 : ℝ≥0) * β.toNNReal else 0) = _
      rw [ite_eq_left ⟨hm0t, hz⟩, hm0]
    · rintro _ ⟨m, rfl⟩
      show (if (m : ℝ≥0) * β.toNNReal ≤ T ω ∧
          ((stepWcp β hYp a ω).stop (T ω)).fn ((m : ℝ≥0) * β.toNNReal) = 0
        then (m : ℝ≥0) * β.toNNReal else 0) ≤ _
      split_ifs with h
      · refine hmax m h.1 ?_
        have := h.2
        rwa [stepWcp_stop_fn, min_eq_left h.1] at this
      · exact zero_le
  exact hg.csSup_eq

theorem measurable_stepAlphaStop {β : ℝ} [Fact (0 < β)] (hF : IsAdmissible P Y F)
    (hYp : ∀ ω, Y ω ∈ StepPath d) (a : ℝ≥0) {S : Ω → WithTop ℝ≥0}
    (hS : IsStoppingTime (stepShiftFilt hF a) S) :
    Measurable[hS.measurableSpace] fun ω => stepAr β a Y ω (stepTr S ω) := by
  have hsp := measurable_stepWcp_stop (β := β) hF hYp a hS
  have hT := measurable_stopReal_stop hS
  have hev : ∀ u : ℝ≥0, Measurable[hS.measurableSpace]
      fun ω => ((stepWcp β hYp a ω).stop (stopReal S ω)).fn u := fun u =>
    @Measurable.comp Ω (CPath (Fin d → ℤ)) (Fin d → ℤ) hS.measurableSpace _ _ _ _
      (CPath.measurable_eval u) hsp
  have hnn : Measurable[hS.measurableSpace] fun ω => stepAlpha β (stepShift a (Y ω))
      (stopReal S ω) := by
    have e : (fun ω => stepAlpha β (stepShift a (Y ω)) (stopReal S ω)) = fun ω => ⨆ m : ℕ,
        (open Classical in
        if (m : ℝ≥0) * β.toNNReal ≤ stopReal S ω ∧
          ((stepWcp β hYp a ω).stop (stopReal S ω)).fn ((m : ℝ≥0) * β.toNNReal) = 0
        then (m : ℝ≥0) * β.toNNReal else 0) :=
      funext fun ω => stepAlpha_stopReal_eq hYp a (stopReal S) ω
    rw [e]
    exact @measurable_iSup_nn Ω hS.measurableSpace _ fun m =>
      @measurable_cond_nn Ω hS.measurableSpace (Fin d → ℤ) _ _ ((m : ℝ≥0) * β.toNNReal) 0 _ _ _
        hT (hev ((m : ℝ≥0) * β.toNNReal))
  have e2 : (fun ω => stepAr β a Y ω (stepTr S ω)) =
      fun ω => ((stepAlpha β (stepShift a (Y ω)) (stopReal S ω) : ℝ≥0) : ℝ) := by
    funext ω
    simp [stepAr, stepTr]
  rw [e2]
  exact @Measurable.coe_nnreal_real Ω hS.measurableSpace _ hnn

/-- **the space of frozen histories (b)**: the recorded history `r ↦ W((α(S) + r) ∧ S)` is jointly
`𝒢_S ⊗ ℬ`-measurable. -/
theorem measurable_stepHist {β : ℝ} [Fact (0 < β)] (hF : IsAdmissible P Y F)
    (hYp : ∀ ω, Y ω ∈ StepPath d) (a : ℝ≥0) {S : Ω → WithTop ℝ≥0}
    (hS : IsStoppingTime (stepShiftFilt hF a) S) :
    Measurable[hS.measurableSpace.prod inferInstance] fun p : Ω × ℝ =>
      stepWr β a Y p.1 (min (stepAr β a Y p.1 (stepTr S p.1) + max p.2 0) (stepTr S p.1)) := by
  have hsp := measurable_stepWcp_stop (β := β) hF hYp a hS
  have hA := measurable_stepAlphaStop (β := β) hF hYp a hS
  have hg : Measurable[hS.measurableSpace.prod inferInstance] fun p : Ω × ℝ =>
      (stepAr β a Y p.1 (stepTr S p.1) + max p.2 0).toNNReal := by
    refine Measurable.real_toNNReal ?_
    exact (@Measurable.comp _ _ _ (hS.measurableSpace.prod inferInstance) _ _ _ _ hA
      (@measurable_fst Ω ℝ hS.measurableSpace _)).add
      ((@measurable_snd Ω ℝ hS.measurableSpace _).max measurable_const)
  have hP : Measurable[hS.measurableSpace.prod inferInstance] fun p : Ω × ℝ =>
      (stepWcp β hYp a p.1).stop (stopReal S p.1) :=
    @Measurable.comp _ _ _ (hS.measurableSpace.prod inferInstance) _ _ _ _ hsp
      (@measurable_fst Ω ℝ hS.measurableSpace _)
  have h := @measurable_fn_at (Fin d → ℤ) _ _ _ (Ω × ℝ) (hS.measurableSpace.prod inferInstance)
    _ hP _ hg
  have e : (fun p : Ω × ℝ => stepWr β a Y p.1
        (min (stepAr β a Y p.1 (stepTr S p.1) + max p.2 0) (stepTr S p.1))) =
      fun p => ((stepWcp β hYp a p.1).stop (stopReal S p.1)).fn
        ((stepAr β a Y p.1 (stepTr S p.1) + max p.2 0).toNNReal) := by
    funext p
    show stepReg β (stepShift a (Y p.1))
        (min (stepAr β a Y p.1 (stepTr S p.1) + max p.2 0) (stepTr S p.1)).toNNReal =
      stepReg β (stepShift a (Y p.1))
        (min (stepAr β a Y p.1 (stepTr S p.1) + max p.2 0).toNNReal (stopReal S p.1))
    congr 1
    rw [Monotone.map_min (f := Real.toNNReal) (fun _ _ h => Real.toNNReal_mono h), stepTr, Real.toNNReal_coe]
  rw [e]
  exact h

end ElboimSly.Paper.Step

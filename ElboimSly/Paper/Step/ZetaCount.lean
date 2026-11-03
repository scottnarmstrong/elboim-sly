/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Paper.Step.ZetaGap
public import ElboimSly.Paper.Step.ZetaThit
public import ElboimSly.Paper.Step.ZetaShift
public import ElboimSly.Paper.Step.ZetaCountAux
public import ElboimSly.Paper.Step.AvoidStopping
public import ElboimSly.Foundations.Concentration.GapCount
public import ElboimSly.Foundations.Concentration.BinomialTail
public import ElboimSly.Foundations.Concentration.BernoulliStopping
public import ElboimSly.Foundations.SRW.AdmissibleSRW
public import Mathlib

/-!
# Step 4 of Lemma 7.1: the number of excursions

ES22 Lemma 7.1, Step 4 (ES22 §7); counting long gaps, binomial tails (c).

`P(ζ_{n³+1} ≤ t_n) ≤ P(Bin(n³, ½) ≤ 4) ≤ e^{-n³/17}`.
-/

@[expose] public section

open MeasureTheory Set Filter Topology ElboimSly.SRW
open scoped ENNReal NNReal

namespace ElboimSly.Paper.Step

open ElboimSly.Paper

variable {d : ℕ}

theorem le_thitStop {β : ℝ} {Ω : Type*} {w : ℝ≥0 → Ω → Fin d → ℤ} {α : ℝ≥0 → Ω → ℝ≥0}
    {R : Ω → WithTop ℝ≥0} (ω : Ω) :
    R ω ≤ (stepThitStop β w α R ω : WithTop ℝ≥0) := by
  by_cases h : R ω = ⊤
  · have : stepThitStop β w α R ω = ⊤ := by unfold stepThitStop; rw [ite_eq_left h]
    rw [h, this]; exact le_rfl
  · rw [stepThitStop_of_ne h]
    obtain ⟨y, hy⟩ := WithTop.ne_top_iff_exists.1 h
    have hyz : stopReal R ω = y := by unfold stopReal; rw [← hy]; rfl
    rw [← hy, hyz]
    unfold stepThit
    refine le_iInf₂ fun s hs => ?_
    have : ((y : ℝ)) < s := hs.1
    have h2 := ENNReal.ofReal_le_ofReal this.le
    rw [ENNReal.ofReal_coe_nnreal] at h2
    exact h2

section events

variable {Ω : Type*} {β : ℝ}

/-- `{R + L ≤ thit_{(w,α)}(R)}`. -/
def zEvent (β : ℝ) (w : ℝ≥0 → Ω → Fin d → ℤ) (α : ℝ≥0 → Ω → ℝ≥0) (R : Ω → WithTop ℝ≥0)
    (L : ℝ≥0) : Set Ω :=
  {ω | R ω + (L : WithTop ℝ≥0) ≤ (stepThitStop β w α R ω : WithTop ℝ≥0)}

theorem mem_zEvent_of {w : ℝ≥0 → Ω → Fin d → ℤ} {α : ℝ≥0 → Ω → ℝ≥0} {R : Ω → WithTop ℝ≥0}
    {L : ℝ≥0} {ω : Ω}
    (h : ∀ t : ℝ≥0, R ω = t → ENNReal.ofReal ((t : ℝ) + L) ≤
      stepThit β (stepExt fun s => w s ω) (fun r => ((α r.toNNReal ω : ℝ≥0) : ℝ)) (t : ℝ)) :
    ω ∈ zEvent β w α R L := by
  by_cases hR : R ω = ⊤
  · have : stepThitStop β w α R ω = ⊤ := by unfold stepThitStop; rw [ite_eq_left hR]
    show R ω + (L : WithTop ℝ≥0) ≤ (stepThitStop β w α R ω : WithTop ℝ≥0)
    rw [hR, this]
    exact le_rfl
  · obtain ⟨t, ht⟩ := WithTop.ne_top_iff_exists.1 hR
    have hz : stopReal R ω = t := by unfold stopReal; rw [← ht]; rfl
    have := h t ht.symm
    show R ω + (L : WithTop ℝ≥0) ≤ (stepThitStop β w α R ω : WithTop ℝ≥0)
    rw [stepThitStop_of_ne hR, hz, ← ht]
    rw [ENNReal.ofReal_add (NNReal.coe_nonneg _) (NNReal.coe_nonneg _), ENNReal.ofReal_coe_nnreal,
      ENNReal.ofReal_coe_nnreal] at this
    exact this

theorem measurableSet_zEvent {m : MeasurableSpace Ω} {f : Filtration ℝ≥0 m} (hβ : 1 < β)
    {w : ℝ≥0 → Ω → Fin d → ℤ} {α : ℝ≥0 → Ω → ℝ≥0} (h : ZetaProc f w α) {R : Ω → WithTop ℝ≥0}
    (hR : IsStoppingTime f R) (L : ℝ≥0) : MeasurableSet (zEvent β w α R L) := by
  have hT := isStoppingTime_stepThit' hβ f w α h.adapted h.alpha h.fin hR
  have := measurableSet_add_const_le_stopping hR hT hT (fun ω => le_thitStop ω)
    (fun ω => le_rfl) L
  exact hT.measurableSpace_le _ this

end events

end ElboimSly.Paper.Step

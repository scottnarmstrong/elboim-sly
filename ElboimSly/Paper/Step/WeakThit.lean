/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Paper.Step.WeakEvents
public import Mathlib

/-!
# `thit(R)` is a stopping time under the local event hypothesis

Structure of relaxed times; stopping times (d).

`{thit(R) ≤ t}` only depends on the paths up to time `t + 1`, so it is read off the paths truncated
at `t + 1`, which are eventually constant.
-/

@[expose] public section

open MeasureTheory Set Filter Topology
open scoped ENNReal NNReal

namespace ElboimSly.Paper.Step

open ElboimSly.Paper

variable {d : ℕ}

/-- `{thit ≤ t}` only depends on the data up to time `t + 1`. -/
theorem stepThit_le_of_agree {β : ℝ} {w w' : ℝ → Fin d → ℤ} {α α' : ℝ → ℝ} {T t : ℝ} (ht : 0 ≤ t)
    (hw : ∀ s, s ≤ t + 1 → w s = w' s) (hα : T ≤ t + 1 → α T = α' T)
    (h : stepThit β w α T ≤ ENNReal.ofReal t) : stepThit β w' α' T ≤ ENNReal.ofReal t := by
  refine le_of_forall_gt_imp_ge_of_dense fun c hc => ?_
  set c'' := min c (ENNReal.ofReal (t + 1)) with hc''
  have hlt : stepThit β w α T < c'' := by
    refine lt_of_le_of_lt h (lt_min hc ?_)
    exact (ENNReal.ofReal_lt_ofReal_iff (by linarith)).2 (by linarith)
  unfold stepThit at hlt
  rw [iInf_lt_iff] at hlt
  obtain ⟨s, hs⟩ := hlt
  rw [iInf_lt_iff] at hs
  obtain ⟨⟨hTs, s', ⟨k, hk⟩, hαs, hs't, hn⟩, hslt⟩ := hs
  have hs1 : s < t + 1 := by
    have : ENNReal.ofReal s < ENNReal.ofReal (t + 1) := hslt.trans_le (min_le_right _ _)
    exact (ENNReal.ofReal_lt_ofReal_iff').1 this |>.1
  have hTle : T ≤ t + 1 := by linarith
  have hmem : s ∈ {s : ℝ | T < s ∧ ∃ s' : ℝ, (∃ k : ℤ, s' = s + k * β) ∧ α' T < s' ∧ s' < T ∧
      ‖w' s - w' s'‖ ≤ 1} :=
    ⟨hTs, s', ⟨k, hk⟩, by rw [← hα hTle]; exact hαs, hs't, by
      rw [← hw s hs1.le, ← hw s' (by linarith)]; exact hn⟩
  unfold stepThit
  exact (iInf₂_le s hmem).trans (hslt.trans_le (min_le_left _ _)).le

theorem toNNReal_min_coe (s : ℝ) (M : ℝ≥0) : (min s (M : ℝ)).toNNReal = min s.toNNReal M := by
  rcases le_total s (M : ℝ) with h | h
  · rw [min_eq_left h, min_eq_left]
    exact Real.toNNReal_le_iff_le_coe.2 h
  · rw [min_eq_right h, Real.toNNReal_coe, min_eq_right]
    rw [← Real.toNNReal_coe (r := M)]
    exact Real.toNNReal_mono h

variable {Ω : Type*} {m : MeasurableSpace Ω}

/-- **`thit(R)` is a stopping time** under the local event hypothesis
(structure of relaxed times; stopping times (d)). -/
theorem isStoppingTime_stepThit' {β : ℝ} (hβ : 1 < β) (f : Filtration ℝ≥0 m)
    (w : ℝ≥0 → Ω → Fin d → ℤ) (α : ℝ≥0 → Ω → ℝ≥0)
    (hw : ∀ t, Measurable[f t] (w t)) (hα : ∀ t, Measurable[f t] (α t))
    (hfin : ∀ ω, StepEventsFiniteW (stepExt fun s => w s ω)
      (fun r => ((α r.toNNReal ω : ℝ≥0) : ℝ)))
    {R : Ω → WithTop ℝ≥0} (hR : IsStoppingTime f R) :
    IsStoppingTime f (fun ω => (stepThitStop β w α R ω : WithTop ℝ≥0)) := by
  intro t
  show MeasurableSet[f t] {ω | (stepThitStop β w α R ω : WithTop ℝ≥0) ≤ t}
  set M : ℝ≥0 := t + 1 with hM
  have hwt : ∀ u, Measurable[f u] fun ω => w (min u M) ω := fun u =>
    (hw (min u M)).mono (f.mono (min_le_left u M)) le_rfl
  have hαt : ∀ u, Measurable[f u] fun ω => α (min u M) ω := fun u =>
    (hα (min u M)).mono (f.mono (min_le_left u M)) le_rfl
  have hfint : ∀ ω, StepEventsFinite (stepExt fun s => w (min s M) ω)
      (fun r => ((α (min r.toNNReal M) ω : ℝ≥0) : ℝ)) := by
    intro ω
    have := (hfin ω).trunc (M : ℝ) M.2
    have e1 : (fun s : ℝ => stepExt (fun s => w s ω) (min s (M : ℝ))) =
        stepExt fun s => w (min s M) ω := by
      funext s; simp only [stepExt]; rw [toNNReal_min_coe]
    have e2 : (fun s : ℝ => ((α (min s (M : ℝ)).toNNReal ω : ℝ≥0) : ℝ)) =
        fun r => ((α (min r.toNNReal M) ω : ℝ≥0) : ℝ) := by
      funext s; rw [toNNReal_min_coe]
    rw [e1, e2] at this
    exact this
  have key := isStoppingTime_stepThit hβ f (fun u ω => w (min u M) ω) (fun u ω => α (min u M) ω)
    hwt hαt hfint hR t
  have heq : {ω | (stepThitStop β w α R ω : WithTop ℝ≥0) ≤ t} =
      {ω | (stepThitStop β (fun u ω => w (min u M) ω) (fun u ω => α (min u M) ω) R ω :
        WithTop ℝ≥0) ≤ t} := by
    ext ω
    simp only [mem_ofPred_eq]
    by_cases hRt : R ω = ⊤
    · simp [stepThitStop, hRt]
    · have e : ∀ (x : ℝ≥0∞), (x : WithTop ℝ≥0) ≤ t ↔ x ≤ ENNReal.ofReal t := fun x => by
        rw [ENNReal.ofReal_coe_nnreal]
      rw [e, e]
      simp only [stepThitStop, hRt, ite_false]
      have ht0 : (0 : ℝ) ≤ t := t.2
      have hmin : ∀ s : ℝ, s ≤ (t : ℝ) + 1 → min s.toNNReal M = s.toNNReal := by
        intro s hs
        refine min_eq_left ?_
        rw [hM]
        exact Real.toNNReal_le_iff_le_coe.2 (by push_cast; linarith)
      have hagw : ∀ s : ℝ, s ≤ (t : ℝ) + 1 → stepExt (fun s => w s ω) s =
          stepExt (fun s => w (min s M) ω) s := by
        intro s hs
        simp only [stepExt]
        rw [hmin s hs]
      have hagw' : ∀ s : ℝ, s ≤ (t : ℝ) + 1 → stepExt (fun s => w (min s M) ω) s =
          stepExt (fun s => w s ω) s := fun s hs => (hagw s hs).symm
      have hagα : ∀ T : ℝ, T ≤ (t : ℝ) + 1 →
          ((α T.toNNReal ω : ℝ≥0) : ℝ) = ((α (min T.toNNReal M) ω : ℝ≥0) : ℝ) := by
        intro T hT
        rw [hmin T hT]
      constructor
      · exact stepThit_le_of_agree ht0 hagw (hagα _)
      · exact stepThit_le_of_agree ht0 hagw' fun hT => (hagα _ hT).symm
  rw [heq]
  exact key

end ElboimSly.Paper.Step

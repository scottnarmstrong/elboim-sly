/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Paper.Step.RelaxedStoppingApp
public import ElboimSly.Paper.Step.ThitStopping
public import Mathlib

/-!
# Local event finiteness

`StepEventsFinite` of `Step/RelaxedStoppingApp` demands that `w` and `α` be constant after the last
event, so it holds only for eventually constant paths. The regenerated walk has infinitely many events,
with finitely many in each bounded interval. `StepEventsFiniteW` is the correct local form: constancy
between events is required only up to the level `M`.

By truncating at a level (`StepEventsFiniteW.trunc`) the results of `Step/RelaxedStoppingApp` and
`Step/ThitStopping` transfer: `isLocIco_stepRelaxedSet'` and `isStoppingTime_stepThit'`.
-/

@[expose] public section

open MeasureTheory Set Filter Topology
open scoped ENNReal NNReal

namespace ElboimSly.Paper.Step

open ElboimSly.Paper

variable {d : ℕ}

/-- Local finiteness of the events of `(w, α)`: constancy between events up to each level `M`. -/
def StepEventsFiniteW (w : ℝ → Fin d → ℤ) (α : ℝ → ℝ) : Prop :=
  (∀ e : ℝ, 0 ≤ e → 0 ≤ α e ∧ α e ≤ e) ∧
  ∀ M : ℝ, ∃ E : Finset ℝ, 0 ∈ E ∧ (∀ x ∈ E, 0 ≤ x) ∧ (∃ x ∈ E, M < x) ∧
    ∀ e ∈ E, ∀ s, e ≤ s → s ≤ M → (∀ x ∈ E, x ≤ e ∨ s < x) → w s = w e ∧ α s = α e

theorem StepEventsFiniteW.trunc {w : ℝ → Fin d → ℤ} {α : ℝ → ℝ} (h : StepEventsFiniteW w α)
    (M0 : ℝ) (hM0 : 0 ≤ M0) :
    StepEventsFinite (fun s => w (min s M0)) (fun s => α (min s M0)) := by
  classical
  intro M
  obtain ⟨E, h0, hpos, htop, hpiece⟩ := h.2 M0
  refine ⟨(E.filter (· ≤ M0)) ∪ {M0, max M M0 + 1}, ?_, ?_, ?_, ?_, ?_⟩
  · simp [h0, hM0]
  · intro x hx
    simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with ⟨hx, -⟩ | rfl | rfl
    · exact hpos x hx
    · exact hM0
    · exact (hM0.trans (le_max_right _ _)).trans (by linarith)
  · exact ⟨max M M0 + 1, by simp, by linarith [le_max_left M M0]⟩
  · intro e he s hes hno
    simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_insert,
      Finset.mem_singleton] at he
    by_cases heM : M0 ≤ e
    · have hsM : M0 ≤ s := heM.trans hes
      simp [min_eq_right heM, min_eq_right hsM]
    · rw [not_le] at heM
      have heE : e ∈ E := by
        rcases he with ⟨he, -⟩ | rfl | rfl
        · exact he
        · exact absurd le_rfl (not_le.2 heM)
        · exact absurd (by linarith [le_max_right M M0]) (not_le.2 heM)
      have hsM : s < M0 := by
        have := hno M0 (by simp)
        rcases this with h1 | h1
        · exact absurd h1 (not_le.2 heM)
        · exact h1
      simp only [min_eq_left hsM.le, min_eq_left heM.le]
      refine hpiece e heE s hes hsM.le fun x hx => ?_
      by_cases hxM : x ≤ M0
      · exact hno x (by simp [hx, hxM])
      · exact Or.inr (lt_of_lt_of_le hsM (not_le.1 hxM).le)
  · intro e he
    simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_insert, Finset.mem_singleton] at he
    have he0 : 0 ≤ e := by
      rcases he with ⟨he, -⟩ | rfl | rfl
      · exact hpos e he
      · exact hM0
      · exact (hM0.trans (le_max_right _ _)).trans (by linarith)
    have := h.1 (min e M0) (le_min he0 hM0)
    exact ⟨this.1, this.2.trans (min_le_left _ _)⟩

/-- `𝒯` is locally of type `[l, r)` under the local form of the event hypothesis. -/
theorem isLocIco_stepRelaxedSet' {β : ℝ} (hd : 1 ≤ d) (hβ : 1 < β) {w : ℝ → Fin d → ℤ}
    {α : ℝ → ℝ} (h : StepEventsFiniteW w α) : IsLocIco (stepRelaxedSet β w α) := by
  intro M
  obtain ⟨L, hL, hLe⟩ := isLocIco_stepRelaxedSet hd hβ (h.trunc (max M 0) (le_max_right _ _)) M
  refine ⟨L, hL, ?_⟩
  rw [← hLe]
  ext t
  simp only [mem_inter_iff, Icc, mem_ofPred_eq, stepRelaxedSet]
  constructor
  · rintro ⟨⟨ht0, hrel⟩, h1, h2⟩
    refine ⟨⟨ht0, ?_⟩, h1, h2⟩
    have e1 : min t (max M 0) = t := min_eq_left (h2.trans (le_max_left _ _))
    rw [e1]
    refine (isRelaxedTimeWrt_congr_le (by linarith) (fun s hs0 hst => ?_) (h.1 t ht0).1 ht0).1 hrel
    simp [min_eq_left (hst.trans (h2.trans (le_max_left _ _)))]
  · rintro ⟨⟨ht0, hrel⟩, h1, h2⟩
    refine ⟨⟨ht0, ?_⟩, h1, h2⟩
    have e1 : min t (max M 0) = t := min_eq_left (h2.trans (le_max_left _ _))
    rw [e1] at hrel
    refine (isRelaxedTimeWrt_congr_le (by linarith) (fun s hs0 hst => ?_) (h.1 t ht0).1 ht0).2 hrel
    simp [min_eq_left (hst.trans (h2.trans (le_max_left _ _)))]

end ElboimSly.Paper.Step

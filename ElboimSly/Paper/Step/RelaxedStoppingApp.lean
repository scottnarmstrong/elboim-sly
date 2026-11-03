/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Paper.Step.RelaxedStopping2
public import ElboimSly.Paper.Step.RelaxedAdapted
public import Mathlib

/-!
# Stopping times built from the relaxed set `𝒯`

Structure of relaxed times; stopping times (a), (d) for `U = 𝒯`.
-/

@[expose] public section

open MeasureTheory Set Filter Topology
open scoped ENNReal NNReal

namespace ElboimSly.Paper

variable {d : ℕ}

/-- The event times of `(w, α)` are locally finite: on each bounded interval `w` and `α` are
constant between the points of a finite set `E` of non-negative times with `0 ∈ E`, and
`0 ≤ α e ≤ e` at those points. This is the hypothesis "finitely many jumps in bounded intervals"
of structure of relaxed times; stopping times. -/
def StepEventsFinite (w : ℝ → Fin d → ℤ) (α : ℝ → ℝ) : Prop :=
  ∀ M : ℝ, ∃ E : Finset ℝ, 0 ∈ E ∧ (∀ x ∈ E, 0 ≤ x) ∧ (∃ x ∈ E, M < x) ∧
    (∀ e ∈ E, ∀ s, e ≤ s → (∀ x ∈ E, x ≤ e ∨ s < x) → w s = w e ∧ α s = α e) ∧
    ∀ e ∈ E, 0 ≤ α e ∧ α e ≤ e

/-- Structure of relaxed times; stopping times (a): `𝒯` is locally of type `[l, r)`. -/
theorem isLocIco_stepRelaxedSet {β : ℝ} (hd : 1 ≤ d) (hβ : 1 < β) {w : ℝ → Fin d → ℤ}
    {α : ℝ → ℝ} (h : StepEventsFinite w α) : IsLocIco (stepRelaxedSet β w α) := by
  intro M
  obtain ⟨E, h0, hpos, htop, hpiece, hα⟩ := h M
  exact relaxedSet_finite_union hd hβ E h0 hpos htop hpiece hα

variable {Ω : Type*} {m : MeasurableSpace Ω}

/-- The real-time relaxed set of the sample path `ω`. -/
def stepRelaxedSetOf (β : ℝ) (w : ℝ≥0 → Ω → Fin d → ℤ) (α : ℝ≥0 → Ω → ℝ≥0) (ω : Ω) :
    Set ℝ :=
  stepRelaxedSet β (stepExt fun s => w s ω) (fun r => ((α r.toNNReal ω : ℝ≥0) : ℝ))

end ElboimSly.Paper

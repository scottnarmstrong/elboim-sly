/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Foundations.SRW.Lemma82E2
public import ElboimSly.Foundations.SRW.CountableReduction
public import Mathlib

/-!
# Regular events defined by pairs of times

Countable reduction of path events (iii); used for SRW content of Lemma 8.2 (c).
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Real

namespace ElboimSly
namespace SRW

variable {d : ℕ}

theorem isRegSet_pair (G : (Fin d → ℤ) → (Fin d → ℤ) → Prop) (b h : ℝ≥0) :
    IsRegSet {γ : PathSpace d | ∃ s s' : ℝ≥0, 0 ≤ s ∧ s ≤ s' ∧ s' ≤ b ∧ s' - s ≤ h ∧
      G (γ s) (γ s')} := by
  classical
  set Q : Set ℝ≥0 := range ratNN ∪ {b} with hQ
  have hQc : Q.Countable := (countable_range _).union (countable_singleton _)
  set V : Set (PathSpace d) := ⋃ q ∈ Q, ⋃ q' ∈ Q,
    {γ | q ≤ q' ∧ q' ≤ b ∧ q' - q ≤ h ∧ G (γ q) (γ q')} with hV
  refine ⟨V, ?_, fun γ hγ => ?_⟩
  · refine MeasurableSet.biUnion hQc fun q _ => MeasurableSet.biUnion hQc fun q' _ => ?_
    by_cases hc : q ≤ q' ∧ q' ≤ b ∧ q' - q ≤ h
    · have : {γ : PathSpace d | q ≤ q' ∧ q' ≤ b ∧ q' - q ≤ h ∧ G (γ q) (γ q')} =
          (fun γ : PathSpace d => (γ q, γ q')) ⁻¹' {p | G p.1 p.2} := by
        ext γ; simp [hc]
      rw [this]
      exact ((measurable_pi_apply q).prodMk (measurable_pi_apply q')) (MeasurableSet.of_discrete)
    · have : {γ : PathSpace d | q ≤ q' ∧ q' ≤ b ∧ q' - q ≤ h ∧ G (γ q) (γ q')} = ∅ := by
        ext γ; simp only [mem_ofPred_eq, mem_empty_iff_false, iff_false]
        exact fun ⟨a, b', c, _⟩ => hc ⟨a, b', c⟩
      rw [this]; exact MeasurableSet.empty
  · have := hγ.exists_pair_iff G (a := 0) (b := b) (h := h) bot_le
    simp only [mem_ofPred_eq, hV, mem_iUnion]
    rw [this]
    constructor
    · rintro ⟨q, q', hq, hq', -, h1, h2, h3, h4⟩
      exact ⟨q, hq, q', hq', h1, h2, h3, h4⟩
    · rintro ⟨q, hq, q', hq', h1, h2, h3, h4⟩
      exact ⟨q, q', hq, hq', bot_le, h1, h2, h3, h4⟩

end SRW
end ElboimSly

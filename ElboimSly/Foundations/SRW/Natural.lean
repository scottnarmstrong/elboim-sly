/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Foundations.SRW.SrwDef
public import Mathlib

/-!
# Integrality of counts on the good event

Good event and path properties (integrality part).  For `ν ∈ goodSet d` all counts
`ν ({v} × I)` of bounded intervals `I ⊆ (0,∞)` are natural numbers.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal

namespace ElboimSly
namespace SRW

/-- An infimum of natural numbers (in `[0,∞]`) is attained. -/
theorem exists_eq_iInf_of_nat {ι : Type*} [Nonempty ι] (g : ι → ℝ≥0∞)
    (h : ∀ i, ∃ n : ℕ, g i = n) : ∃ i, g i = ⨅ j, g j := by
  choose f hf using h
  obtain ⟨i0⟩ := ‹Nonempty ι›
  obtain ⟨m, ⟨i, rfl⟩, hm⟩ := wellFounded_lt.has_min (Set.range f) ⟨f i0, i0, rfl⟩
  refine ⟨i, ?_⟩
  refine le_antisymm (le_iInf fun j => ?_) (iInf_le _ _)
  rw [hf, hf]
  exact_mod_cast not_lt.1 (hm (f j) ⟨j, rfl⟩)

/-- Along a countable directed-downwards family of measurable sets with natural measures, the
measure of the intersection is attained. -/
theorem exists_measure_eq_iInter {α : Type*} [MeasurableSpace α] (μ : Measure α) {ι : Type*}
    [Countable ι] [Nonempty ι] (s : ι → Set α) (hs : ∀ i, MeasurableSet (s i))
    (hd : Directed (· ⊇ ·) s) (hn : ∀ i, ∃ n : ℕ, μ (s i) = n) :
    ∃ i, μ (s i) = μ (⋂ j, s j) := by
  obtain ⟨i0⟩ := ‹Nonempty ι›
  obtain ⟨n0, hn0⟩ := hn i0
  have hfin : ∃ i, μ (s i) ≠ ∞ := ⟨i0, by rw [hn0]; exact ENNReal.natCast_ne_top _⟩
  rw [hd.measure_iInter (fun i => (hs i).nullMeasurableSet) hfin]
  exact exists_eq_iInf_of_nat _ hn

end SRW
end ElboimSly

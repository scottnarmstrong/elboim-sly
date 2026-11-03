/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Paper.Base.H1Version
public import Mathlib

/-!
# (H1) at the base: measure of the relaxed times

ES22 Lemma 8.1, Step 4.

* `h1_relTimes_volume`: if (R1) holds at every time of `[0,T]` and the set of times where (R2)
  fails has measure at most `T/20`, then the relaxed times have measure at least `19 T / 20`.
-/

@[expose] public section

open MeasureTheory Set
open scoped ENNReal NNReal

namespace ElboimSly.Paper

open ElboimSly.SRW

variable {d : ℕ}

/-- The times of `[0,T]` at which (R2) fails for the stopped path. -/
def h1BadTimes (β : ℝ) (T : ℝ≥0) (γ : PathSpace d) : Set ℝ :=
  {t | t ∈ Icc (0 : ℝ) T ∧ ¬ ∀ s : ℝ, 0 ≤ s → s ≤ t - β ^ (3 * indDelta d) →
    β ^ indDelta d ≤ ‖h1Walk T γ t - h1Walk T γ s‖}

theorem h1_relTimes_volume {β : ℝ} {T : ℝ≥0} {γ : PathSpace d}
    (hR1 : ∀ t : ℝ, 0 ≤ t → t ≤ T → ∀ r : ℝ, β ^ indDelta d ≤ r →
      ¬ IsHeavy (h1Walk T γ) 0 t (h1Walk T γ t) r)
    (hBd : volume (h1BadTimes β T γ) ≤ ENNReal.ofReal ((T : ℝ) / 20)) :
    ENNReal.ofReal (19 / 20 * (T : ℝ)) ≤ volume (h1RelTimes β T γ) := by
  have hsub : Icc (0 : ℝ) T ⊆ h1RelTimes β T γ ∪ h1BadTimes β T γ := by
    intro t ht
    by_cases h2 : ∀ s : ℝ, 0 ≤ s → s ≤ t - β ^ (3 * indDelta d) →
        β ^ indDelta d ≤ ‖h1Walk T γ t - h1Walk T γ s‖
    · exact Or.inl ⟨ht, hR1 t ht.1 ht.2, h2⟩
    · exact Or.inr ⟨ht, h2⟩
  have h1 : ENNReal.ofReal (T : ℝ) ≤ volume (h1RelTimes β T γ) + ENNReal.ofReal ((T : ℝ) / 20) := by
    calc ENNReal.ofReal (T : ℝ) = volume (Icc (0 : ℝ) T) := by simp
      _ ≤ volume (h1RelTimes β T γ ∪ h1BadTimes β T γ) := measure_mono hsub
      _ ≤ volume (h1RelTimes β T γ) + volume (h1BadTimes β T γ) := measure_union_le _ _
      _ ≤ _ := by gcongr
  have hT0 : (0 : ℝ) ≤ T := T.2
  have e : ENNReal.ofReal (T : ℝ) =
      ENNReal.ofReal (19 / 20 * (T : ℝ)) + ENNReal.ofReal ((T : ℝ) / 20) := by
    rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
    congr 1; ring
  rw [e] at h1
  exact (ENNReal.add_le_add_iff_right ENNReal.ofReal_ne_top).1 h1

end ElboimSly.Paper

end

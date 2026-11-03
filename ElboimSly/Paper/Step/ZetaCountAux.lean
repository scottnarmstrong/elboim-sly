/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import Mathlib

/-!
# Two events of conditional probability at least `1 - c` have intersection of probability
at least `1 - 2c`

ES22 Lemma 7.1, Step 4 (the success probability `p = 1/2`).
-/

@[expose] public section

open MeasureTheory Set

namespace ElboimSly.Paper.Step

theorem half_le_inter {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {H E₁ E₂ A : Set Ω} {c : ℝ} (hc : c ≤ 1 / 4) (hH : MeasurableSet H) (hE₁ : MeasurableSet E₁)
    (hinc : H ∩ E₁ ∩ E₂ ⊆ H ∩ A)
    (h1 : (1 - c) * P.real H ≤ P.real (H ∩ E₁)) (h2 : (1 - c) * P.real H ≤ P.real (H ∩ E₂)) :
    (1 / 2) * P.real H ≤ P.real (H ∩ A) := by
  have hu := measureReal_union_add_inter₀ (μ := P) (s := H ∩ E₂) (t := H ∩ E₁)
    (hH.inter hE₁).nullMeasurableSet
  have hU : P.real ((H ∩ E₂) ∪ (H ∩ E₁)) ≤ P.real H :=
    measureReal_mono (union_subset inter_subset_left inter_subset_left)
  have hI : P.real ((H ∩ E₂) ∩ (H ∩ E₁)) ≤ P.real (H ∩ A) := by
    refine measureReal_mono ?_
    intro x hx
    exact hinc ⟨⟨hx.2.1, hx.2.2⟩, hx.1.2⟩
  have h0 : 0 ≤ P.real H := measureReal_nonneg
  nlinarith

end ElboimSly.Paper.Step

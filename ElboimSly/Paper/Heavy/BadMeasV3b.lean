/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Paper.Heavy.BadMeasV3

/-!
# Measurability of badness: merging and proximity volume

Properties of discovered bad blocks (c), (d).

* `AdaptedCyclic.measurableSet_segMerge`.
* `proxSet_eq_rat`: pathwise, `𝔓(x₁, x₂)` is described through rational times only.
* `AdaptedCyclic.measurable_proxVol`: `ω ↦ |𝔓(x₁, x₂)|` is `ℱ_t`-measurable.
-/

@[expose] public section

open MeasureTheory Set Filter Topology
open scoped ENNReal NNReal

namespace ElboimSly.Paper

open ElboimSly

variable {d : ℕ} {Ω : Type*} {m : MeasurableSpace Ω} {f : Filtration ℝ≥0 m}
  {W : Ω → ℝ → Fin d → ℤ}

theorem AdaptedCyclic.measurableSet_segMerge (h : AdaptedCyclic f W) {β tk x₁ x₂ : ℝ}
    {t : ℝ≥0} (htk : 0 ≤ tk) (hx₁ : 0 ≤ x₁) (hx₂ : 0 ≤ x₂) (h1t : x₁ + tk ≤ t)
    (h2t : x₂ + tk ≤ t) : MeasurableSet[f t] {ω | SegMerge β tk (W ω) x₁ x₂} := by
  have hset : {ω | SegMerge β tk (W ω) x₁ x₂} =
      ⋃ ℓ : ℤ, ⋃ _ : mergeLo β x₁ x₂ ℓ ≤ mergeHi β tk x₁ x₂ ℓ,
        ({ω | W ω (x₁ + mergeHi β tk x₁ x₂ ℓ) =
            W ω (x₂ + (mergeHi β tk x₁ x₂ ℓ + mergeShift β x₁ x₂ ℓ))} ∪
          ⋃ q : {q : ℚ // mergeLo β x₁ x₂ ℓ < (q : ℝ) ∧ (q : ℝ) < mergeHi β tk x₁ x₂ ℓ},
            {ω | W ω (x₁ + q) = W ω (x₂ + (q + mergeShift β x₁ x₂ ℓ))}) := by
    ext ω
    simp only [mem_ofPred_eq, mem_iUnion, mem_union, exists_prop]
    rw [segMerge_iff_rat (h.path ω) htk hx₁ hx₂]
    refine exists_congr fun ℓ => and_congr Iff.rfl ?_
    constructor
    · rintro (h1 | ⟨q, h2, h3, h4⟩)
      · exact Or.inl h1
      · exact Or.inr ⟨⟨q, h2, h3⟩, h4⟩
    · rintro (h1 | ⟨q, h4⟩)
      · exact Or.inl h1
      · exact Or.inr ⟨q.1, q.2.1, q.2.2, h4⟩
  rw [hset]
  refine MeasurableSet.iUnion fun ℓ => MeasurableSet.iUnion fun hab => ?_
  have hlo0 : 0 ≤ mergeLo β x₁ x₂ ℓ := le_max_left _ _
  have hlo1 : -(mergeShift β x₁ x₂ ℓ) ≤ mergeLo β x₁ x₂ ℓ := le_max_right _ _
  have hhi1 : mergeHi β tk x₁ x₂ ℓ ≤ tk := min_le_left _ _
  have hhi2 : mergeHi β tk x₁ x₂ ℓ ≤ tk - mergeShift β x₁ x₂ ℓ := min_le_right _ _
  have key : ∀ u, mergeLo β x₁ x₂ ℓ ≤ u → u ≤ mergeHi β tk x₁ x₂ ℓ →
      MeasurableSet[f t] {ω | W ω (x₁ + u) = W ω (x₂ + (u + mergeShift β x₁ x₂ ℓ))} := by
    intro u hu1 hu2
    exact h.measurableSet_eq (by linarith) (by linarith) (by linarith) (by linarith)
  refine (key _ hab le_rfl).union (MeasurableSet.iUnion fun q => key q q.2.1.le q.2.2.le)

/-- Pathwise, `𝔓(x₁, x₂)` only involves rational times for the inner existential. -/
theorem proxSet_eq_rat {w : ℝ → Fin d → ℤ} (hw : IsCyclicPath w) {tk ρ x₁ x₂ : ℝ}
    (htk : 0 ≤ tk) (hx₁ : 0 ≤ x₁) (_hx₂ : 0 ≤ x₂) :
    proxSet tk w ρ x₁ x₂ = {u₂ : ℝ | u₂ ∈ Icc 0 tk ∧
      (‖w (x₁ + tk) - w (x₂ + u₂)‖ ≤ ρ ∨ ∃ q : ℚ, 0 < (q : ℝ) ∧ (q : ℝ) < tk ∧
        ‖w (x₁ + q) - w (x₂ + u₂)‖ ≤ ρ)} := by
  ext u₂
  simp only [proxSet, mem_ofPred_eq]
  refine and_congr_right fun hu₂ => ?_
  have hP : ∀ u ∈ Icc (0 : ℝ) tk, ∃ η > 0, ∀ u' ∈ Ico u (u + η),
      (‖w (x₁ + u') - w (x₂ + u₂)‖ ≤ ρ ↔ ‖w (x₁ + u) - w (x₂ + u₂)‖ ≤ ρ) := by
    intro u hu
    obtain ⟨η, hη, h1⟩ := hw.exists_plateau (show 0 ≤ x₁ + u by linarith [hu.1])
    refine ⟨η, hη, fun u' hu' => ?_⟩
    rw [h1 (x₁ + u') ⟨by linarith [hu'.1], by linarith [hu'.2]⟩]
  exact exists_Icc_iff_rat htk hP

end ElboimSly.Paper

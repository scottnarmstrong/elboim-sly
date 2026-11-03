/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Paper.Heavy.BadMeasV12

/-!
# Measurability of badness: merging and proximity, condition (V3)

Properties of discovered bad blocks (c), (d).

* `segMerge_iff_rat`: merging of two segments, pathwise: for each of the countably many `ℓ ∈ ℤ`,
  merging with shift `ℓβ` is an existential over an interval of a right-open property, which
  reduces to rational times (`exists_Icc_iff_rat`).
* `AdaptedCyclic.measurableSet_segMerge`.
-/

@[expose] public section

open MeasureTheory Set Filter Topology
open scoped ENNReal NNReal

namespace ElboimSly.Paper

open ElboimSly

variable {d : ℕ}

/-- The time shift `δ_ℓ = x₁ - x₂ - ℓβ` between the two segments when `u₂ = u₁ + δ_ℓ`. -/
def mergeShift (β x₁ x₂ : ℝ) (ℓ : ℤ) : ℝ := x₁ - x₂ - ℓ * β

/-- Lower end of the admissible `u₁` for the shift `ℓ`. -/
def mergeLo (β x₁ x₂ : ℝ) (ℓ : ℤ) : ℝ := max 0 (-(mergeShift β x₁ x₂ ℓ))

/-- Upper end of the admissible `u₁` for the shift `ℓ`. -/
def mergeHi (β tk x₁ x₂ : ℝ) (ℓ : ℤ) : ℝ := min tk (tk - mergeShift β x₁ x₂ ℓ)

theorem segMerge_iff_rat {w : ℝ → Fin d → ℤ} (hw : IsCyclicPath w) {β tk x₁ x₂ : ℝ}
    (_htk : 0 ≤ tk) (hx₁ : 0 ≤ x₁) (hx₂ : 0 ≤ x₂) :
    SegMerge β tk w x₁ x₂ ↔ ∃ ℓ : ℤ, mergeLo β x₁ x₂ ℓ ≤ mergeHi β tk x₁ x₂ ℓ ∧
      (w (x₁ + mergeHi β tk x₁ x₂ ℓ) = w (x₂ + (mergeHi β tk x₁ x₂ ℓ + mergeShift β x₁ x₂ ℓ)) ∨
        ∃ q : ℚ, mergeLo β x₁ x₂ ℓ < (q : ℝ) ∧ (q : ℝ) < mergeHi β tk x₁ x₂ ℓ ∧
          w (x₁ + q) = w (x₂ + (q + mergeShift β x₁ x₂ ℓ))) := by
  constructor
  · rintro ⟨u₁, u₂, hu1, hu2, hwe, ℓ, hℓ⟩
    have hu2e : u₂ = u₁ + mergeShift β x₁ x₂ ℓ := by unfold mergeShift; linarith
    have hlo : mergeLo β x₁ x₂ ℓ ≤ u₁ := max_le hu1.1 (by linarith [hu2.1])
    have hhi : u₁ ≤ mergeHi β tk x₁ x₂ ℓ := le_min hu1.2 (by linarith [hu2.2])
    refine ⟨ℓ, hlo.trans hhi, ?_⟩
    have hP : ∀ u ∈ Icc (mergeLo β x₁ x₂ ℓ) (mergeHi β tk x₁ x₂ ℓ), ∃ η > 0,
        ∀ u' ∈ Ico u (u + η), (w (x₁ + u') = w (x₂ + (u' + mergeShift β x₁ x₂ ℓ)) ↔
          w (x₁ + u) = w (x₂ + (u + mergeShift β x₁ x₂ ℓ))) := by
      intro u hu
      have hu0 : 0 ≤ u := (le_max_left _ _).trans hu.1
      have hu0' : 0 ≤ u + mergeShift β x₁ x₂ ℓ := by
        have := (le_max_right _ _).trans hu.1
        linarith
      obtain ⟨η1, hη1, h1⟩ := hw.exists_plateau (show 0 ≤ x₁ + u by linarith)
      obtain ⟨η2, hη2, h2⟩ := hw.exists_plateau (show 0 ≤ x₂ + (u + mergeShift β x₁ x₂ ℓ) by
        linarith)
      refine ⟨min η1 η2, lt_min hη1 hη2, fun u' hu' => ?_⟩
      rw [h1 (x₁ + u') ⟨by linarith [hu'.1], by linarith [hu'.2, min_le_left η1 η2]⟩,
        h2 (x₂ + (u' + mergeShift β x₁ x₂ ℓ))
          ⟨by linarith [hu'.1], by linarith [hu'.2, min_le_right η1 η2]⟩]
    have := (exists_Icc_iff_rat (hlo.trans hhi) hP).1 ⟨u₁, ⟨hlo, hhi⟩, by rw [← hu2e]; exact hwe⟩
    exact this
  · rintro ⟨ℓ, hab, h⟩
    have key : ∀ u, mergeLo β x₁ x₂ ℓ ≤ u → u ≤ mergeHi β tk x₁ x₂ ℓ →
        w (x₁ + u) = w (x₂ + (u + mergeShift β x₁ x₂ ℓ)) → SegMerge β tk w x₁ x₂ := by
      intro u hu1 hu2 hwe
      have hl1 : 0 ≤ u := (le_max_left _ _).trans hu1
      have hl2 : -(mergeShift β x₁ x₂ ℓ) ≤ u := (le_max_right _ _).trans hu1
      have hh1 : u ≤ tk := hu2.trans (min_le_left _ _)
      have hh2 : u ≤ tk - mergeShift β x₁ x₂ ℓ := hu2.trans (min_le_right _ _)
      refine ⟨u, u + mergeShift β x₁ x₂ ℓ, ⟨hl1, hh1⟩, ⟨by linarith, by linarith⟩, hwe, ℓ, ?_⟩
      unfold mergeShift; ring
    rcases h with h | ⟨q, hq1, hq2, hq⟩
    · exact key _ hab le_rfl h
    · exact key q hq1.le hq2.le hq

end ElboimSly.Paper

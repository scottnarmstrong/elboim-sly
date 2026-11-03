/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Paper.Heavy.Lambda

/-!
# Badness by time `t` reads the path only on `[0, t]`

Properties of discovered bad blocks (a), last sentence.

If `w = w'` on `[0, t]` then a block is bad by time `t` for `w` iff for `w'`
(`badByTime_congr`), hence `badCount` and `badUnion` agree too.
-/

@[expose] public section

open MeasureTheory Set
open scoped ENNReal

namespace ElboimSly.Paper

open ElboimSly

variable {d : ℕ} {w w' : ℝ → Fin d → ℤ}

theorem visitedSet_congr {a t : ℝ} (h : ∀ s ∈ Icc a t, w s = w' s) :
    visitedSet w a t = visitedSet w' a t := by
  unfold visitedSet
  exact Set.image_congr h

theorem isRelaxedTimeWrt_congr {β a t : ℝ} (hβ : 0 < β) (h : ∀ s ∈ Icc a t, w s = w' s)
    (hat : a ≤ t) : IsRelaxedTimeWrt β w a t ↔ IsRelaxedTimeWrt β w' a t := by
  have ht : w t = w' t := h t ⟨hat, le_rfl⟩
  unfold IsRelaxedTimeWrt IsHeavy
  rw [visitedSet_congr h, ht]
  refine and_congr Iff.rfl ?_
  refine forall_congr' fun s => ?_
  refine forall_congr' fun hs => ?_
  refine forall_congr' fun hs2 => ?_
  have hp : 0 < β ^ (3 * indDelta d) := Real.rpow_pos_of_pos hβ _
  rw [h s ⟨hs, by linarith⟩]

section seg

variable {β tk t x : ℝ}

theorem segClosed_congr (h : ∀ s ∈ Icc 0 t, w s = w' s) (_htk : 0 ≤ tk) (hx : 0 ≤ x)
    (hxt : x + tk ≤ t) : SegClosed β tk w x ↔ SegClosed β tk w' x := by
  unfold SegClosed
  constructor <;> rintro ⟨u, hu0, hu1, hl, hw⟩ <;> refine ⟨u, hu0, hu1, hl, ?_⟩
  · rwa [← h x ⟨hx, by linarith⟩, ← h (x + u) ⟨by linarith, by linarith⟩]
  · rwa [h x ⟨hx, by linarith⟩, h (x + u) ⟨by linarith, by linarith⟩]

theorem segRelaxed_congr (hβ : 0 < β) {k' : ℕ} (h : ∀ s ∈ Icc 0 t, w s = w' s) (hx : 0 ≤ x)
    (hxt : x + tk ≤ t) : SegRelaxed β tk w k' x ↔ SegRelaxed β tk w' k' x := by
  unfold SegRelaxed
  have : {u : ℝ | u ∈ Icc 0 tk ∧ IsRelaxedTimeWrt β w x (x + u)} =
      {u : ℝ | u ∈ Icc 0 tk ∧ IsRelaxedTimeWrt β w' x (x + u)} := by
    ext u
    simp only [mem_ofPred_eq]
    refine and_congr_right fun hu => isRelaxedTimeWrt_congr hβ (fun s hs => h s ⟨by linarith [hs.1],
      by linarith [hs.2, hu.2]⟩) (by linarith [hu.1])
  rw [this]

theorem segMerge_congr (h : ∀ s ∈ Icc 0 t, w s = w' s) (hx₁ : 0 ≤ x) {x₂ : ℝ} (hx₂ : 0 ≤ x₂)
    (hxt₁ : x + tk ≤ t) (hxt₂ : x₂ + tk ≤ t) :
    SegMerge β tk w x x₂ ↔ SegMerge β tk w' x x₂ := by
  unfold SegMerge
  constructor <;> rintro ⟨u₁, u₂, h1, h2, hw, hl⟩ <;> refine ⟨u₁, u₂, h1, h2, ?_, hl⟩
  · rwa [← h (x + u₁) ⟨by linarith [h1.1], by linarith [h1.2]⟩,
      ← h (x₂ + u₂) ⟨by linarith [h2.1], by linarith [h2.2]⟩]
  · rwa [h (x + u₁) ⟨by linarith [h1.1], by linarith [h1.2]⟩,
      h (x₂ + u₂) ⟨by linarith [h2.1], by linarith [h2.2]⟩]

theorem proxSet_congr (h : ∀ s ∈ Icc 0 t, w s = w' s) {ρ x₁ x₂ : ℝ} (hx₁ : 0 ≤ x₁) (hx₂ : 0 ≤ x₂)
    (hxt₁ : x₁ + tk ≤ t) (hxt₂ : x₂ + tk ≤ t) :
    proxSet tk w ρ x₁ x₂ = proxSet tk w' ρ x₁ x₂ := by
  ext u₂
  simp only [proxSet, mem_ofPred_eq]
  refine and_congr_right fun hu₂ => exists_congr fun u₁ => and_congr_right fun hu₁ => ?_
  rw [h (x₁ + u₁) ⟨by linarith [hu₁.1], by linarith [hu₁.2]⟩,
    h (x₂ + u₂) ⟨by linarith [hu₂.1], by linarith [hu₂.2]⟩]

end seg

variable {β t₀ : ℝ} {n : ℕ} {ι : Fin d → ℤ} {t : ℝ}

private theorem badByTime_congr_aux (hβ : 0 < β) (htk : 0 ≤ heavyTkPrime d t₀ n)
    (h : ∀ s ∈ Icc 0 t, w s = w' s) (hb : BadByTime d β t₀ n w ι t) :
    BadByTime d β t₀ n w' ι t := by
  unfold BadByTime at hb ⊢
  dsimp only at hb ⊢
  rcases hb with ⟨x, hx, h1, h2, h3, h4⟩ | ⟨x, hx, h1, h2, u, hu, h3⟩ |
    ⟨x₁, hx₁, x₂, hx₂, h1, h2, h3, h4, h5, h6, h7, h8⟩
  · refine Or.inl ⟨x, hx, ?_, h2, ?_, ?_⟩
    · rwa [← h x ⟨hx.1, by linarith⟩]
    · rwa [← segClosed_congr h htk hx.1 h2]
    · rwa [← segRelaxed_congr hβ h hx.1 h2]
  · have hu1 : x + u ≤ t := by
      have := hu.2.trans (min_le_right _ _); linarith
    refine Or.inr (Or.inl ⟨x, hx, h1, ?_, u, hu, ?_⟩)
    · rwa [← h x ⟨hx.1, h1⟩]
    · rwa [← h x ⟨hx.1, h1⟩, ← h (x + u) ⟨by linarith [hx.1, hu.1], hu1⟩]
  · refine Or.inr (Or.inr ⟨x₁, hx₁, x₂, hx₂, ?_, ?_, h3, h4, ?_, ?_, ?_, ?_⟩)
    · rwa [← h x₁ ⟨hx₁.1, by linarith⟩]
    · rwa [← h x₂ ⟨hx₂.1, by linarith⟩]
    · rwa [← segMerge_congr h hx₁.1 hx₂.1 h3 h4]
    · rwa [← segClosed_congr h htk hx₁.1 h3]
    · rwa [← segClosed_congr h htk hx₂.1 h4]
    · rwa [← proxSet_congr h hx₁.1 hx₂.1 h3 h4]

/-- Properties of discovered bad blocks (a), last sentence: badness by time `t` depends only on
`w|[0,t]`. -/
theorem badByTime_congr (hβ : 0 < β) (htk : 0 ≤ heavyTkPrime d t₀ n)
    (h : ∀ s ∈ Icc 0 t, w s = w' s) :
    BadByTime d β t₀ n w ι t ↔ BadByTime d β t₀ n w' ι t :=
  ⟨badByTime_congr_aux hβ htk h, badByTime_congr_aux hβ htk fun s hs => (h s hs).symm⟩

theorem badCount_congr (hβ : 0 < β) (htk : 0 ≤ heavyTkPrime d t₀ n)
    (h : ∀ s ∈ Icc 0 t, w s = w' s) :
    badCount d β t₀ n w t = badCount d β t₀ n w' t := by
  unfold badCount
  congr 2
  ext ι
  exact badByTime_congr hβ htk h

end ElboimSly.Paper

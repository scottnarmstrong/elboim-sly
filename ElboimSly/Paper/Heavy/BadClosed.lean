/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Paper.Heavy.BadFinite

/-!
# Badness is right-stable

Properties of discovered bad blocks (a).

For a cyclic path `w` and `s ≥ 0`: if `B` is not bad by time `s` then it is not bad by time
`s + η` for all small `η > 0` (`badByTime_eventually_not`).  Consequently the set of bad blocks is
locally constant from the right (`badSet_eventually_eq`).
-/

@[expose] public section

open Set Filter Topology MeasureTheory
open scoped ENNReal

namespace ElboimSly.Paper

open ElboimSly

variable {d : ℕ} {β t₀ : ℝ} {n : ℕ} {w : ℝ → Fin d → ℤ} {ι : Fin d → ℤ}

/-- Condition (V1) of `BadByTime`. -/
def BadV1 (d : ℕ) (β t₀ : ℝ) (n : ℕ) (w : ℝ → Fin d → ℤ) (ι : Fin d → ℤ) (t : ℝ) : Prop :=
  ∃ x ∈ cycIntTimes β, w x ∈ latNbhd (heavyBlock (heavyLevel d n) ι) (2 ^ (heavyLevel d n + 2)) ∧
    x + heavyTkPrime d t₀ n ≤ t ∧ ¬ SegClosed β (heavyTkPrime d t₀ n) w x ∧
      ¬ SegRelaxed β (heavyTkPrime d t₀ n) w (heavyLevelPrime d t₀ n) x

/-- Condition (V2) of `BadByTime`. -/
def BadV2 (d : ℕ) (β t₀ : ℝ) (n : ℕ) (w : ℝ → Fin d → ℤ) (ι : Fin d → ℤ) (t : ℝ) : Prop :=
  ∃ x ∈ cycIntTimes β, x ≤ t ∧
    w x ∈ latNbhd (heavyBlock (heavyLevel d n) ι) (2 ^ (heavyLevel d n + 2)) ∧
      ∃ u ∈ Icc (0 : ℝ) (min (heavyTkPrime d t₀ n) (t - x)),
        (2 : ℝ) ^ (heavyLevel d n - 1) < ‖w (x + u) - w x‖

/-- Condition (V3) of `BadByTime`. -/
def BadV3 (d : ℕ) (β t₀ : ℝ) (n : ℕ) (w : ℝ → Fin d → ℤ) (ι : Fin d → ℤ) (t : ℝ) : Prop :=
  ∃ x₁ ∈ cycIntTimes β, ∃ x₂ ∈ cycIntTimes β,
    w x₁ ∈ latNbhd (heavyBlock (heavyLevel d n) ι) (2 ^ (heavyLevel d n + 2)) ∧
    w x₂ ∈ latNbhd (heavyBlock (heavyLevel d n) ι) (2 ^ (heavyLevel d n + 2)) ∧
    x₁ + heavyTkPrime d t₀ n ≤ t ∧ x₂ + heavyTkPrime d t₀ n ≤ t ∧
      ¬ SegMerge β (heavyTkPrime d t₀ n) w x₁ x₂ ∧ ¬ SegClosed β (heavyTkPrime d t₀ n) w x₁ ∧
      ¬ SegClosed β (heavyTkPrime d t₀ n) w x₂ ∧
      ENNReal.ofReal ((3.9 : ℝ) ^ heavyLevel d n) ≤
        volume (proxSet (heavyTkPrime d t₀ n) w ((1.9 : ℝ) ^ heavyLevel d n) x₁ x₂)

theorem badByTime_iff (t : ℝ) : BadByTime d β t₀ n w ι t ↔
    BadV1 d β t₀ n w ι t ∨ BadV2 d β t₀ n w ι t ∨ BadV3 d β t₀ n w ι t := Iff.rfl

/-- A finite family of strict lower bounds survives a small positive shift. -/
theorem eventually_lt_of_finite {α : Type*} {F : Set α} (hF : F.Finite) (f : α → ℝ)
    (P : α → Prop) (s : ℝ) (h : ∀ a ∈ F, P a → s < f a) :
    ∀ᶠ η in 𝓝[>] (0 : ℝ), ∀ a ∈ F, P a → s + η < f a := by
  refine (Filter.eventually_all_finite hF).2 fun a ha => ?_
  by_cases hP : P a
  · have hpos : 0 < f a - s := by linarith [h a ha hP]
    filter_upwards [Ioo_mem_nhdsGT hpos] with η hη _ using by linarith [hη.2]
  · exact Eventually.of_forall fun η h' => absurd h' hP

variable (hw : IsCyclicPath w) (hβ : 0 < β) (htk : 0 ≤ heavyTkPrime d t₀ n)

include hβ htk in
theorem badV1_eventually_not {s : ℝ} (_hs : 0 ≤ s) (h : ¬ BadV1 d β t₀ n w ι s) :
    ∀ᶠ η in 𝓝[>] (0 : ℝ), ¬ BadV1 d β t₀ n w ι (s + η) := by
  have hX : (cycIntTimes β ∩ Icc 0 (s + 1)).Finite := cycIntTimes_inter_Icc_finite hβ _
  have key := eventually_lt_of_finite hX (fun x => x + heavyTkPrime d t₀ n)
    (fun x => w x ∈ latNbhd (heavyBlock (heavyLevel d n) ι) (2 ^ (heavyLevel d n + 2)) ∧
      ¬ SegClosed β (heavyTkPrime d t₀ n) w x ∧
      ¬ SegRelaxed β (heavyTkPrime d t₀ n) w (heavyLevelPrime d t₀ n) x) s (by
    rintro x ⟨hx, -⟩ ⟨h1, h2, h3⟩
    by_contra hcon
    exact h ⟨x, hx, h1, not_lt.1 hcon, h2, h3⟩)
  filter_upwards [key, Ioo_mem_nhdsGT (zero_lt_one : (0 : ℝ) < 1)] with η hη hη1
  rintro ⟨x, hx, h1, h2, h3, h4⟩
  have hxX : x ∈ cycIntTimes β ∩ Icc 0 (s + 1) := ⟨hx, hx.1, by linarith [hη1.2]⟩
  linarith [hη x hxX ⟨h1, h3, h4⟩]

include hβ htk in
theorem badV3_eventually_not {s : ℝ} (_hs : 0 ≤ s) (h : ¬ BadV3 d β t₀ n w ι s) :
    ∀ᶠ η in 𝓝[>] (0 : ℝ), ¬ BadV3 d β t₀ n w ι (s + η) := by
  have hX : (cycIntTimes β ∩ Icc 0 (s + 1)).Finite := cycIntTimes_inter_Icc_finite hβ _
  have key := eventually_lt_of_finite (hX.prod hX) (fun p => max p.1 p.2 + heavyTkPrime d t₀ n)
    (fun p => w p.1 ∈ latNbhd (heavyBlock (heavyLevel d n) ι) (2 ^ (heavyLevel d n + 2)) ∧
      w p.2 ∈ latNbhd (heavyBlock (heavyLevel d n) ι) (2 ^ (heavyLevel d n + 2)) ∧
      ¬ SegMerge β (heavyTkPrime d t₀ n) w p.1 p.2 ∧ ¬ SegClosed β (heavyTkPrime d t₀ n) w p.1 ∧
      ¬ SegClosed β (heavyTkPrime d t₀ n) w p.2 ∧
      ENNReal.ofReal ((3.9 : ℝ) ^ heavyLevel d n) ≤
        volume (proxSet (heavyTkPrime d t₀ n) w ((1.9 : ℝ) ^ heavyLevel d n) p.1 p.2)) s (by
    rintro ⟨x₁, x₂⟩ ⟨hx₁, hx₂⟩ ⟨h1, h2, h3, h4, h5, h6⟩
    by_contra hcon
    have hc : max x₁ x₂ + heavyTkPrime d t₀ n ≤ s := not_lt.1 hcon
    exact h ⟨x₁, hx₁.1, x₂, hx₂.1, h1, h2, by linarith [le_max_left x₁ x₂],
      by linarith [le_max_right x₁ x₂], h3, h4, h5, h6⟩)
  filter_upwards [key, Ioo_mem_nhdsGT (zero_lt_one : (0 : ℝ) < 1)] with η hη hη1
  rintro ⟨x₁, hx₁, x₂, hx₂, h1, h2, h3, h4, h5, h6, h7, h8⟩
  have hm : max x₁ x₂ ≤ s + η - heavyTkPrime d t₀ n := max_le (by linarith) (by linarith)
  have hxX₁ : x₁ ∈ cycIntTimes β ∩ Icc 0 (s + 1) := ⟨hx₁, hx₁.1, by linarith [hη1.2]⟩
  have hxX₂ : x₂ ∈ cycIntTimes β ∩ Icc 0 (s + 1) := ⟨hx₂, hx₂.1, by linarith [hη1.2]⟩
  have := hη (x₁, x₂) ⟨hxX₁, hxX₂⟩ ⟨h1, h2, h5, h6, h7, h8⟩
  simp only at this
  linarith

include hw hβ in
theorem badV2_eventually_not {s : ℝ} (hs : 0 ≤ s) (h : ¬ BadV2 d β t₀ n w ι s) :
    ∀ᶠ η in 𝓝[>] (0 : ℝ), ¬ BadV2 d β t₀ n w ι (s + η) := by
  have hX : (cycIntTimes β ∩ Icc 0 (s + 1)).Finite := cycIntTimes_inter_Icc_finite hβ _
  obtain ⟨η0, hη0, hrc⟩ := mem_nhdsGE_iff_exists_Ico_subset.1 (hw.rc s hs)
  have hH : ∀ x ∈ cycIntTimes β, x ≤ s →
      w x ∈ latNbhd (heavyBlock (heavyLevel d n) ι) (2 ^ (heavyLevel d n + 2)) →
      ∀ u ∈ Icc (0 : ℝ) (min (heavyTkPrime d t₀ n) (s - x)),
        ‖w (x + u) - w x‖ ≤ (2 : ℝ) ^ (heavyLevel d n - 1) := by
    intro x hx hxs hN u hu
    by_contra hcon
    exact h ⟨x, hx, hxs, hN, u, hu, not_le.1 hcon⟩
  have hgap := eventually_lt_of_finite hX (fun x => x) (fun x => s < x) s (fun x _ h => h)
  have hall : ∀ᶠ η in 𝓝[>] (0 : ℝ), η < η0 - s ∧ η < 1 ∧ ∀ x ∈ cycIntTimes β ∩ Icc 0 (s + 1),
      s < x → s + η < x := by
    filter_upwards [Ioo_mem_nhdsGT (sub_pos.2 (show s < η0 from hη0)), Ioo_mem_nhdsGT (zero_lt_one : (0 : ℝ) < 1), hgap]
      with η h1 h2 h3
    exact ⟨h1.2, h2.2, h3⟩
  filter_upwards [hall] with η ⟨hη0', hη1, hgapη⟩
  rintro ⟨x, hx, hxt, hN, u, hu, hviol⟩
  have hxX : x ∈ cycIntTimes β ∩ Icc 0 (s + 1) := ⟨hx, hx.1, by linarith⟩
  have hu1 : u ≤ s + η - x := hu.2.trans (min_le_right _ _)
  have hutk : u ≤ heavyTkPrime d t₀ n := hu.2.trans (min_le_left _ _)
  by_cases hxs : x ≤ s
  · by_cases hus : u ≤ s - x
    · exact absurd (hH x hx hxs hN u ⟨hu.1, le_min hutk hus⟩) (not_le.2 hviol)
    · push Not at hus
      have hy : w (x + u) = w s := hrc ⟨by linarith, by linarith⟩
      have h2 := hH x hx hxs hN (s - x) ⟨by linarith, le_min (by linarith) le_rfl⟩
      rw [hy] at hviol
      simp only [add_sub_cancel] at h2
      exact absurd h2 (not_le.2 hviol)
  · push Not at hxs
    have := hgapη x hxX hxs
    linarith [hu.1]

include hw hβ htk in
theorem badByTime_eventually_not {s : ℝ} (hs : 0 ≤ s) (h : ¬ BadByTime d β t₀ n w ι s) :
    ∀ᶠ η in 𝓝[>] (0 : ℝ), ¬ BadByTime d β t₀ n w ι (s + η) := by
  rw [badByTime_iff, not_or, not_or] at h
  filter_upwards [badV1_eventually_not hβ htk hs h.1, badV2_eventually_not hw hβ hs h.2.1,
    badV3_eventually_not hβ htk hs h.2.2] with η h1 h2 h3
  rw [badByTime_iff, not_or, not_or]
  exact ⟨h1, h2, h3⟩

end ElboimSly.Paper

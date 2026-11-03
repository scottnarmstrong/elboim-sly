/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Paper.Heavy.BadMeasAux
public import ElboimSly.Paper.Heavy.BadClosed

/-!
# Measurability of badness: conditions (V1) and (V2)

Properties of discovered bad blocks (c), (d).  For an adapted family of cyclic paths, the events
`BadV1` and `BadV2` at time `t` are `ℱ_t`-measurable.
-/

@[expose] public section

open MeasureTheory Set Filter Topology
open scoped ENNReal NNReal

namespace ElboimSly.Paper

open ElboimSly

variable {d : ℕ} {Ω : Type*} {m : MeasurableSpace Ω} {f : Filtration ℝ≥0 m}
  {W : Ω → ℝ → Fin d → ℤ} {β t₀ : ℝ} {n : ℕ} {ι : Fin d → ℤ}

theorem AdaptedCyclic.measurableSet_norm_lt (h : AdaptedCyclic f W) {s₁ s₂ : ℝ} (h1 : 0 ≤ s₁)
    (h2 : 0 ≤ s₂) {t : ℝ≥0} (h1t : s₁ ≤ t) (h2t : s₂ ≤ t) (c : ℝ) :
    MeasurableSet[f t] {ω | c < ‖W ω s₁ - W ω s₂‖} := by
  have := ((h.measurable_at h1 h1t).prodMk (h.measurable_at h2 h2t))
    (Set.to_countable {p : (Fin d → ℤ) × (Fin d → ℤ) | c < ‖p.1 - p.2‖}).measurableSet
  exact this

theorem AdaptedCyclic.measurableSet_badV1 (h : AdaptedCyclic f W) (hβ : 0 < β)
    (htk : 0 ≤ heavyTkPrime d t₀ n) (t : ℝ≥0) :
    MeasurableSet[f t] {ω | BadV1 d β t₀ n (W ω) ι t} := by
  have hset : {ω | BadV1 d β t₀ n (W ω) ι t} =
      ⋃ x ∈ cycIntTimes β ∩ Icc 0 (t : ℝ), ⋃ _ : x + heavyTkPrime d t₀ n ≤ t,
        (({ω | W ω x ∈ latNbhd (heavyBlock (heavyLevel d n) ι) (2 ^ (heavyLevel d n + 2))} ∩
          {ω | SegClosed β (heavyTkPrime d t₀ n) (W ω) x}ᶜ) ∩
          {ω | SegRelaxed β (heavyTkPrime d t₀ n) (W ω) (heavyLevelPrime d t₀ n) x}ᶜ) := by
    ext ω
    simp only [BadV1, mem_ofPred_eq, mem_iUnion, mem_inter_iff, mem_compl_iff, exists_prop]
    constructor
    · rintro ⟨x, hx, h1, h2, h3, h4⟩
      exact ⟨x, ⟨hx, hx.1, by linarith⟩, h2, ⟨h1, h3⟩, h4⟩
    · rintro ⟨x, ⟨hx, -⟩, h2, ⟨h1, h3⟩, h4⟩
      exact ⟨x, hx, h1, h2, h3, h4⟩
  rw [hset]
  refine MeasurableSet.biUnion (cycIntTimes_inter_Icc_finite hβ _).countable fun x hx => ?_
  refine MeasurableSet.iUnion fun hxt => ?_
  refine ((h.measurableSet_mem hx.1.1 (by linarith) _).inter
    (h.measurableSet_segClosed hβ htk hx.1.1 hxt).compl).inter
    (h.measurableSet_segRelaxed hβ htk hx.1.1 hxt).compl

theorem AdaptedCyclic.measurableSet_badV2 (h : AdaptedCyclic f W) (hβ : 0 < β)
    (htk : 0 ≤ heavyTkPrime d t₀ n) (t : ℝ≥0) :
    MeasurableSet[f t] {ω | BadV2 d β t₀ n (W ω) ι t} := by
  set r : ℝ := (2 : ℝ) ^ (heavyLevel d n - 1) with hr
  set tk := heavyTkPrime d t₀ n with htkdef
  have hset : {ω | BadV2 d β t₀ n (W ω) ι t} =
      ⋃ x ∈ cycIntTimes β ∩ Icc 0 (t : ℝ),
        ({ω | W ω x ∈ latNbhd (heavyBlock (heavyLevel d n) ι) (2 ^ (heavyLevel d n + 2))} ∩
          ({ω | r < ‖W ω (x + min tk (t - x)) - W ω x‖} ∪
            ⋃ q : {q : ℚ // 0 < (q : ℝ) ∧ (q : ℝ) < min tk (t - x)},
              {ω | r < ‖W ω (x + q) - W ω x‖})) := by
    ext ω
    simp only [BadV2, mem_ofPred_eq, mem_iUnion, mem_inter_iff, mem_union, exists_prop]
    constructor
    · rintro ⟨x, hx, hxt, hN, hu⟩
      refine ⟨x, ⟨hx, hx.1, hxt⟩, hN, ?_⟩
      have hU : 0 ≤ min tk (t - x) := le_min htk (by linarith)
      have hrc : ∀ u ∈ Icc (0 : ℝ) (min tk (t - x)), ∃ η > 0, ∀ u' ∈ Ico u (u + η),
          (r < ‖W ω (x + u') - W ω x‖ ↔ r < ‖W ω (x + u) - W ω x‖) := by
        intro u hu'
        obtain ⟨η, hη, hη'⟩ := (h.path ω).exists_plateau (show 0 ≤ x + u by linarith [hx.1, hu'.1])
        refine ⟨η, hη, fun u' hu'' => ?_⟩
        rw [hη' (x + u') ⟨by linarith [hu''.1], by linarith [hu''.2]⟩]
      have := (exists_Icc_iff_rat hU hrc).1 hu
      rcases this with h1 | ⟨q, hq1, hq2, hq⟩
      · exact Or.inl h1
      · exact Or.inr ⟨⟨q, hq1, hq2⟩, hq⟩
    · rintro ⟨x, ⟨hx, -, hxt⟩, hN, hu⟩
      refine ⟨x, hx, hxt, hN, ?_⟩
      have hU : 0 ≤ min tk (t - x) := le_min htk (by linarith)
      rcases hu with h1 | ⟨q, hq⟩
      · exact ⟨min tk (t - x), ⟨hU, le_rfl⟩, h1⟩
      · exact ⟨q, ⟨q.2.1.le, q.2.2.le⟩, hq⟩
  rw [hset]
  refine MeasurableSet.biUnion (cycIntTimes_inter_Icc_finite hβ _).countable fun x hx => ?_
  have hxt : x ≤ t := hx.2.2
  have hU : min tk (t - x) ≤ t - x := min_le_right _ _
  refine (h.measurableSet_mem hx.1.1 hxt _).inter ?_
  refine (h.measurableSet_norm_lt (by linarith [hx.1.1, le_min htk (by linarith : 0 ≤ t - x)])
    hx.1.1 (by linarith) hxt r).union (MeasurableSet.iUnion fun q => ?_)
  exact h.measurableSet_norm_lt (by linarith [hx.1.1, q.2.1]) hx.1.1
    (by linarith [q.2.2, hU]) hxt r

end ElboimSly.Paper

/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Paper.Heavy.BadMeasV3b

/-!
# Measurability of badness: the proximity volume and condition (V3)

Properties of discovered bad blocks (c), (d).

* `AdaptedCyclic.measurable_proxVol`: `ω ↦ |𝔓(x₁, x₂)|` is `ℱ_t`-measurable (Tonelli, through the
  clipped path, which is jointly measurable).
* `AdaptedCyclic.measurableSet_badV3`.
-/

@[expose] public section

open MeasureTheory Set Filter Topology
open scoped ENNReal NNReal

namespace ElboimSly.Paper

open ElboimSly

variable {d : ℕ} {Ω : Type*} {m : MeasurableSpace Ω} {f : Filtration ℝ≥0 m}
  {W : Ω → ℝ → Fin d → ℤ} {β t₀ : ℝ} {n : ℕ} {ι : Fin d → ℤ}

theorem AdaptedCyclic.measurable_proxVol (h : AdaptedCyclic f W) {tk ρ x₁ x₂ : ℝ} {t : ℝ≥0}
    (htk : 0 ≤ tk) (hx₁ : 0 ≤ x₁) (hx₂ : 0 ≤ x₂) (h1t : x₁ + tk ≤ t) (h2t : x₂ + tk ≤ t) :
    Measurable[f t] (fun ω => volume (proxSet tk (W ω) ρ x₁ x₂)) := by
  let : MeasurableSpace Ω := f t
  have hjoint := h.measurable_clipPath t
  have hle : ∀ a : ℝ, 0 ≤ a → a ≤ t →
      MeasurableSet {p : Ω × ℝ | ‖W p.1 a - clipPath W t p.1 (x₂ + p.2)‖ ≤ ρ} := by
    intro a ha hat
    have h1 : Measurable (fun p : Ω × ℝ => W p.1 a) := (h.measurable_at ha hat).comp measurable_fst
    have h2 : Measurable (fun p : Ω × ℝ => clipPath W t p.1 (x₂ + p.2)) :=
      hjoint.comp (measurable_fst.prodMk (measurable_const.add measurable_snd))
    exact (h1.prodMk h2) (Set.to_countable
      {q : (Fin d → ℤ) × (Fin d → ℤ) | ‖q.1 - q.2‖ ≤ ρ}).measurableSet
  obtain ⟨S, hS⟩ : ∃ S : Set (Ω × ℝ), S = {p | p.2 ∈ Icc 0 tk ∧
      (‖W p.1 (x₁ + tk) - clipPath W t p.1 (x₂ + p.2)‖ ≤ ρ ∨
        ∃ q : {q : ℚ // 0 < (q : ℝ) ∧ (q : ℝ) < tk},
          ‖W p.1 (x₁ + q) - clipPath W t p.1 (x₂ + p.2)‖ ≤ ρ)} := ⟨_, rfl⟩
  have hSm : MeasurableSet S := by
    rw [hS]
    have h0 : MeasurableSet {p : Ω × ℝ | p.2 ∈ Icc (0 : ℝ) tk} := measurable_snd measurableSet_Icc
    have h1 := hle (x₁ + tk) (by linarith) h1t
    have h3 : MeasurableSet {p : Ω × ℝ | ∃ q : {q : ℚ // 0 < (q : ℝ) ∧ (q : ℝ) < tk},
        ‖W p.1 (x₁ + q) - clipPath W t p.1 (x₂ + p.2)‖ ≤ ρ} := by
      have : {p : Ω × ℝ | ∃ q : {q : ℚ // 0 < (q : ℝ) ∧ (q : ℝ) < tk},
          ‖W p.1 (x₁ + q) - clipPath W t p.1 (x₂ + p.2)‖ ≤ ρ} =
          ⋃ q : {q : ℚ // 0 < (q : ℝ) ∧ (q : ℝ) < tk},
            {p : Ω × ℝ | ‖W p.1 (x₁ + q) - clipPath W t p.1 (x₂ + p.2)‖ ≤ ρ} := by
        ext p; simp
      rw [this]
      exact MeasurableSet.iUnion fun q => hle _ (by linarith [q.2.1]) (by linarith [q.2.2])
    exact h0.inter (h1.union h3)
  have hvol := measurable_measure_prodMk_left (ν := (volume : Measure ℝ)) hSm
  have hfun : (fun ω => volume (proxSet tk (W ω) ρ x₁ x₂)) = fun ω => volume (Prod.mk ω ⁻¹' S) := by
    funext ω
    congr 1
    rw [proxSet_eq_rat (h.path ω) htk hx₁ hx₂]
    ext u
    simp only [mem_ofPred_eq, mem_preimage, hS]
    refine and_congr_right fun hu => ?_
    have hc : clipPath W t ω (x₂ + u) = W ω (x₂ + u) :=
      clipPath_eq t ω (by linarith [hu.1]) (by linarith [hu.2])
    rw [hc]
    constructor
    · rintro (h1 | ⟨q, h2, h3, h4⟩)
      · exact Or.inl h1
      · exact Or.inr ⟨⟨q, h2, h3⟩, h4⟩
    · rintro (h1 | ⟨q, h4⟩)
      · exact Or.inl h1
      · exact Or.inr ⟨q.1, q.2.1, q.2.2, h4⟩
  rw [hfun]
  exact hvol

theorem AdaptedCyclic.measurableSet_badV3 (h : AdaptedCyclic f W) (hβ : 0 < β)
    (htk : 0 ≤ heavyTkPrime d t₀ n) (t : ℝ≥0) :
    MeasurableSet[f t] {ω | BadV3 d β t₀ n (W ω) ι t} := by
  set tk := heavyTkPrime d t₀ n with htkdef
  set k := heavyLevel d n
  have hset : {ω | BadV3 d β t₀ n (W ω) ι t} =
      ⋃ x₁ ∈ cycIntTimes β ∩ Icc 0 (t : ℝ), ⋃ x₂ ∈ cycIntTimes β ∩ Icc 0 (t : ℝ),
        ⋃ _ : x₁ + tk ≤ t ∧ x₂ + tk ≤ t,
        ((({ω | W ω x₁ ∈ latNbhd (heavyBlock k ι) (2 ^ (k + 2))} ∩
          {ω | W ω x₂ ∈ latNbhd (heavyBlock k ι) (2 ^ (k + 2))}) ∩
          ({ω | SegMerge β tk (W ω) x₁ x₂}ᶜ ∩ {ω | SegClosed β tk (W ω) x₁}ᶜ)) ∩
          ({ω | SegClosed β tk (W ω) x₂}ᶜ ∩
            {ω | ENNReal.ofReal ((3.9 : ℝ) ^ k) ≤
              volume (proxSet tk (W ω) ((1.9 : ℝ) ^ k) x₁ x₂)})) := by
    ext ω
    simp only [BadV3, mem_ofPred_eq, mem_iUnion, mem_inter_iff, mem_compl_iff, exists_prop]
    constructor
    · rintro ⟨x₁, hx₁, x₂, hx₂, h1, h2, h3, h4, h5, h6, h7, h8⟩
      exact ⟨x₁, ⟨hx₁, hx₁.1, by linarith⟩, x₂, ⟨hx₂, hx₂.1, by linarith⟩, ⟨h3, h4⟩,
        ⟨⟨h1, h2⟩, h5, h6⟩, h7, h8⟩
    · rintro ⟨x₁, ⟨hx₁, -⟩, x₂, ⟨hx₂, -⟩, ⟨h3, h4⟩, ⟨⟨h1, h2⟩, h5, h6⟩, h7, h8⟩
      exact ⟨x₁, hx₁, x₂, hx₂, h1, h2, h3, h4, h5, h6, h7, h8⟩
  rw [hset]
  have hX := cycIntTimes_inter_Icc_finite hβ (t : ℝ)
  refine MeasurableSet.biUnion hX.countable fun x₁ hx₁ => ?_
  refine MeasurableSet.biUnion hX.countable fun x₂ hx₂ => ?_
  refine MeasurableSet.iUnion fun ht => ?_
  refine (((h.measurableSet_mem hx₁.1.1 (by linarith [ht.1]) _).inter
    (h.measurableSet_mem hx₂.1.1 (by linarith [ht.2]) _)).inter
    ((h.measurableSet_segMerge htk hx₁.1.1 hx₂.1.1 ht.1 ht.2).compl.inter
      (h.measurableSet_segClosed hβ htk hx₁.1.1 ht.1).compl)).inter
    ((h.measurableSet_segClosed hβ htk hx₂.1.1 ht.2).compl.inter ?_)
  exact measurableSet_le measurable_const (h.measurable_proxVol htk hx₁.1.1 hx₂.1.1 ht.1 ht.2)

end ElboimSly.Paper

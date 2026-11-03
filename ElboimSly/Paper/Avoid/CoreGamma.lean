/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Paper.Avoid.CoreHit
public import ElboimSly.Paper.Avoid.ProcessLaw
public import Mathlib

/-!
# ES22 §4, Lemma 4.1 (core form): the good event as a measurable set of (history, path)

ES22 Lemma 4.1, "Measurable structure" and "Two events". The history is recorded as
`u = (h, ℓ, x₀)`: the path `h(s) = w((a + s) ∧ T)` of the history from its start, its length
`ℓ = T - a` and its endpoint `x₀ = w(T)`. The good event `E₁ ∩ E₂` is written with countably many
test times (`qSet`), so it is a measurable subset of (history) × (path space); for right-continuous
paths it implies the real-time conditions of `no_hit`.
-/

@[expose] public section

open MeasureTheory Set
open scoped ENNReal NNReal

namespace ElboimSly.Paper

variable {d : ℕ}

/-- The recorded history: its path from the start, its length and its endpoint. -/
abbrev HistE (d : ℕ) : Type := (ℝ≥0 → Fin d → ℤ) × ℝ≥0 × (Fin d → ℤ)

/-- The countable-time visited set `{x₀} ∪ {h(s) : s ≤ ℓ rational}`. -/
def histVisited (u : HistE d) : Set (Fin d → ℤ) :=
  {u.2.2} ∪ {v | ∃ s : ℝ≥0, (∃ r : ℚ, (s : ℝ) = r) ∧ s ≤ u.2.1 ∧ u.1 s = v}

/-- The good event `E₁ ∩ E₂` with countably many test times:
(E₁) `y(q) ∉ A_u` for `q` a test time in `[0, 4ⁿ]`, (E₂) `‖y(q)‖ ≥ b₁` for `q` a test time in
`[b₃, 4ⁿ]`. -/
def cylGamma (d : ℕ) (L1 b1 : ℝ) (b3 b4 : ℝ≥0) : Set (HistE d × (ℝ≥0 → Fin d → ℤ)) :=
  {p | (∀ q ∈ qSet 0 b4, ¬ (L1 ≤ ‖p.2 q‖ ∧ ∃ v ∈ histVisited p.1, ‖p.2 q + p.1.2.2 - v‖ ≤ 1)) ∧
    (∀ q ∈ qSet b3 b4, b1 ≤ ‖p.2 q‖)}

theorem ratSet_countable : {s : ℝ≥0 | ∃ r : ℚ, (s : ℝ) = r}.Countable := by
  refine (Set.countable_range (fun r : ℚ => Real.toNNReal r)).mono ?_
  rintro q ⟨r, hr⟩
  exact ⟨r, by rw [← NNReal.coe_inj, Real.coe_toNNReal _ (by rw [← hr]; exact q.2), hr]⟩

theorem measurableSet_cylGamma (L1 b1 : ℝ) (b3 b4 : ℝ≥0) :
    MeasurableSet (cylGamma d L1 b1 b3 b4) := by
  have hnorm : ∀ (c : ℝ) (g : HistE d × (ℝ≥0 → Fin d → ℤ) → Fin d → ℤ), Measurable g →
      MeasurableSet {p | ‖g p‖ ≤ c} := fun c g hg =>
    hg (Set.to_countable {z : Fin d → ℤ | ‖z‖ ≤ c}).measurableSet
  have hnorm' : ∀ (c : ℝ) (g : HistE d × (ℝ≥0 → Fin d → ℤ) → Fin d → ℤ), Measurable g →
      MeasurableSet {p | c ≤ ‖g p‖} := fun c g hg =>
    hg (Set.to_countable {z : Fin d → ℤ | c ≤ ‖z‖}).measurableSet
  have hy : ∀ q : ℝ≥0, Measurable fun p : HistE d × (ℝ≥0 → Fin d → ℤ) => p.2 q :=
    fun q => (measurable_pi_apply q).comp measurable_snd
  have hx : Measurable fun p : HistE d × (ℝ≥0 → Fin d → ℤ) => p.1.2.2 :=
    measurable_snd.comp (measurable_snd.comp measurable_fst)
  have hh : ∀ s : ℝ≥0, Measurable fun p : HistE d × (ℝ≥0 → Fin d → ℤ) => p.1.1 s :=
    fun s => (measurable_pi_apply s).comp (measurable_fst.comp measurable_fst)
  have hl : Measurable fun p : HistE d × (ℝ≥0 → Fin d → ℤ) => p.1.2.1 :=
    measurable_fst.comp (measurable_snd.comp measurable_fst)
  unfold cylGamma
  rw [ofPred_and]
  refine MeasurableSet.inter ?_ ?_
  · -- E₁
    have : {p : HistE d × (ℝ≥0 → Fin d → ℤ) | ∀ q ∈ qSet 0 b4,
        ¬ (L1 ≤ ‖p.2 q‖ ∧ ∃ v ∈ histVisited p.1, ‖p.2 q + p.1.2.2 - v‖ ≤ 1)} =
        ⋂ q ∈ qSet 0 b4, ({p | L1 ≤ ‖p.2 q‖ ∧ ∃ v ∈ histVisited p.1,
          ‖p.2 q + p.1.2.2 - v‖ ≤ 1})ᶜ := by
      ext p; simp
    rw [this]
    refine MeasurableSet.biInter (qSet_countable 0 b4) fun q _ => MeasurableSet.compl ?_
    have e : {p : HistE d × (ℝ≥0 → Fin d → ℤ) | L1 ≤ ‖p.2 q‖ ∧ ∃ v ∈ histVisited p.1,
        ‖p.2 q + p.1.2.2 - v‖ ≤ 1} = {p | L1 ≤ ‖p.2 q‖} ∩
        ({p | ‖p.2 q + p.1.2.2 - p.1.2.2‖ ≤ 1} ∪
          ⋃ s ∈ {s : ℝ≥0 | ∃ r : ℚ, (s : ℝ) = r}, ({p | s ≤ p.1.2.1} ∩
            {p | ‖p.2 q + p.1.2.2 - p.1.1 s‖ ≤ 1})) := by
      ext p
      simp only [histVisited, mem_inter_iff, mem_ofPred_eq, mem_union, mem_singleton_iff,
        mem_iUnion, exists_prop]
      constructor
      · rintro ⟨h1, v, hv, h2⟩
        refine ⟨h1, ?_⟩
        rcases hv with rfl | ⟨s, hs, hsl, rfl⟩
        · exact Or.inl h2
        · exact Or.inr ⟨s, hs, hsl, h2⟩
      · rintro ⟨h1, h2 | ⟨s, hs, hsl, h2⟩⟩
        · exact ⟨h1, _, Or.inl rfl, h2⟩
        · exact ⟨h1, _, Or.inr ⟨s, hs, hsl, rfl⟩, h2⟩
    rw [e]
    refine MeasurableSet.inter (hnorm' L1 _ (hy q)) (MeasurableSet.union ?_ ?_)
    · exact hnorm 1 _ ((hy q).add hx |>.sub hx)
    · refine MeasurableSet.biUnion ratSet_countable fun s _ => MeasurableSet.inter ?_ ?_
      · exact measurableSet_le measurable_const hl
      · exact hnorm 1 _ (((hy q).add hx).sub (hh s))
  · -- E₂
    have : {p : HistE d × (ℝ≥0 → Fin d → ℤ) | ∀ q ∈ qSet b3 b4, b1 ≤ ‖p.2 q‖} =
        ⋂ q ∈ qSet b3 b4, {p | b1 ≤ ‖p.2 q‖} := by
      ext p; simp
    rw [this]
    exact MeasurableSet.biInter (qSet_countable b3 b4) fun q _ => hnorm' b1 _ (hy q)

end ElboimSly.Paper

end

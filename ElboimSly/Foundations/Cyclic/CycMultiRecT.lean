/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Foundations.Cyclic.CycMultiStopT
public import ElboimSly.Foundations.Cyclic.CycTruncRC
public import ElboimSly.Foundations.Cyclic.CycRecCoords
public import ElboimSly.Foundations.Cyclic.CPathStop
public import Mathlib

/-!
# Several walks explored one after another (a), Step 2 (I): measurability of a right-continuous process at `T`

Several walks explored one after another (a), Step 2, which refers to the argument of
Paths (c). We prove the abstract statement: if `s ↦ Z s` is adapted and right-continuous
(either eventually constant to the right, or `ℝ≥0∞`-valued and tending to its value), then
`ω ↦ Z (T ω) ω` is `ℱ_T`-measurable (`measurable_stoppedValue_of_bdd` plus the two bounded cores).
-/

@[expose] public section

open MeasureTheory Set Filter Topology
open scoped ENNReal NNReal

namespace ElboimSly.Cyclic

section core

variable {Ω Y : Type*} {𝒢 : MeasurableSpace Ω} [MeasurableSpace Y]

/-- The value of a process at the dyadic upper approximation of a random time, capped at `C`. -/
theorem measurable_grid (Z : ℝ≥0 → Ω → Y) (σ : Ω → ℝ≥0) (C : ℝ≥0) (hσ : Measurable[𝒢] σ)
    (hZ : ∀ t ≤ C, Measurable[𝒢] (Z t)) (m : ℕ) :
    Measurable[𝒢] fun ω => Z (min (dyUp m (σ ω)) C) ω := by
  let : MeasurableSpace Ω := 𝒢
  have h0 : Measurable fun ω => σ ω * 2 ^ m := hσ.mul_const _
  have h1 : Measurable fun ω => (⌈σ ω * 2 ^ m⌉₊, ω) :=
    (Nat.measurable_ceil.comp h0).prodMk measurable_id
  have h2 : Measurable fun q : ℕ × Ω => Z (min ((q.1 : ℝ≥0) / 2 ^ m) C) q.2 :=
    measurable_from_prod_countable_right fun k => hZ (min ((k : ℝ≥0) / 2 ^ m) C) (min_le_right _ _)
  have h3 := h2.comp h1
  exact h3

/-- Bounded core, eventually constant to the right. -/
theorem measurable_stopped_bdd_const (Z : ℝ≥0 → Ω → Y) (σ : Ω → ℝ≥0) (C : ℝ≥0)
    (hσ : Measurable[𝒢] σ) (hC : ∀ ω, σ ω ≤ C) (hZ : ∀ t ≤ C, Measurable[𝒢] (Z t))
    (hrc : ∀ ω s, ∃ ε : ℝ≥0, 0 < ε ∧ ∀ s', s ≤ s' → s' < s + ε → Z s' ω = Z s ω) :
    Measurable[𝒢] fun ω => Z (σ ω) ω := by
  let : MeasurableSpace Ω := 𝒢
  intro B hB
  have key : ∀ ω, ∀ᶠ m in atTop, Z (min (dyUp m (σ ω)) C) ω = Z (σ ω) ω := by
    intro ω
    obtain ⟨ε, hε, h⟩ := hrc ω (σ ω)
    have hε2 : 0 < ε / 2 := half_pos hε
    have hev := eventually_dyUp_le (σ ω) (σ ω + ε / 2) (lt_add_of_pos_right _ hε2)
    filter_upwards [hev] with m hm
    refine h _ (le_min (le_dyUp m _) (hC ω)) ?_
    calc min (dyUp m (σ ω)) C ≤ dyUp m (σ ω) := min_le_left _ _
      _ ≤ σ ω + ε / 2 := hm
      _ < σ ω + ε := add_lt_add_right (NNReal.half_lt_self hε.ne') _
  have : (fun ω => Z (σ ω) ω) ⁻¹' B = ⋃ M : ℕ, ⋂ m : ℕ, ⋂ (_ : M ≤ m),
      (fun ω => Z (min (dyUp m (σ ω)) C) ω) ⁻¹' B := by
    ext ω
    simp only [mem_preimage, mem_iUnion, mem_iInter]
    obtain ⟨M, hM⟩ := eventually_atTop.1 (key ω)
    constructor
    · intro h
      exact ⟨M, fun m hm => by rw [hM m hm]; exact h⟩
    · rintro ⟨M', hM'⟩
      have := hM' (max M M') (le_max_right _ _)
      rwa [hM _ (le_max_left _ _)] at this
  rw [this]
  exact MeasurableSet.iUnion fun M => MeasurableSet.iInter fun m => MeasurableSet.iInter fun _ =>
    measurable_grid Z σ C hσ hZ m hB

/-- Bounded core, `ℝ≥0∞`-valued and right-continuous. -/
theorem measurable_stopped_bdd_tendsto (Z : ℝ≥0 → Ω → ℝ≥0∞) (σ : Ω → ℝ≥0) (C : ℝ≥0)
    (hσ : Measurable[𝒢] σ) (hC : ∀ ω, σ ω ≤ C) (hZ : ∀ t ≤ C, Measurable[𝒢] (Z t))
    (hrc : ∀ ω s, Tendsto (fun s' => Z s' ω) (𝓝[≥] s) (𝓝 (Z s ω))) :
    Measurable[𝒢] fun ω => Z (σ ω) ω := by
  let : MeasurableSpace Ω := 𝒢
  refine measurable_of_tendsto_metrizable (fun m => measurable_grid Z σ C hσ hZ m)
    (tendsto_pi_nhds.2 fun ω => ?_)
  refine (hrc ω (σ ω)).comp ?_
  rw [tendsto_nhdsWithin_iff]
  refine ⟨?_, Eventually.of_forall fun m => mem_Ici.2 (le_min (le_dyUp m _) (hC ω))⟩
  have h0 : Tendsto (fun m : ℕ => ((1 / 2 : ℝ≥0)) ^ m) atTop (𝓝 0) :=
    NNReal.tendsto_pow_atTop_nhds_zero_of_lt_one (by
      rw [one_div]; exact inv_lt_one_of_one_lt₀ (by norm_num))
  have h1 : Tendsto (fun m : ℕ => σ ω + ((1 / 2 : ℝ≥0)) ^ m) atTop (𝓝 (σ ω)) := by
    simpa using tendsto_const_nhds.add h0
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds h1
    (fun m => le_min (le_dyUp m _) (hC ω))
    (fun m => (min_le_left _ _).trans (dyUp_lt m _).le)

end core

section glue

variable {Ω Y : Type*} [MeasurableSpace Y] {mΩ : MeasurableSpace Ω} {f : Filtration ℝ≥0 mΩ}
  {T : Ω → WithTop ℝ≥0}

/-- A process stopped at `T` is `ℱ_T`-measurable as soon as its stoppings at the bounded times
`T ∧ i` are `ℱ_i`-measurable. -/
theorem measurable_stoppedValue_of_bdd (Z : ℝ≥0 → Ω → Y) (hT : IsStoppingTime f T)
    (h : ∀ i : ℝ≥0, Measurable[f i] fun ω => Z (ElboimSly.SRW.stopMin T i ω) ω)
    (h0 : Measurable[f 0] (Z 0)) :
    Measurable[hT.measurableSpace] fun ω => Z (ElboimSly.SRW.stopReal T ω) ω := by
  intro B hB
  have hfin : ∀ (ω : Ω) (i : ℝ≥0), T ω ≤ (i : WithTop ℝ≥0) →
      ElboimSly.SRW.stopMin T i ω = ElboimSly.SRW.stopReal T ω := by
    intro ω i hi
    cases hh : T ω using WithTop.recTopCoe with
    | top => rw [hh] at hi; exact absurd (top_le_iff.mp hi) WithTop.coe_ne_top
    | coe a =>
      rw [hh] at hi
      have ha : a ≤ i := WithTop.coe_le_coe.1 hi
      have e1 : ElboimSly.SRW.stopReal T ω = a := by
        unfold ElboimSly.SRW.stopReal; rw [hh]; rfl
      have e2 : ElboimSly.SRW.stopMin T i ω = min a i := by
        unfold ElboimSly.SRW.stopMin; rw [hh]; rfl
      rw [e1, e2, min_eq_left ha]
  have hle : ∀ t, f t ≤ ⨆ t, f t := fun t => le_iSup f t
  have hU : ∀ n : ℕ, MeasurableSet[f n]
      ((fun ω => Z (ElboimSly.SRW.stopReal T ω) ω) ⁻¹' B ∩ {ω | T ω ≤ ((n : ℝ≥0) : WithTop ℝ≥0)}) := by
    intro n
    have : (fun ω => Z (ElboimSly.SRW.stopReal T ω) ω) ⁻¹' B ∩ {ω | T ω ≤ ((n : ℝ≥0) : WithTop ℝ≥0)} =
        (fun ω => Z (ElboimSly.SRW.stopMin T n ω) ω) ⁻¹' B ∩ {ω | T ω ≤ ((n : ℝ≥0) : WithTop ℝ≥0)} := by
      ext ω
      simp only [mem_inter_iff, mem_preimage, mem_ofPred_eq]
      constructor
      · rintro ⟨h1, h2⟩; exact ⟨by rwa [hfin ω n h2], h2⟩
      · rintro ⟨h1, h2⟩; exact ⟨by rwa [hfin ω n h2] at h1, h2⟩
    rw [this]
    exact (h n hB).inter (hT n)
  refine ⟨?_, fun i => ?_⟩
  · have hS : (fun ω => Z (ElboimSly.SRW.stopReal T ω) ω) ⁻¹' B =
        (⋃ n : ℕ, (fun ω => Z (ElboimSly.SRW.stopReal T ω) ω) ⁻¹' B ∩
          {ω | T ω ≤ ((n : ℝ≥0) : WithTop ℝ≥0)}) ∪
        (Z 0 ⁻¹' B ∩ (⋃ n : ℕ, {ω | T ω ≤ ((n : ℝ≥0) : WithTop ℝ≥0)})ᶜ) := by
      ext ω
      simp only [mem_preimage, mem_union, mem_iUnion, mem_inter_iff, mem_ofPred_eq, mem_compl_iff,
        not_exists]
      by_cases hex : ∃ n : ℕ, T ω ≤ ((n : ℝ≥0) : WithTop ℝ≥0)
      · obtain ⟨n, hn⟩ := hex
        constructor
        · intro hh; exact Or.inl ⟨n, hh, hn⟩
        · rintro (⟨n', hh, -⟩ | ⟨-, hh⟩)
          · exact hh
          · exact absurd hn (hh n)
      · push Not at hex
        have hTop : T ω = ⊤ := by
          by_contra hne
          obtain ⟨a, ha⟩ := WithTop.ne_top_iff_exists.1 hne
          obtain ⟨n, hn⟩ := exists_nat_ge a
          have := hex n
          rw [← ha] at this
          exact absurd (WithTop.coe_le_coe.2 hn) (not_le.2 this)
        have h0' : ElboimSly.SRW.stopReal T ω = 0 := by simp [ElboimSly.SRW.stopReal, hTop]
        constructor
        · intro hh; exact Or.inr ⟨by rwa [h0'] at hh, fun n => not_le.2 (hex n)⟩
        · rintro (⟨n, -, hn⟩ | ⟨hh, -⟩)
          · exact absurd hn (not_le.2 (hex n))
          · rwa [h0']
    rw [hS]
    refine MeasurableSet.union (MeasurableSet.iUnion fun n : ℕ => hle (n : ℝ≥0) _ (hU n)) ?_
    exact (hle 0 _ (h0 hB)).inter (MeasurableSet.iUnion fun n : ℕ => hle (n : ℝ≥0) _ (hT n)).compl
  · have : (fun ω => Z (ElboimSly.SRW.stopReal T ω) ω) ⁻¹' B ∩ {ω | T ω ≤ (i : WithTop ℝ≥0)} =
        (fun ω => Z (ElboimSly.SRW.stopMin T i ω) ω) ⁻¹' B ∩ {ω | T ω ≤ (i : WithTop ℝ≥0)} := by
      ext ω
      simp only [mem_inter_iff, mem_preimage, mem_ofPred_eq]
      constructor
      · rintro ⟨h1, h2⟩; exact ⟨by rwa [hfin ω i h2], h2⟩
      · rintro ⟨h1, h2⟩; exact ⟨by rwa [hfin ω i h2] at h1, h2⟩
    rw [this]
    exact (h i hB).inter (hT i)

end glue

end ElboimSly.Cyclic

end

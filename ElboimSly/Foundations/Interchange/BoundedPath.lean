/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Foundations.Interchange.Swap
import Mathlib

/-!
# `ν`-paths on a compact interval

ν-paths (for `J = [a, b]`), restriction, restart, periodicity(a) and the third sentence of
Existence and uniqueness of trajectories.

A `ν`-path on `[a, b]` is a function `f : ℝ → ℤᵈ` of real time whose values outside `[a, b]` are
irrelevant. Such a path is determined by its value at `a`, and also by its value at `b`.
-/

@[expose] public section

open MeasureTheory Filter Topology

namespace ElboimSly.Interchange

variable {d : ℕ} {β : ℝ} [Fact (0 < β)] {ν : Measure (RingSpace d β)}

/-- `z` is the left limit of `f` at `t`, looking only at times above `a`. -/
def IsLeftLimitAbove (a : ℝ) (f : ℝ → Fin d → ℤ) (t : ℝ) (z : Fin d → ℤ) : Prop :=
  ∀ᶠ u in 𝓝[<] t, a < u → f u = z

/-- A `ν`-path on `[a, b]` (ν-paths). -/
def IsPathOn (ν : Measure (RingSpace d β)) (a b : ℝ) (f : ℝ → Fin d → ℤ) : Prop :=
  (∀ t ∈ Set.Ico a b, ∀ᶠ u in 𝓝[≥] t, u ≤ b → f u = f t) ∧
  (∀ t ∈ Set.Ioc a b, ∃ z, IsLeftLimitAbove a f t z) ∧
  {t | t ∈ Set.Ioc a b ∧ ∃ z, IsLeftLimitAbove a f t z ∧ z ≠ f t}.Finite ∧
  (∀ t ∈ Set.Ioc a b, ∀ z, IsLeftLimitAbove a f t z → SwapRule ν t z (f t))

theorem IsLeftLimitAbove.unique {a : ℝ} {f : ℝ → Fin d → ℤ} {t : ℝ} (ht : a < t)
    {z z' : Fin d → ℤ} (h : IsLeftLimitAbove a f t z) (h' : IsLeftLimitAbove a f t z') :
    z = z' := by
  have : (𝓝[<] t).NeBot := nhdsLT_neBot_of_exists_lt ⟨a, ht⟩
  have hev : ∀ᶠ u in 𝓝[<] t, a < u := nhdsWithin_le_nhds (lt_mem_nhds ht)
  obtain ⟨u, h1, h2, h3⟩ := (h.and (h'.and hev)).exists
  exact (h1 h3).symm.trans (h2 h3)

/-- Raising the base point does not change a left limit at a time above it. -/
theorem isLeftLimitAbove_iff {a a' : ℝ} (haa : a ≤ a') {f : ℝ → Fin d → ℤ} {t : ℝ} (ht : a' < t)
    {z : Fin d → ℤ} : IsLeftLimitAbove a' f t z ↔ IsLeftLimitAbove a f t z := by
  have hev : ∀ᶠ u in 𝓝[<] t, a' < u := nhdsWithin_le_nhds (lt_mem_nhds ht)
  constructor
  · intro h
    filter_upwards [h, hev] with u hu hu' _
    exact hu hu'
  · intro h
    filter_upwards [h] with u hu hau
    exact hu (haa.trans_lt hau)

/-- The left limit at `t` only depends on the values strictly between `a` and `t`. -/
theorem IsLeftLimitAbove.congr {a : ℝ} {f g : ℝ → Fin d → ℤ} {t : ℝ} {z : Fin d → ℤ}
    (h : IsLeftLimitAbove a f t z) (hfg : ∀ u, a < u → u < t → g u = f u) :
    IsLeftLimitAbove a g t z := by
  filter_upwards [h, self_mem_nhdsWithin (a := t) (s := Set.Iio t)] with u hu hu' hau
  exact (hfg u hau hu').trans (hu hau)

omit [Fact (0 < β)] in
/-- Restriction of a path to a subinterval. Restriction, restart, periodicity(a). -/
theorem IsPathOn.mono {a b a' b' : ℝ} {f : ℝ → Fin d → ℤ} (h : IsPathOn ν a b f)
    (ha : a ≤ a') (hb : b' ≤ b) : IsPathOn ν a' b' f := by
  refine ⟨fun t ht => ?_, fun t ht => ?_, ?_, fun t ht z hz => ?_⟩
  · filter_upwards [h.1 t ⟨ha.trans ht.1, ht.2.trans_le hb⟩] with u hu hub
    exact hu (hub.trans hb)
  · obtain ⟨z, hz⟩ := h.2.1 t ⟨ha.trans_lt ht.1, ht.2.trans hb⟩
    exact ⟨z, (isLeftLimitAbove_iff ha ht.1).mpr hz⟩
  · refine h.2.2.1.subset ?_
    rintro t ⟨ht, z, hz, hne⟩
    exact ⟨⟨ha.trans_lt ht.1, ht.2.trans hb⟩, z, (isLeftLimitAbove_iff ha ht.1).mp hz, hne⟩
  · exact h.2.2.2 t ⟨ha.trans_lt ht.1, ht.2.trans hb⟩ z ((isLeftLimitAbove_iff ha ht.1).mp hz)

omit [Fact (0 < β)] in
/-- A path on `[a, b]` is determined by its value at `a`. Existence and uniqueness of trajectories, third
sentence. -/
theorem IsPathOn.eq_of_left {a b : ℝ} (_hab : a ≤ b) {f g : ℝ → Fin d → ℤ}
    (hf : IsPathOn ν a b f) (hg : IsPathOn ν a b g) (h0 : f a = g a) :
    ∀ t ∈ Set.Icc a b, f t = g t := by
  by_contra hne
  push Not at hne
  obtain ⟨t0, ht0, hne0⟩ := hne
  set B : Set ℝ := {t | t ∈ Set.Icc a b ∧ f t ≠ g t} with hB
  have hBne : B.Nonempty := ⟨t0, ht0, hne0⟩
  have hbdd : BddBelow B := ⟨a, fun t ht => ht.1.1⟩
  set s := sInf B with hs
  have has : a ≤ s := le_csInf hBne fun t ht => ht.1.1
  have hsb : s ≤ b := (csInf_le hbdd ⟨ht0, hne0⟩).trans ht0.2
  have hA : ∀ u, a ≤ u → u < s → f u = g u := fun u hau hu => by
    by_contra hu'
    exact absurd (csInf_le hbdd (show u ∈ B from ⟨⟨hau, (hu.le.trans hsb)⟩, hu'⟩)) (not_le.mpr hu)
  have hBs : f s = g s := by
    rcases eq_or_lt_of_le has with hz | hpos
    · rw [← hz]; exact h0
    · have hsI : s ∈ Set.Ioc a b := ⟨hpos, hsb⟩
      obtain ⟨z, hz⟩ := hf.2.1 s hsI
      have hz' : IsLeftLimitAbove a g s z := by
        filter_upwards [hz, self_mem_nhdsWithin (a := s) (s := Set.Iio s)] with u hu hu' hau
        exact (hA u hau.le hu').symm.trans (hu hau)
      exact SwapRule.unique (hf.2.2.2 s hsI z hz) (hg.2.2.2 s hsI z hz')
  have hstrict : ∀ u ∈ B, s < u := fun u hu =>
    lt_of_le_of_ne (csInf_le hbdd hu) (fun h => hu.2 (h ▸ hBs))
  rcases eq_or_lt_of_le hsb with hsb' | hsb'
  · obtain ⟨u, hu⟩ := hBne
    exact absurd (hstrict u hu) (not_lt.mpr (hu.1.2.trans hsb'.ge))
  · have hev : ∀ᶠ u in 𝓝[≥] s, u ≤ b → f u = f s := hf.1 s ⟨has, hsb'⟩
    have hev' : ∀ᶠ u in 𝓝[≥] s, u ≤ b → g u = g s := hg.1 s ⟨has, hsb'⟩
    have hevb : ∀ᶠ u in 𝓝[≥] s, u < b := nhdsWithin_le_nhds (gt_mem_nhds hsb')
    obtain ⟨u0, hu0, hsub⟩ := mem_nhdsGE_iff_exists_Ico_subset.mp (hev.and (hev'.and hevb))
    refine absurd (le_csInf hBne fun u hu => ?_) (not_le.mpr hu0)
    by_contra hlt
    have := hsub ⟨(hstrict u hu).le, not_le.mp hlt⟩
    exact hu.2 ((this.1 this.2.2.le).trans (hBs.trans (this.2.1 this.2.2.le).symm))

omit [Fact (0 < β)] in
/-- A path on `[a, b]` is determined by its value at `b`. Existence and uniqueness of trajectories, third
sentence. -/
theorem IsPathOn.eq_of_right (hν : Good ν) {a b : ℝ} (_hab : a ≤ b) {f g : ℝ → Fin d → ℤ}
    (hf : IsPathOn ν a b f) (hg : IsPathOn ν a b g) (h0 : f b = g b) :
    ∀ t ∈ Set.Icc a b, f t = g t := by
  by_contra hne
  push Not at hne
  obtain ⟨t0, ht0, hne0⟩ := hne
  set B : Set ℝ := {t | t ∈ Set.Icc a b ∧ f t ≠ g t} with hB
  have hBne : B.Nonempty := ⟨t0, ht0, hne0⟩
  have hbdd : BddAbove B := ⟨b, fun t ht => ht.1.2⟩
  set s := sSup B with hs
  have hsb : s ≤ b := csSup_le hBne fun t ht => ht.1.2
  have has : a ≤ s := ht0.1.trans (le_csSup hbdd ⟨ht0, hne0⟩)
  have hA : ∀ u, s < u → u ≤ b → f u = g u := fun u hu hub => by
    by_contra hu'
    exact absurd (le_csSup hbdd (show u ∈ B from ⟨⟨has.trans hu.le, hub⟩, hu'⟩)) (not_le.mpr hu)
  have hBs : f s = g s := by
    rcases eq_or_lt_of_le hsb with hz | hlt
    · rw [hz]; exact h0
    · have hev : ∀ᶠ u in 𝓝[≥] s, u ≤ b → f u = f s := hf.1 s ⟨has, hlt⟩
      have hev' : ∀ᶠ u in 𝓝[≥] s, u ≤ b → g u = g s := hg.1 s ⟨has, hlt⟩
      have hevb : ∀ᶠ u in 𝓝[>] s, u ≤ b :=
        (Filter.Eventually.filter_mono nhdsWithin_le_nhds (eventually_lt_nhds hlt)).mono
          fun u hu => hu.le
      obtain ⟨u, ⟨h1, h2⟩, h3, h4⟩ := (((hev.and hev').filter_mono
        (nhdsWithin_mono s Set.Ioi_subset_Ici_self)).and
          (hevb.and self_mem_nhdsWithin)).exists
      exact (h1 h3).symm.trans ((hA u h4 h3).trans (h2 h3))
  have hstrict : ∀ u ∈ B, u < s := fun u hu =>
    lt_of_le_of_ne (le_csSup hbdd hu) (fun h => hu.2 (h ▸ hBs))
  rcases eq_or_lt_of_le has with has' | has'
  · obtain ⟨u, hu⟩ := hBne
    exact absurd (hstrict u hu) (not_lt.mpr (has'.symm.le.trans hu.1.1))
  · have hsI : s ∈ Set.Ioc a b := ⟨has', hsb⟩
    obtain ⟨z, hz⟩ := hf.2.1 s hsI
    obtain ⟨z', hz'⟩ := hg.2.1 s hsI
    have hzz : z = z' := by
      have h1 := SwapRule.symm hν (hf.2.2.2 s hsI z hz)
      have h2 := SwapRule.symm hν (hg.2.2.2 s hsI z' hz')
      rw [← hBs] at h2
      exact SwapRule.unique h1 h2
    subst hzz
    obtain ⟨u0, hu0, hsub⟩ := mem_nhdsLT_iff_exists_Ioo_subset.mp (hz.and hz')
    refine absurd (csSup_le hBne fun u hu => ?_) (not_le.mpr (max_lt hu0 has'))
    by_contra hlt
    have hlt' := not_le.mp hlt
    have hu1 := hstrict u hu
    have := hsub ⟨(le_max_left _ _).trans_lt hlt', hu1⟩
    exact hu.2 ((this.1 ((le_max_right _ _).trans_lt hlt')).trans
      (this.2 ((le_max_right _ _).trans_lt hlt')).symm)

end ElboimSly.Interchange

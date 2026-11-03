/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Foundations.Cyclic.CPathLeft
public import Mathlib

/-!
# Nearest-neighbour paths and cutting

World-lines, records, exploration plans (the measurable subset `Path` of `Path_{ℤᵈ}` of paths all of whose jumps
have `ℓ¹`-size `1`).

`CPath.UnitJumps p` says `‖p(s) - p(s-)‖₁ = 1` at every discontinuity `s`. `CycPath d` is the
subtype of `CPath (Fin d → ℤ)` with this property, with the induced σ-algebra (a measurable
subset: see `CPath.unitJumps_iff`, which expresses the property on the jump list).

`CPath.cut p ℓ` is `(ℓ, p(· ∧ ℓ))` for `ℓ ∈ [0, ∞]`; it preserves `UnitJumps`.
-/

@[expose] public section

open MeasureTheory Set Filter Topology
open scoped ENNReal NNReal

namespace ElboimSly.Cyclic

variable {d : ℕ}

/-- All jumps have `ℓ¹`-size `1`. -/
def CPath.UnitJumps (p : CPath (Fin d → ℤ)) : Prop :=
  ∀ s ∈ CDisc p.fn, ∑ i, |p.fn s i - p.left s i| = 1

/-- Nearest-neighbour paths with finitely many jumps and a length. World-lines, records, exploration plans. -/
abbrev CycPath (d : ℕ) : Type := {p : CPath (Fin d → ℤ) // p.UnitJumps}

/-- The path `p(· ∧ ℓ)` of length `ℓ ∈ [0, ∞]`. -/
noncomputable def CPath.cut {V : Type*} (p : CPath V) (ℓ : ℝ≥0∞) : CPath V :=
  open scoped Classical in
  if ℓ = ⊤ then ⟨⊤, p.fn, p.rc, p.fin, fun s s' h _ => absurd h (by simp)⟩
  else p.stop ℓ.toNNReal

@[simp] theorem CPath.cut_len {V : Type*} (p : CPath V) (ℓ : ℝ≥0∞) : (p.cut ℓ).len = ℓ := by
  unfold CPath.cut
  split_ifs with h
  · exact h.symm
  · exact ENNReal.coe_toNNReal h

theorem CPath.cut_fn {V : Type*} (p : CPath V) (ℓ : ℝ≥0∞) (s : ℝ≥0) :
    (p.cut ℓ).fn s = p.fn (min (s : ℝ≥0∞) ℓ).toNNReal := by
  unfold CPath.cut
  split_ifs with h
  · simp [h]
  · simp only [CPath.stop_fn]
    congr 1
    rcases le_total (s : ℝ≥0∞) ℓ with hsl | hls
    · rw [min_eq_left hsl]
      have : s ≤ ℓ.toNNReal := by
        rw [← ENNReal.coe_le_coe, ENNReal.coe_toNNReal h]; exact hsl
      simp [min_eq_left this]
    · rw [min_eq_right hls]
      have : ℓ.toNNReal ≤ s := by
        rw [← ENNReal.coe_le_coe, ENNReal.coe_toNNReal h]; exact hls
      simp [min_eq_right this]

theorem CPath.CDisc_stop_subset {V : Type*} (p : CPath V) (t : ℝ≥0) :
    CDisc (p.stop t).fn ⊆ CDisc p.fn ∩ Iic t := by
  intro s hs
  obtain ⟨hs0, hs1⟩ := hs
  have hst : s ≤ t := by
    by_contra hts
    push Not at hts
    refine hs1 ?_
    have h1 : ∀ᶠ u in 𝓝[<] s, t < u :=
      eventually_nhdsWithin_of_eventually_nhds (Ioi_mem_nhds hts)
    filter_upwards [h1] with u hu
    simp [CPath.stop_fn, min_eq_right hu.le, min_eq_right hts.le]
  refine ⟨⟨hs0, fun hev => hs1 ?_⟩, hst⟩
  filter_upwards [hev, self_mem_nhdsWithin (a := s) (s := Iio s)] with u hu hus
  have hut : u ≤ t := le_trans (le_of_lt (Set.mem_Iio.mp hus)) hst
  simp only [CPath.stop_fn, min_eq_left hut, min_eq_left hst]
  exact hu


theorem CPath.left_stop (p : CPath (Fin d → ℤ)) (t : ℝ≥0) {s : ℝ≥0} (hs : 0 < s) (hst : s ≤ t) :
    (p.stop t).left s = p.left s := by
  refine (p.stop t).left_eq_of_eventually hs ?_
  filter_upwards [p.eventually_left hs, self_mem_nhdsWithin (a := s) (s := Iio s)] with u hu hus
  have hut : u ≤ t := le_trans (le_of_lt (Set.mem_Iio.mp hus)) hst
  simp only [CPath.stop_fn, min_eq_left hut]
  exact hu

theorem CPath.left_cut {V : Type*} [MeasurableSpace V] [Countable V] [MeasurableSingletonClass V]
    (p : CPath V) (ℓ : ℝ≥0∞) {s : ℝ≥0} (hs : 0 < s) (hsl : (s : ℝ≥0∞) ≤ ℓ) :
    (p.cut ℓ).left s = p.left s := by
  refine (p.cut ℓ).left_eq_of_eventually hs ?_
  filter_upwards [p.eventually_left hs, self_mem_nhdsWithin (a := s) (s := Iio s)] with u hu hus
  have hus' : (u : ℝ≥0∞) ≤ ℓ := (ENNReal.coe_le_coe.mpr (le_of_lt (Set.mem_Iio.mp hus))).trans hsl
  rw [CPath.cut_fn, min_eq_left hus']
  simpa using hu

theorem CPath.UnitJumps.cut {p : CPath (Fin d → ℤ)} (h : p.UnitJumps) (ℓ : ℝ≥0∞) :
    (p.cut ℓ).UnitJumps := by
  intro s hs
  have hs0 : 0 < s := hs.1
  by_cases hℓ : ℓ = ⊤
  · have hfn : (p.cut ℓ).fn = p.fn := by
      funext x; simp [CPath.cut_fn, hℓ]
    rw [hfn] at hs ⊢
    have hl : (p.cut ℓ).left s = p.left s :=
      (p.cut ℓ).left_eq_of_eventually hs0 (by rw [hfn]; exact p.eventually_left hs0)
    rw [hl]
    exact h s hs
  · have hc : p.cut ℓ = p.stop ℓ.toNNReal := by simp [CPath.cut, hℓ]
    rw [hc] at hs ⊢
    obtain ⟨hs1, hs2⟩ := CPath.CDisc_stop_subset p _ hs
    have hs2' : s ≤ ℓ.toNNReal := hs2
    rw [CPath.left_stop p _ hs0 hs2']
    simp only [CPath.stop_fn, min_eq_left hs2']
    exact h s hs1

/-- The truncation `(ℓ, p(· ∧ ℓ))` of a nearest-neighbour path. -/
noncomputable def CycPath.cut (p : CycPath d) (ℓ : ℝ≥0∞) : CycPath d := ⟨p.1.cut ℓ, p.2.cut ℓ⟩

end ElboimSly.Cyclic

end

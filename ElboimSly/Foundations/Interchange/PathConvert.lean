/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Foundations.Interchange.BoundedPath
public import ElboimSly.Frozen.Defs.IsForwardPath
public import ElboimSly.Frozen.Defs.IsBackwardPath
import Mathlib

/-!
# From half-line paths to real-time paths on `[a, b]`

ν-paths; Restriction, restart, periodicity(a).

A forward path `γ` from time `a` (with `γ s` the position at time `a + s`) gives the real-time path
`t ↦ γ (t - a)` on `[a, b]` for every `b`. A backward path `η` from time `b` (with `η s` the position
at time `b - s`) gives `t ↦ η (b - t)` on `[a, b]` for every `a`.
-/

@[expose] public section

open MeasureTheory Filter Topology
open scoped NNReal

namespace ElboimSly.Interchange

variable {d : ℕ} {β : ℝ} [Fact (0 < β)] {ν : Measure (RingSpace d β)}

/-- The real-time version of a forward half-line path from time `a`. -/
def fwdReal (a : ℝ) (γ : ℝ≥0 → Fin d → ℤ) (t : ℝ) : Fin d → ℤ := γ (t - a).toNNReal

/-- The real-time version of a backward half-line path from time `b`. -/
def bwdReal (b : ℝ) (η : ℝ≥0 → Fin d → ℤ) (t : ℝ) : Fin d → ℤ := η (b - t).toNNReal

section forward

variable {a : ℝ} {γ : ℝ≥0 → Fin d → ℤ}

theorem tendsto_fwd_ge (t : ℝ) :
    Tendsto (fun u : ℝ => (u - a).toNNReal) (𝓝[≥] t) (𝓝[≥] (t - a).toNNReal) := by
  refine tendsto_nhdsWithin_iff.mpr ⟨?_, ?_⟩
  · exact ((continuous_real_toNNReal.comp (continuous_id.sub continuous_const)).tendsto t).mono_left
      nhdsWithin_le_nhds
  · filter_upwards [self_mem_nhdsWithin (a := t) (s := Set.Ici t)] with u hu
    exact Real.toNNReal_le_toNNReal (sub_le_sub_right hu a)

theorem tendsto_fwd_lt {t : ℝ} (ht : a < t) :
    Tendsto (fun u : ℝ => (u - a).toNNReal) (𝓝[<] t) (𝓝[<] (t - a).toNNReal) := by
  refine tendsto_nhdsWithin_iff.mpr ⟨?_, ?_⟩
  · exact ((continuous_real_toNNReal.comp (continuous_id.sub continuous_const)).tendsto t).mono_left
      nhdsWithin_le_nhds
  · filter_upwards [self_mem_nhdsWithin (a := t) (s := Set.Iio t)] with u hu
    exact (Real.toNNReal_lt_toNNReal_iff (sub_pos.mpr ht)).mpr (sub_lt_sub_right hu a)

theorem fwdReal_isLeftLimitAbove {t : ℝ} (ht : a < t) {z : Fin d → ℤ}
    (hz : IsLeftLimit γ (t - a).toNNReal z) : IsLeftLimitAbove a (fwdReal a γ) t z :=
  ((tendsto_fwd_lt ht).eventually hz).mono fun _ hu _ => hu

omit [Fact (0 < β)] in
/-- A forward half-line path is a path on every `[a, b]`. -/
theorem IsForwardPath.toPathOn {ν : Measure (RingSpace d β)} (h : IsForwardPath ν a γ) (b : ℝ) :
    IsPathOn ν a b (fwdReal a γ) := by
  have hcoe : ∀ {t : ℝ}, a < t → a + ((t - a).toNNReal : ℝ) = t := fun {t} ht => by
    rw [Real.coe_toNNReal _ (sub_pos.mpr ht).le]; ring
  have hpos : ∀ {t : ℝ}, a < t → 0 < (t - a).toNNReal := fun {t} ht =>
    Real.toNNReal_pos.mpr (sub_pos.mpr ht)
  have key : ∀ {t : ℝ}, a < t → ∀ z, IsLeftLimitAbove a (fwdReal a γ) t z →
      IsLeftLimit γ (t - a).toNNReal z := fun {t} ht z hz => by
    obtain ⟨z', hz'⟩ := h.2.1 _ (hpos ht)
    exact ((fwdReal_isLeftLimitAbove ht hz').unique ht hz) ▸ hz'
  refine ⟨fun t ht => ?_, fun t ht => ?_, ?_, fun t ht z hz => ?_⟩
  · filter_upwards [(tendsto_fwd_ge t).eventually (h.1 _)] with u hu _
    exact hu
  · obtain ⟨z, hz⟩ := h.2.1 _ (hpos ht.1)
    exact ⟨z, fwdReal_isLeftLimitAbove ht.1 hz⟩
  · refine ((h.2.2.1 (b - a).toNNReal).image (fun s : ℝ≥0 => a + (s : ℝ))).subset ?_
    rintro t ⟨ht, z, hz, hne⟩
    have hzl := key ht.1 z hz
    refine ⟨(t - a).toNNReal, ⟨hpos ht.1, ?_, z, hzl, hne⟩, hcoe ht.1⟩
    exact Real.toNNReal_le_toNNReal (sub_le_sub_right ht.2 a)
  · have := h.2.2.2 _ (hpos ht.1) z (key ht.1 z hz)
    rwa [hcoe ht.1] at this

end forward

section backward

variable {b : ℝ} {η : ℝ≥0 → Fin d → ℤ}

theorem tendsto_bwd_ge (t : ℝ) :
    Tendsto (fun u : ℝ => (b - u).toNNReal) (𝓝[≥] t) (𝓝[≤] (b - t).toNNReal) := by
  refine tendsto_nhdsWithin_iff.mpr ⟨?_, ?_⟩
  · exact ((continuous_real_toNNReal.comp (continuous_const.sub continuous_id)).tendsto t).mono_left
      nhdsWithin_le_nhds
  · filter_upwards [self_mem_nhdsWithin (a := t) (s := Set.Ici t)] with u hu
    exact Real.toNNReal_le_toNNReal (sub_le_sub_left hu b)

theorem tendsto_bwd_lt {t : ℝ} (ht : t ≤ b) :
    Tendsto (fun u : ℝ => (b - u).toNNReal) (𝓝[<] t) (𝓝[>] (b - t).toNNReal) := by
  refine tendsto_nhdsWithin_iff.mpr ⟨?_, ?_⟩
  · exact ((continuous_real_toNNReal.comp (continuous_const.sub continuous_id)).tendsto t).mono_left
      nhdsWithin_le_nhds
  · filter_upwards [self_mem_nhdsWithin (a := t) (s := Set.Iio t)] with u hu
    exact (Real.toNNReal_lt_toNNReal_iff (sub_pos.mpr (hu.trans_le ht))).mpr (sub_lt_sub_left hu b)

theorem bwdReal_isLeftLimitAbove {a t : ℝ} (ht : t ≤ b) {z : Fin d → ℤ}
    (hz : IsRightLimit η (b - t).toNNReal z) : IsLeftLimitAbove a (bwdReal b η) t z :=
  ((tendsto_bwd_lt ht).eventually hz).mono fun _ hu _ => hu

omit [Fact (0 < β)] in
/-- A backward half-line path is a path on every `[a, b]`. -/
theorem IsBackwardPath.toPathOn {ν : Measure (RingSpace d β)} (h : IsBackwardPath ν b η) (a : ℝ) :
    IsPathOn ν a b (bwdReal b η) := by
  have hcoe : ∀ {t : ℝ}, t ≤ b → b - ((b - t).toNNReal : ℝ) = t := fun {t} ht => by
    rw [Real.coe_toNNReal _ (sub_nonneg.mpr ht)]; ring
  have key : ∀ {t : ℝ}, a < t → t ≤ b → ∀ z, IsLeftLimitAbove a (bwdReal b η) t z →
      IsRightLimit η (b - t).toNNReal z := fun {t} hat ht z hz => by
    obtain ⟨z', hz'⟩ := h.2.1 (b - t).toNNReal
    exact ((bwdReal_isLeftLimitAbove (a := a) ht hz').unique hat hz) ▸ hz'
  refine ⟨fun t ht => ?_, fun t ht => ?_, ?_, fun t ht z hz => ?_⟩
  · filter_upwards [(tendsto_bwd_ge t).eventually (h.1 _)] with u hu _
    exact hu
  · obtain ⟨z, hz⟩ := h.2.1 (b - t).toNNReal
    exact ⟨z, bwdReal_isLeftLimitAbove ht.2 hz⟩
  · refine ((h.2.2.1 (b - a).toNNReal).image (fun s : ℝ≥0 => b - (s : ℝ))).subset ?_
    rintro t ⟨ht, z, hz, hne⟩
    have hzl := key ht.1 ht.2 z hz
    refine ⟨(b - t).toNNReal, ⟨?_, z, hzl, hne⟩, hcoe ht.2⟩
    exact Real.toNNReal_le_toNNReal (sub_le_sub_left ht.1.le b)
  · have := h.2.2.2 (b - t).toNNReal z (key ht.1 ht.2 z hz)
    rwa [hcoe ht.2] at this

end backward

end ElboimSly.Interchange

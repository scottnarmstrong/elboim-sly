/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Foundations.Cyclic.CycSchemeEnvTruncNth
public import ElboimSly.Foundations.Cyclic.CycSchemeEnvLim
public import ElboimSly.Foundations.Cyclic.CycRecLimitSpec
public import Mathlib

/-!
# The environment scheme (c): the explored region of the limit record

The environment scheme (c): "regions of growing records are increasing with union the
region of the limit". For a trajectory of the scheme:

* `CycRec.region_mono_of_extends`: a record that extends another has a larger region;
* `Traj.region_recLim_eq`: `R(Φ) = ⋃_j R(ρ_j)` for the limit record `Φ` of the records `ρ_j`
  (any `s_∘`). A point of `R(Φ)` lies in the region of a single `ρ_j`, because the limit entries
  are either attained by a `ρ_j` (finite stopping length or finite horizon) or have infinite length,
  in which case the region of a longer and longer piece contains it.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped ENNReal NNReal

namespace ElboimSly.Cyclic

variable {I : Type*} [MeasurableSpace I] {d : ℕ} {β : ℝ} [Fact (0 < β)]

omit [MeasurableSpace I] [Fact (0 < β)] in
theorem CycEntry.region_mono_of_piece {e e' : CycEntry I d} (hd : e.data = e'.data)
    (hp : e.path.IsPiece e'.path) : e.region β ⊆ e'.region β := by
  rintro x ⟨r, hr0, hrl, hcopy, hclock, hmem⟩
  refine ⟨r, hr0, hrl.trans hp.1, ?_, ?_, ?_⟩
  · rw [← hd]; exact hcopy
  · rw [← hd]; exact hclock
  · have h1 : e.path.left r = e'.path.left r := by
      calc e.path.left r = (e'.path.cut e.path.len).left r := by rw [← hp.2]
        _ = e'.path.left r := CPath.left_cut _ _ hr0 hrl
    rw [← h1]; exact hmem

omit [MeasurableSpace I] [Fact (0 < β)] in
theorem CycRec.region_mono_of_extends {ρ ρ' : CycRec I d} (h : ρ.Extends ρ') :
    ρ.region β ⊆ ρ'.region β := by
  rintro x ⟨e, ⟨k, hk⟩, hx⟩
  obtain ⟨e', he', hd, hp⟩ := h k e hk
  exact ⟨e', ⟨k, he'⟩, CycEntry.region_mono_of_piece hd hp hx⟩

namespace CycSchemeEnv

omit [MeasurableSpace I] [Fact (0 < β)] in
theorem mem_region_cut_iff (δ : CycData I d) (p : CycPath d) (ℓ : ℝ≥0∞)
    (x : I × RingSpace d β) :
    x ∈ CycEntry.region β ((δ, p.cut ℓ) : CycEntry I d) ↔
      ∃ r : ℝ≥0, 0 < r ∧ (r : ℝ≥0∞) ≤ ℓ ∧ x.1 = δ.copy ∧ x.2.2 = δ.clock β r ∧
        Edge.Mem (p.1.left r) x.2.1 := by
  constructor
  · rintro ⟨r, hr0, hrl, h1, h2, h3⟩
    have hrl' : (r : ℝ≥0∞) ≤ ℓ := by
      have : CycEntry.len ((δ, p.cut ℓ) : CycEntry I d) = ℓ := CPath.cut_len _ _
      rwa [this] at hrl
    refine ⟨r, hr0, hrl', h1, h2, ?_⟩
    have : (p.cut ℓ).1.left r = p.1.left r := CPath.left_cut _ _ hr0 hrl'
    rw [← this]; exact h3
  · rintro ⟨r, hr0, hrl, h1, h2, h3⟩
    have hlen : CycEntry.len ((δ, p.cut ℓ) : CycEntry I d) = ℓ := CPath.cut_len _ _
    refine ⟨r, hr0, by rw [hlen]; exact hrl, h1, h2, ?_⟩
    have : (p.cut ℓ).1.left r = p.1.left r := CPath.left_cut _ _ hr0 hrl
    show Edge.Mem ((p.cut ℓ).1.left r) x.2.1
    rw [this]; exact h3

end CycSchemeEnv

end ElboimSly.Cyclic

end

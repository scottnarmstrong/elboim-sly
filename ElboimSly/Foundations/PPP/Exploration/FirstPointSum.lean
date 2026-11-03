/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Foundations.PPP.Exploration.FirstPointProb
import Mathlib

/-!
# The grid argument: two-sided bound on `P(first event)`

First-point law of a deterministic probe, proof of (c).
-/

@[expose] public section

open MeasureTheory
open scoped ENNReal NNReal

namespace ElboimSly

variable {S : Type*} [MeasurableSpace S] {μ : Measure S} [SigmaFinite μ] {R : S → ℝ≥0∞} {h : ℝ≥0}
  {W : Measure (Measure S)}

omit [SigmaFinite μ] in
theorem ae_region_zero_eq_zero (hW : IsPPPLaw μ W) (hP : IsProbe μ R h) :
    ∀ᵐ ν ∂W, ν (probeRegion R 0) = 0 := by
  have hA := measurableSet_probeRegion hP.measurable 0
  have h1 := hW.lintegral_count hA
  have h0 : μ (probeRegion R 0) = 0 := probeMass_zero hP
  rw [h0] at h1
  exact (lintegral_eq_zero_iff (Measure.measurable_coe hA)).1 h1

theorem ae_rho_ne_zero (hW : IsPPPLaw μ W) (hP : IsProbe μ R h) (hh : 0 < h) :
    ∀ᵐ ν ∂W, probeRho μ R h ν ≠ 0 := by
  filter_upwards [ae_goodSet hW hP MeasurableSet.univ, ae_region_zero_eq_zero hW hP] with
    ν hν h0 hρ
  have := (probeRho_le_iff hP.measurable hν.1 hν.2.1 (r := 0) (by exact_mod_cast hh)).1 hρ.le
  rw [h0] at this
  exact absurd this (by simp)

variable (hW : IsPPPLaw μ W) (hP : IsProbe μ R h) (hh : 0 < h) {B : Set S}
  (hB : MeasurableSet B) {L : ℕ} (hL : 0 < L)

include hW hP hh hB hL in
theorem sum_cellEvent_le :
    ∑ i ∈ Finset.Icc 1 L, W (cellEvent R h B L i) ≤ W (firstEvent μ R h B) := by
  have hR := hP.measurable
  have hgood := ae_goodSet hW hP hB
  calc ∑ i ∈ Finset.Icc 1 L, W (cellEvent R h B L i)
      ≤ ∑ i ∈ Finset.Icc 1 L, W (firstEvent μ R h B ∩ cellIndex μ R h L i) := by
        refine Finset.sum_le_sum fun i hi => ?_
        rw [Finset.mem_Icc] at hi
        refine measure_mono_ae ?_
        filter_upwards [hgood] with ν hν hc
        exact cellEvent_good_subset hR hh hB hL hi.1 hi.2 hν hc
    _ = W (⋃ i ∈ Finset.Icc 1 L, (firstEvent μ R h B ∩ cellIndex μ R h L i)) := by
        refine (measure_biUnion_finset ?_ fun i _ =>
          (measurableSet_firstEvent hR hB).inter (measurableSet_cellIndex hR L i)).symm
        intro i _ j _ hij
        exact (pairwiseDisjoint_cellIndex L hij).mono Set.inter_subset_right
          Set.inter_subset_right
    _ ≤ W (firstEvent μ R h B) := measure_mono (Set.iUnion₂_subset fun i _ =>
        Set.inter_subset_left)

include hW hP hh hB hL in
theorem firstEvent_le_sum :
    W (firstEvent μ R h B) ≤ ∑ i ∈ Finset.Icc 1 L,
      (W (cellEvent R h B L i) + W {ν | 2 ≤ ν (gridCell R h L i)}) := by
  have hR := hP.measurable
  have hgood := ae_goodSet hW hP hB
  calc W (firstEvent μ R h B)
      ≤ W (⋃ i ∈ Finset.Icc 1 L, (cellEvent R h B L i ∪ {ν | 2 ≤ ν (gridCell R h L i)})) := by
        refine measure_mono_ae ?_
        filter_upwards [hgood, ae_rho_ne_zero hW hP hh] with ν hν hne hf
        have hρh : probeRho μ R h ν ≤ h := probeRho_le_h
        rcases exists_grid_index hL hρh with h0 | ⟨i, hi1, hiL, hlt, hle⟩
        · exact absurd (le_antisymm h0 bot_le) hne
        · simp only [Set.mem_iUnion, Finset.mem_Icc]
          exact ⟨i, ⟨hi1, hiL⟩, cellEvent_of_firstEvent hR hB hi1 hiL hν hf ⟨hlt, hle⟩⟩
    _ ≤ ∑ i ∈ Finset.Icc 1 L,
          W (cellEvent R h B L i ∪ {ν | 2 ≤ ν (gridCell R h L i)}) :=
        measure_biUnion_finset_le _ _
    _ ≤ _ := Finset.sum_le_sum fun i _ => measure_union_le _ _

end ElboimSly

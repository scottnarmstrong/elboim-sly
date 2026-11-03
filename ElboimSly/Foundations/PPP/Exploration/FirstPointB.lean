/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Foundations.PPP.Exploration.FirstPointC
import Mathlib

/-!
# First-point law, parts (a) and (b)

First-point law of a deterministic probe (a), (b).
-/

@[expose] public section

open MeasureTheory
open scoped ENNReal NNReal

namespace ElboimSly

variable {S : Type*} [MeasurableSpace S] {μ : Measure S} [SigmaFinite μ] {R : S → ℝ≥0∞}
  {h : ℝ≥0} {W : Measure (Measure S)}

theorem exists_grid_good (hP : IsProbe μ R h) {δ : ℝ≥0} (hδ : 0 < δ) :
    ∃ (L : ℕ) (_ : 0 < L) (ε : ℝ≥0), (ε : ℝ≥0∞) * μ (probeRegion R h) ≤ δ ∧
      ∀ i ∈ Finset.Icc 1 L, μ (gridCell R h L i) ≤ ε := by
  set M : ℝ≥0 := (μ (probeRegion R h)).toNNReal with hM
  have hMh : μ (probeRegion R h) = M := (ENNReal.coe_toNNReal hP.mass_lt_top.ne).symm
  have hε : 0 < δ / (M + 1) := div_pos hδ (by positivity)
  obtain ⟨L, hL, hcell⟩ := exists_grid_small hP hε
  refine ⟨L, hL, δ / (M + 1), ?_, fun i hi => ?_⟩
  · rw [hMh, ← ENNReal.coe_mul]
    refine ENNReal.coe_le_coe.2 ?_
    rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
    nlinarith [M.2]
  · have hi' := Finset.mem_Icc.1 hi
    exact hcell i hi'.1 hi'.2

/-- First-point law of a deterministic probe (b): almost surely on `{D(h) hit}`, `V(S) = 1`. -/
theorem ae_succ_V_univ (hW : IsPPPLaw μ W) (hP : IsProbe μ R h) (hh : 0 < h) :
    ∀ᵐ ν ∂W, 1 ≤ tau μ ν (probeRegion R h) → probeV μ R h ν Set.univ = 1 := by
  have hR := hP.measurable
  rw [ae_iff]
  have : {ν : Measure S | ¬ (1 ≤ tau μ ν (probeRegion R h) → probeV μ R h ν Set.univ = 1)} ⊆
      {ν | 1 ≤ tau μ ν (probeRegion R h) ∧ probeV μ R h ν Set.univ ≠ 1} := by
    intro ν hν
    simpa using hν
  refine le_antisymm ?_ zero_le
  refine ENNReal.le_of_forall_pos_le_add fun δ hδ _ => ?_
  obtain ⟨L, hL, ε, hεM, hcell⟩ := exists_grid_good hP hδ
  have hgood := ae_goodSet hW hP MeasurableSet.univ
  calc W _ ≤ W (⋃ i ∈ Finset.Icc 1 L, {ν | 2 ≤ ν (gridCell R h L i)}) := by
        refine (measure_mono this).trans (measure_mono_ae ?_)
        filter_upwards [hgood, ae_rho_ne_zero hW hP hh] with ν hν hne hbad
        obtain ⟨hlf, hreg, -, -⟩ := hν
        obtain ⟨hs, hV⟩ := hbad
        rw [tau_of_mem μ hlf] at hs
        rw [probeV_univ hlf] at hV
        have h1 := one_le_measure_region hR hlf hreg hs
        obtain ⟨n, hn⟩ := exists_natCast_measure_region (μ := μ) (ν := ν) hR MeasurableSet.univ
          (by simpa using hreg)
        rw [Set.inter_univ] at hn
        have h2 : 2 ≤ ν (probeRegion R (probeRho μ R h ν)) := by
          rw [hn] at h1 hV ⊢
          have : 1 ≤ n := by exact_mod_cast h1
          have : n ≠ 1 := fun e => hV (by rw [e]; simp)
          exact_mod_cast (by omega : 2 ≤ n)
        rcases exists_grid_index hL (r := probeRho μ R h ν) probeRho_le_h with h0 | ⟨i, hi1, hiL, hlt, hle⟩
        · exact absurd (le_antisymm h0 bot_le) hne
        · simp only [Set.mem_iUnion, Finset.mem_Icc]
          exact ⟨i, ⟨hi1, hiL⟩, two_le_cell_of_two_le hR hlf hreg
            (gridTime_mono (Nat.sub_le i 1)) hlt hle h2⟩
    _ ≤ ∑ i ∈ Finset.Icc 1 L, W {ν | 2 ≤ ν (gridCell R h L i)} :=
        measure_biUnion_finset_le _ _
    _ ≤ 0 + δ := by
        rw [zero_add]
        exact (sum_two_le_aux hW hP hL hcell).trans hεM

/-- First-point law of a deterministic probe (a): `P(N(D h) = 0) = e^{-m(h)}`. -/
theorem measure_not_succ (hW : IsPPPLaw μ W) (hP : IsProbe μ R h) :
    W {ν | ¬ 1 ≤ tau μ ν (probeRegion R h)} = expNeg (probeMass μ R h) := by
  have hA := measurableSet_probeRegion hP.measurable h
  unfold probeMass
  rw [← hW.measure_count_eq_natCast_zero hA hP.mass_lt_top]
  refine measure_congr ?_
  filter_upwards [ae_goodSet hW hP MeasurableSet.univ] with ν hν
  obtain ⟨hlf, hreg, -, -⟩ := hν
  obtain ⟨n, hn⟩ := hreg.2
  simp only [Set.inter_univ] at hn
  rw [tau_of_mem μ hlf, hn]
  simp only [eq_iff_iff, not_le]
  constructor
  · intro h1
    have : n < 1 := by exact_mod_cast h1
    have : n = 0 := by omega
    simp [this]
  · intro h0
    rw [h0]; exact zero_lt_one

end ElboimSly

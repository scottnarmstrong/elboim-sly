/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Foundations.PPP.Exploration.FirstPointLimit
import Mathlib

/-!
# First-point law, part (c)

First-point law of a deterministic probe (c): the probability that `D(h)` is hit, `V(S) = 1` and `V(B) = 1`
equals `∫_{D(h) ∩ B} e^{-m(R x)} μ(dx)`.
-/

@[expose] public section

open MeasureTheory
open scoped ENNReal NNReal

namespace ElboimSly

variable {S : Type*} [MeasurableSpace S] {μ : Measure S} [SigmaFinite μ] {R : S → ℝ≥0∞}
  {h : ℝ≥0} {W : Measure (Measure S)}

theorem ofReal_sq_div_two_le {x ε : ℝ} (hx : 0 ≤ x) (hxε : x ≤ ε) :
    ENNReal.ofReal (x ^ 2 / 2) ≤ ENNReal.ofReal ε * ENNReal.ofReal x := by
  rw [← ENNReal.ofReal_mul (hx.trans hxε)]
  refine ENNReal.ofReal_le_ofReal ?_
  nlinarith

omit [SigmaFinite μ] in
theorem sum_two_le_aux (hW : IsPPPLaw μ W) (hP : IsProbe μ R h) {L : ℕ} (hL : 0 < L)
    {ε : ℝ≥0} (hε : ∀ i ∈ Finset.Icc 1 L, μ (gridCell R h L i) ≤ ε) :
    ∑ i ∈ Finset.Icc 1 L, W {ν | 2 ≤ ν (gridCell R h L i)} ≤ ε * μ (probeRegion R h) := by
  have hR := hP.measurable
  have hsum := sum_measure_cell_le hP MeasurableSet.univ hL
  simp only [Set.inter_univ] at hsum
  calc _ ≤ ∑ i ∈ Finset.Icc 1 L, (ε : ℝ≥0∞) * μ (gridCell R h L i) := by
        refine Finset.sum_le_sum fun i hi => ?_
        have hfin : μ (gridCell R h L i) < ∞ := lt_of_le_of_lt (hε i hi) ENNReal.coe_lt_top
        refine (hW.measure_two_le_count_le (measurableSet_gridCell hR L i) hfin).trans ?_
        have hx : (μ (gridCell R h L i)).toReal ≤ ε :=
          ENNReal.toReal_le_of_le_ofReal ε.2 (by
            simpa [ENNReal.ofReal_coe_nnreal] using hε i hi)
        refine (ofReal_sq_div_two_le ENNReal.toReal_nonneg hx).trans (le_of_eq ?_)
        rw [ENNReal.ofReal_coe_nnreal, ENNReal.ofReal_toReal hfin.ne]
    _ = ε * ∑ i ∈ Finset.Icc 1 L, μ (gridCell R h L i) := by rw [Finset.mul_sum]
    _ ≤ _ := by gcongr

/-- First-point law of a deterministic probe (c). -/
theorem measure_firstEvent (hW : IsPPPLaw μ W) (hP : IsProbe μ R h) (hh : 0 < h) {B : Set S}
    (hB : MeasurableSet B) : W (firstEvent μ R h B) = firstIntegral μ R h B := by
  set M : ℝ≥0 := (μ (probeRegion R h)).toNNReal with hM
  have hMh : μ (probeRegion R h) = M := (ENNReal.coe_toNNReal hP.mass_lt_top.ne).symm
  have key : ∀ δ : ℝ≥0, 0 < δ → ∃ (L : ℕ) (_ : 0 < L) (ε : ℝ≥0), (ε : ℝ≥0∞) * μ (probeRegion R h) ≤ δ ∧
      ∀ i ∈ Finset.Icc 1 L, μ (gridCell R h L i) ≤ ε := by
    intro δ hδ
    have hε : 0 < δ / (M + 1) := div_pos hδ (by positivity)
    obtain ⟨L, hL, hcell⟩ := exists_grid_small hP hε
    refine ⟨L, hL, δ / (M + 1), ?_, fun i hi => ?_⟩
    · rw [hMh, ← ENNReal.coe_mul]
      refine ENNReal.coe_le_coe.2 ?_
      rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
      nlinarith [M.2]
    · have hi' := Finset.mem_Icc.1 hi
      exact hcell i hi'.1 hi'.2
  apply le_antisymm
  · refine ENNReal.le_of_forall_pos_le_add fun δ hδ _ => ?_
    obtain ⟨L, hL, ε, hεM, hcell⟩ := key δ hδ
    calc W (firstEvent μ R h B)
        ≤ ∑ i ∈ Finset.Icc 1 L, (W (cellEvent R h B L i) + W {ν | 2 ≤ ν (gridCell R h L i)}) :=
          firstEvent_le_sum hW hP hh hB hL
      _ = ∑ i ∈ Finset.Icc 1 L, W (cellEvent R h B L i) +
            ∑ i ∈ Finset.Icc 1 L, W {ν | 2 ≤ ν (gridCell R h L i)} := Finset.sum_add_distrib
      _ ≤ firstIntegral μ R h B + δ := by
          refine add_le_add ?_ ((sum_two_le_aux hW hP hL hcell).trans hεM)
          rw [Finset.sum_congr rfl fun i hi => measure_cellEvent hW hP hB hL
            (Finset.mem_Icc.1 hi).1 (Finset.mem_Icc.1 hi).2]
          exact sum_le_firstIntegral hP hB hL
  · refine ENNReal.le_of_forall_pos_le_add fun δ hδ _ => ?_
    obtain ⟨L, hL, ε, hεM, hcell⟩ := key δ hδ
    calc firstIntegral μ R h B
        ≤ ∑ i ∈ Finset.Icc 1 L, μ (gridCell R h L i ∩ B) *
            expNeg (probeMass μ R (gridTime h L i)) + ε * μ (probeRegion R h) :=
          firstIntegral_le_sum_add hP hB hL (ε := ε) hcell
      _ ≤ W (firstEvent μ R h B) + δ := by
          refine add_le_add ?_ hεM
          rw [← Finset.sum_congr rfl fun i hi => measure_cellEvent hW hP hB hL
            (Finset.mem_Icc.1 hi).1 (Finset.mem_Icc.1 hi).2]
          exact sum_cellEvent_le hW hP hh hB hL

end ElboimSly

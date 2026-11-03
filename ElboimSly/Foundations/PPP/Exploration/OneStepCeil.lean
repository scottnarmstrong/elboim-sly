/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Foundations.PPP.Exploration.OneStepGrid
import Mathlib

/-!
# Properties of the grid ceiling

The unexplored part after one step, Step 2.
-/

@[expose] public section

open MeasureTheory
open scoped ENNReal NNReal

namespace ElboimSly

variable {h : ℝ≥0}

theorem gridTime_succ_sub {L : ℕ} (hL : 0 < L) {i : ℕ} (hi : 1 ≤ i) :
    gridTime h L i = gridTime h L (i - 1) + h / L := by
  obtain ⟨j, rfl⟩ : ∃ j, i = j + 1 := ⟨i - 1, by omega⟩
  have : (L : ℝ≥0) ≠ 0 := by exact_mod_cast hL.ne'
  simp only [gridTime, Nat.add_sub_cancel]
  push_cast
  field_simp

theorem exists_gridCeil_eq {L : ℕ} (hL : 0 < L) {r : ℝ≥0∞} (hr : r ≤ h) :
    ∃ i, i ≤ L ∧ gridCeil h L r = gridTime h L i := by
  rcases exists_grid_index hL hr with h0 | ⟨i, hi1, hiL, hlt, hle⟩
  · refine ⟨0, Nat.zero_le _, le_antisymm ?_ ?_⟩
    · exact iInf_le_of_le ⟨0, by omega⟩ (iInf_le_of_le (by
        rw [gridTime_zero]; simpa using h0) (by simp [gridTime_zero]))
    · rw [gridTime_zero]; simp
  · exact ⟨i, hiL, gridCeil_eq hL hi1 hiL hlt hle⟩

theorem gridCeil_le_add {L : ℕ} (hL : 0 < L) {r : ℝ≥0∞} (hr : r ≤ h) :
    gridCeil h L r ≤ r + ((h / L : ℝ≥0) : ℝ≥0∞) := by
  rcases exists_grid_index hL hr with h0 | ⟨i, hi1, hiL, hlt, hle⟩
  · have : gridCeil h L r ≤ 0 := by
      refine iInf_le_of_le ⟨0, by omega⟩ (iInf_le_of_le (by
        rw [gridTime_zero]; simpa using h0) (by simp [gridTime_zero]))
    exact this.trans zero_le
  · rw [gridCeil_eq hL hi1 hiL hlt hle, gridTime_succ_sub hL hi1]
    push_cast
    exact add_le_add_left hlt.le _

theorem gridCeil_double_le (L : ℕ) (r : ℝ≥0∞) : gridCeil h (2 * L) r ≤ gridCeil h L r := by
  refine le_iInf fun i => le_iInf fun hi => ?_
  have e : gridTime h L i = gridTime h (2 * L) (2 * i) := by
    unfold gridTime
    push_cast
    rcases Nat.eq_zero_or_pos L with rfl | hL
    · simp
    · have : (L : ℝ≥0) ≠ 0 := by exact_mod_cast hL.ne'
      field_simp
  refine iInf_le_of_le ⟨2 * i, by have := i.2; omega⟩ (iInf_le_of_le ?_ ?_)
  · rw [← e]; exact hi
  · rw [← e]

theorem gridCeil_dyadic_anti (r : ℝ≥0∞) : Antitone fun n : ℕ => gridCeil h (2 ^ n) r :=
  antitone_nat_of_succ_le fun n => by
    simpa [pow_succ, mul_comm] using gridCeil_double_le (h := h) (2 ^ n) r

end ElboimSly

/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Paper.Step.ZetaCouple
public import Mathlib

/-!
# `thit` of the globally shifted piece is at least `s₀ + thit` of the piece

ES22 Lemma 7.1, Step 4 (`\\tilde\\tau_{\\rm hit}(t) = s_1 + \\tau_{\\rm hit}^{Z_2}(t - s_1)`).
-/

@[expose] public section

open MeasureTheory Set ElboimSly.Cyclic
open scoped ENNReal NNReal

namespace ElboimSly.Paper.Step

open ElboimSly.Paper

variable {d : ℕ}

theorem stepThit_shift_ge {β : ℝ} [Fact (0 < β)] {y : ℝ≥0 → Fin d → ℤ} (s₀ t : ℝ≥0)
    (hts : s₀ ≤ t) :
    (s₀ : ℝ≥0∞) + stepThit β (stepExt fun s => stepReg β y s)
        (fun r => (stepAlpha β y r.toNNReal : ℝ)) ((t : ℝ) - s₀) ≤
      stepThit β (stepExt fun s => stepReg β y (s - s₀))
        (fun r => ((shiftAlpha s₀ (stepAlpha β y) r.toNNReal : ℝ≥0) : ℝ)) (t : ℝ) := by
  unfold stepThit
  refine le_iInf₂ fun s hs => ?_
  obtain ⟨hts', s', ⟨k, hk⟩, hα, hlt, hn⟩ := hs
  have hs0 : (s₀ : ℝ) ≤ s := by linarith [(by exact_mod_cast hts : (s₀ : ℝ) ≤ t)]
  have hα2 : (stepAlpha β y ((t : ℝ) - s₀).toNNReal : ℝ) < s' - s₀ := by
    have h1 : ((shiftAlpha s₀ (stepAlpha β y) (t : ℝ).toNNReal : ℝ≥0) : ℝ) =
        s₀ + (stepAlpha β y ((t : ℝ) - s₀).toNNReal : ℝ) := by
      simp only [shiftAlpha, Real.toNNReal_coe, not_lt.2 hts, ite_false]
      push_cast
      rw [← toNNReal_sub_nn, Real.toNNReal_coe]
    have := hα
    simp only at this
    rw [h1] at this
    linarith
  have hn2 : ‖stepExt (fun s => stepReg β y s) (s - s₀) -
      stepExt (fun s => stepReg β y s) (s' - s₀)‖ ≤ 1 := by
    simpa only [stepExt, toNNReal_sub_nn] using hn
  have h1 := stepThit_le_of_mem (β := β) (w := stepExt fun s => stepReg β y s)
    (α := fun r => (stepAlpha β y r.toNNReal : ℝ)) (t := (t : ℝ) - s₀) (s := s - s₀)
    (s' := s' - s₀) (k := k) (by linarith) (by rw [hk]; ring) hα2 (by linarith) hn2
  calc (s₀ : ℝ≥0∞) + stepThit β (stepExt fun s => stepReg β y s)
        (fun r => (stepAlpha β y r.toNNReal : ℝ)) ((t : ℝ) - s₀)
      ≤ (s₀ : ℝ≥0∞) + ENNReal.ofReal (s - s₀) := add_le_add le_rfl h1
    _ = ENNReal.ofReal s := by
      rw [← ENNReal.ofReal_coe_nnreal, ← ENNReal.ofReal_add (NNReal.coe_nonneg _) (by linarith)]
      congr 1; ring

end ElboimSly.Paper.Step

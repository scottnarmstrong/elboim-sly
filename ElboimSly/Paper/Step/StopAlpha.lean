/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Paper.Step.DrivenSigma
public import Mathlib

/-!
# `α(t)` is the last lattice zero of the driven walk

The driven regenerated walk (d): the regeneration times of `W = W_reg^x` are exactly the
`r ∈ βℤ_{≥0}` with `W(r) = 0`. So `α(t) = max {m β ≤ t : W(mβ) = 0}`.
-/

@[expose] public section

open MeasureTheory Set ElboimSly.Cyclic
open scoped ENNReal NNReal

namespace ElboimSly.Paper.Step

open ElboimSly.Paper

variable {d : ℕ}

theorem stepAlpha_spec {β : ℝ} [Fact (0 < β)] {x : ℝ≥0 → Fin d → ℤ} (hx : x ∈ StepPath d)
    (t : ℝ≥0) :
    (∃ m : ℕ, stepAlpha β x t = (m : ℝ≥0) * β.toNNReal ∧ (m : ℝ≥0) * β.toNNReal ≤ t ∧
      stepReg β x ((m : ℝ≥0) * β.toNNReal) = 0) ∧
    ∀ m : ℕ, (m : ℝ≥0) * β.toNNReal ≤ t → stepReg β x ((m : ℝ≥0) * β.toNNReal) = 0 →
      (m : ℝ≥0) * β.toNNReal ≤ stepAlpha β x t := by
  have hb : 0 < β.toNNReal := toNNReal_pos'
  obtain ⟨hN1, hN2⟩ := gluedCount_spec' hb x t
  set N := gluedCount (drivenSigma β.toNNReal x) t with hN
  have hα : stepAlpha β x t = (drivenSigma β.toNNReal x N).toNNReal := rfl
  have hfin : drivenSigma β.toNNReal x N < ⊤ := lt_of_le_of_lt hN1 ENNReal.coe_lt_top
  have hcoe : drivenSigma β.toNNReal x N = ((drivenSigma β.toNNReal x N).toNNReal : ℝ≥0∞) :=
    (ENNReal.coe_toNNReal hfin.ne).symm
  refine ⟨?_, fun m hmt hmz => ?_⟩
  · cases hNe : N with
    | zero =>
      refine ⟨0, ?_, by simp, ?_⟩
      · rw [hα, hNe, drivenSigma_zero]; simp
      · simp only [Nat.cast_zero, zero_mul]
        exact drivenRegenFrom_zero hb hx.toIsRegPath
    | succ n =>
      rw [hNe] at hfin hcoe hN1
      rcases drivenSigma_top_or β.toNNReal x (n + 1) with h | ⟨m, hm⟩
      · exact absurd h hfin.ne
      · refine ⟨m, ?_, ?_, ?_⟩
        · rw [hα, hNe, hm, ENNReal.toNNReal_coe]
        · have := hm ▸ hN1
          exact_mod_cast this
        · exact drivenRegenFrom_sigma hb hx.toIsRegPath (n := n) (s := (m : ℝ≥0) * β.toNNReal)
            (by rw [hm])
  · rw [hα]
    by_cases hle : (((m : ℝ≥0) * β.toNNReal : ℝ≥0) : ℝ≥0∞) ≤ drivenSigma β.toNNReal x N
    · rw [hcoe] at hle
      exact_mod_cast hle
    · exfalso
      rw [not_le] at hle
      have hmem : ((m : ℝ≥0) * β.toNNReal) ∈ {r : ℝ≥0 | (∃ k : ℕ, r = (k : ℝ≥0) * β.toNNReal) ∧
          stepSigma β x N < r ∧ stepReg β x r = 0} := ⟨⟨m, rfl⟩, hle, hmz⟩
      have h1 := stepSigma_succ_eq_iInf (β := β) hx N
      have h2 : stepSigma β x (N + 1) ≤ (((m : ℝ≥0) * β.toNNReal : ℝ≥0) : ℝ≥0∞) := by
        rw [h1]
        exact iInf₂_le _ hmem
      have h3 : drivenSigma β.toNNReal x (N + 1) ≤ (t : ℝ≥0∞) :=
        h2.trans (by exact_mod_cast hmt)
      exact absurd hN2 (not_lt.2 h3)

end ElboimSly.Paper.Step

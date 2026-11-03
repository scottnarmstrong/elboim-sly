/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Paper.Step.RelaxedStructure
public import ElboimSly.Paper.Step.RegenPath
public import ElboimSly.Paper.Step.RelaxedAdapted
public import ElboimSly.Paper.Avoid.CoreHit
public import ElboimSly.Foundations.Cyclic.CycHitCoupleDrivenRegen
public import Mathlib

/-!
# `thit` and the shifted walk: the pathwise inclusion of ES22 Lemma 4.1

ES22 Lemma 4.1 (inclusion step).

For a coincidence-free driving path `x`, `W = W_reg^x`, a time `t` that is relaxed, and
`W' = W_reg^{θ_t x}`: if `τ' ≥ 4ⁿ` (the hitting time of ES22 Lemma 4.1 for the history of `W` up
to `t` and the walk `W(t) + W'`), then `thit(t) ≥ t + 4ⁿ`.
-/

@[expose] public section

open MeasureTheory Set Filter Topology ElboimSly.Cyclic
open scoped ENNReal NNReal

namespace ElboimSly.Paper.Step

open ElboimSly.Paper

variable {d : ℕ}

/-- A right-continuous path extended by `g(0)` to the negative reals is locally constant on the
right. -/
theorem exists_Ico_const_stepExt {g : ℝ≥0 → Fin d → ℤ}
    (hg : ∀ s, ∀ᶠ u in 𝓝[≥] s, g u = g s) (r : ℝ) :
    ∃ ε > 0, ∀ r' ∈ Ico r (r + ε), g r'.toNNReal = g r.toNNReal := by
  rcases lt_or_ge r 0 with hr | hr
  · refine ⟨-r, by linarith, fun r' hr' => ?_⟩
    have h1 : r' < 0 := by linarith [hr'.2]
    simp [Real.toNNReal_of_nonpos hr.le, Real.toNNReal_of_nonpos h1.le]
  · obtain ⟨u, hu, hsub⟩ := mem_nhdsGE_iff_exists_Ico_subset.1 (hg r.toNNReal)
    refine ⟨(u : ℝ) - r, ?_, fun r' hr' => ?_⟩
    · have : r.toNNReal < u := hu
      have h2 : r < (u : ℝ) := by
        rw [← Real.coe_toNNReal r hr]; exact_mod_cast this
      linarith
    · have hr'0 : 0 ≤ r' := le_trans hr hr'.1
      have h3 := hsub ⟨(Real.toNNReal_le_toNNReal hr'.1), by
        rw [← NNReal.coe_lt_coe, Real.coe_toNNReal _ hr'0]; linarith [hr'.2]⟩
      exact h3

/-- `thit` for the real-time path is at most the `ℝ≥0`-version `drivenThit` used in the cyclic
chapter. -/
theorem stepThit_le_drivenThit {β : ℝ} [Fact (0 < β)] {x : ℝ≥0 → Fin d → ℤ} (t : ℝ≥0) :
    stepThit β (stepExt fun s => stepReg β x s)
        (fun r => (stepAlpha β x r.toNNReal : ℝ)) (t : ℝ) ≤
      drivenThit β.toNNReal x t := by
  have hβ : (β.toNNReal : ℝ) = β := Real.coe_toNNReal _ (le_of_lt Fact.out)
  unfold drivenThit
  refine le_iInf₂ fun s hs => ?_
  obtain ⟨hts, k, s', hs', hα, hst, hnorm⟩ := hs
  have hmem : (s : ℝ) ∈ {s : ℝ | (t : ℝ) < s ∧ ∃ s'' : ℝ, (∃ k : ℤ, s'' = s + k * β) ∧
      (fun r : ℝ => (stepAlpha β x r.toNNReal : ℝ)) (t : ℝ) < s'' ∧ s'' < t ∧
      ‖stepExt (fun s => stepReg β x s) s - stepExt (fun s => stepReg β x s) s''‖ ≤ 1} := by
    refine ⟨by exact_mod_cast hts, (s' : ℝ), ⟨k, by rw [hs', hβ]⟩, ?_, by exact_mod_cast hst, ?_⟩
    · simp only [Real.toNNReal_coe]
      exact_mod_cast hα
    · simp only [stepExt, Real.toNNReal_coe]
      exact hnorm
  unfold stepThit
  refine iInf₂_le_of_le (s : ℝ) hmem ?_
  rw [ENNReal.ofReal_coe_nnreal]

end ElboimSly.Paper.Step

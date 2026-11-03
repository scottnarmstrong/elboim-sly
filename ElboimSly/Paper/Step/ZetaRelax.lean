/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Paper.Step.ZetaSRW
public import ElboimSly.Paper.Heavy.PiecesRegen
public import Mathlib

/-!
# Relaxed times of the globally shifted second piece

ES22 Lemma 7.1, Step 5.

For `x ≥ s₀`, `x ∈ 𝒯(w₂)` (the relaxed set of `t ↦ Z₂(t - s₀)`, with regeneration function
`shiftAlpha`) iff `x - s₀ ∈ 𝒯(Z₂)`. Consequently the windows of the two sets have equal measure
(`volume_relaxed_shift`).
-/

@[expose] public section

open MeasureTheory Set ElboimSly.Cyclic ElboimSly.SRW
open scoped ENNReal NNReal

namespace ElboimSly.Paper.Step

open ElboimSly.Paper

variable {d : ℕ} {Ω : Type*} {Y : Ω → PathSpace d}

theorem relaxed_shift_iff {β : ℝ} [Fact (0 < β)] (a s₀ : ℝ≥0) (ω : Ω) (hy : Y ω ∈ StepPath d)
    {x : ℝ} (hx : (s₀ : ℝ) ≤ x) :
    x ∈ stepRelaxedSetOf β (zw2 β a s₀ Y) (za2 β a s₀ Y) ω ↔
      x - s₀ ∈ stepRelaxedSet β (stepWr β (a + s₀) Y ω) (stepAr β (a + s₀) Y ω) := by
  have hx0 : 0 ≤ x := (NNReal.coe_nonneg _).trans hx
  have hxs : 0 ≤ x - s₀ := by linarith
  have hge : ¬ x.toNNReal < s₀ := by
    rw [not_lt, Real.le_toNNReal_iff_coe_le hx0]; exact hx
  obtain ⟨A', hA'⟩ : ∃ A' : ℝ, A' = (stepAlpha β (stepShift (a + s₀) (Y ω)) (x - s₀).toNNReal : ℝ) :=
    ⟨_, rfl⟩
  have hA'0 : 0 ≤ A' := by rw [hA']; exact NNReal.coe_nonneg _
  have hA'le : A' ≤ x - s₀ := by
    have := stepAlpha_le (β := β) (stepShift_mem hy (a + s₀)) (x - s₀).toNNReal
    have h2 : A' ≤ (((x - s₀).toNNReal : ℝ≥0) : ℝ) := by rw [hA']; exact_mod_cast this
    rwa [Real.coe_toNNReal _ hxs] at h2
  have eα : ((za2 β a s₀ Y x.toNNReal ω : ℝ≥0) : ℝ) = s₀ + A' := by
    simp only [za2, shiftAlpha, hge, ite_false]
    push_cast
    rw [toNNReal_sub_nn, hA']
  have eα2 : stepAr β (a + s₀) Y ω (x - s₀) = A' := by rw [hA']; rfl
  have hshift : ∀ u : ℝ, 0 ≤ u → stepExt (fun t => zw2 β a s₀ Y t ω) (s₀ + A' + u) =
      stepWr β (a + s₀) Y ω (A' + u) := by
    intro u hu
    simp only [stepExt, zw2, stepWr]
    rw [toNNReal_sub_nn]
    congr 2
    ring
  show (0 ≤ x ∧ IsRelaxedTimeWrt β (stepExt fun t => zw2 β a s₀ Y t ω)
      ((za2 β a s₀ Y x.toNNReal ω : ℝ≥0) : ℝ) x) ↔
    (0 ≤ x - s₀ ∧ IsRelaxedTimeWrt β (stepWr β (a + s₀) Y ω) (stepAr β (a + s₀) Y ω (x - s₀))
      (x - s₀))
  rw [eα, eα2]
  refine and_congr ⟨fun _ => hxs, fun _ => hx0⟩ ?_
  rw [isRelaxedTimeWrt_shift (β := β) (w' := fun u => stepWr β (a + s₀) Y ω (A' + u))
      (by linarith) (fun u hu _ => hshift u hu),
    isRelaxedTimeWrt_shift (β := β) (w' := fun u => stepWr β (a + s₀) Y ω (A' + u))
      hA'le (fun u _ _ => rfl)]
  have e : x - (s₀ + A') = x - s₀ - A' := by ring
  rw [e]

end ElboimSly.Paper.Step

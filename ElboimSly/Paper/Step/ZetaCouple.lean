/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Paper.Step.ZetaPath
public import ElboimSly.Paper.Step.ZetaSRW
public import ElboimSly.Paper.Step.StopHit
public import Mathlib

/-!
# Step 2 of Lemma 7.1: agreement of increments on `[ζ_i, ζ'_i]`

ES22 Lemma 7.1, Step 2; ES22 Lemma 2.1 (c).

* `stepThit_shift_le`: `thit` of the globally shifted second piece is at most `s₀ + drivenThit`;
* `incr_agree`: on `[t, min (thit₁, thit₂)]` the increments of `W` and of `W̃^∞ = W|_{[0,s₀]} ⌢ Z₂`
  agree.
-/

@[expose] public section

open MeasureTheory Set Filter Topology ElboimSly.Cyclic
open scoped ENNReal NNReal

namespace ElboimSly.Paper.Step

open ElboimSly.Paper

variable {d : ℕ}

theorem stepThit_le_of_mem {β : ℝ} {w : ℝ → Fin d → ℤ} {α : ℝ → ℝ} {t s s' : ℝ} {k : ℤ}
    (hts : t < s) (hk : s' = s + k * β) (hα : α t < s') (hst : s' < t)
    (hn : ‖w s - w s'‖ ≤ 1) : stepThit β w α t ≤ ENNReal.ofReal s := by
  unfold stepThit
  exact iInf₂_le_of_le s ⟨hts, s', ⟨k, hk⟩, hα, hst, hn⟩ le_rfl

/-- `thit` of the second piece on the global axis is at most `s₀ + drivenThit` (for `t ≥ s₀`). -/
theorem stepThit_shift_le {β : ℝ} [Fact (0 < β)] {y : ℝ≥0 → Fin d → ℤ} (s₀ t : ℝ≥0)
    (hts : s₀ ≤ t) :
    stepThit β (stepExt fun s => stepReg β y (s - s₀))
        (fun r => ((shiftAlpha s₀ (stepAlpha β y) r.toNNReal : ℝ≥0) : ℝ)) (t : ℝ) ≤
      (s₀ : ℝ≥0∞) + drivenThit β.toNNReal y (t - s₀) := by
  have hβ : (β.toNNReal : ℝ) = β := Real.coe_toNNReal _ (le_of_lt Fact.out)
  unfold drivenThit
  simp only [ENNReal.add_iInf]
  refine le_iInf₂ fun s2 hs2 => ?_
  obtain ⟨hts2, k, s2', hs2', hα, hlt, hnorm⟩ := hs2
  have hts' : (t : ℝ) - s₀ < s2 := by
    have : ((t - s₀ : ℝ≥0) : ℝ) < s2 := by exact_mod_cast hts2
    rwa [NNReal.coe_sub hts] at this
  have hlt' : (s2' : ℝ) < t - s₀ := by
    have : (s2' : ℝ) < ((t - s₀ : ℝ≥0) : ℝ) := by exact_mod_cast hlt
    rwa [NNReal.coe_sub hts] at this
  have hα' : (stepAlpha β y (t - s₀) : ℝ) < s2' := by exact_mod_cast hα
  have e1 : ((s₀ : ℝ) + s2).toNNReal - s₀ = s2 := by
    have : (s₀ : ℝ) + s2 = ((s₀ + s2 : ℝ≥0) : ℝ) := by push_cast; ring
    rw [this, Real.toNNReal_coe, add_tsub_cancel_left]
  have e2 : ((s₀ : ℝ) + s2').toNNReal - s₀ = s2' := by
    have : (s₀ : ℝ) + s2' = ((s₀ + s2' : ℝ≥0) : ℝ) := by push_cast; ring
    rw [this, Real.toNNReal_coe, add_tsub_cancel_left]
  have hk : (s₀ : ℝ) + s2' = ((s₀ : ℝ) + s2) + k * β := by
    have := hs2'
    rw [hβ] at this
    linarith
  have hal : ((shiftAlpha s₀ (stepAlpha β y) (t : ℝ).toNNReal : ℝ≥0) : ℝ) < (s₀ : ℝ) + s2' := by
    simp only [shiftAlpha, Real.toNNReal_coe, not_lt.2 hts, ite_false]
    push_cast
    linarith
  have hn : ‖stepExt (fun s => stepReg β y (s - s₀)) ((s₀ : ℝ) + s2) -
      stepExt (fun s => stepReg β y (s - s₀)) ((s₀ : ℝ) + s2')‖ ≤ 1 := by
    simp only [stepExt, e1, e2]
    exact hnorm
  have h1 := stepThit_le_of_mem (β := β) (w := stepExt fun s => stepReg β y (s - s₀))
    (α := fun r => ((shiftAlpha s₀ (stepAlpha β y) r.toNNReal : ℝ≥0) : ℝ)) (t := (t : ℝ))
    (s := (s₀ : ℝ) + s2) (s' := (s₀ : ℝ) + s2') (k := k) (by linarith) hk hal (by linarith) hn
  refine h1.trans ?_
  rw [ENNReal.ofReal_add (NNReal.coe_nonneg _) (NNReal.coe_nonneg _), ENNReal.ofReal_coe_nnreal,
    ENNReal.ofReal_coe_nnreal]

/-- **Step 2**: before `min (thit₁, thit₂)` the increments of `W` and of
`W̃^∞ = W|_{[0,s₀]} ⌢ Z₂` agree. -/
theorem incr_agree {β : ℝ} [Fact (0 < β)] {x : ℝ≥0 → Fin d → ℤ} (hx : x ∈ StepCF (d := d) β)
    {s₀ : ℝ≥0} (hx₁ : shiftPath x s₀ ∈ StepCF (d := d) β) {t : ℝ≥0} (hts : s₀ ≤ t) {r : ℝ≥0}
    (h1 : ((t + r : ℝ≥0) : ℝ≥0∞) ≤ stepThit β (stepExt fun s => stepReg β x s)
      (fun u => (stepAlpha β x u.toNNReal : ℝ)) (t : ℝ))
    (h2 : ((t + r : ℝ≥0) : ℝ≥0∞) ≤ stepThit β
      (stepExt fun s => stepReg β (shiftPath x s₀) (s - s₀))
      (fun u => ((shiftAlpha s₀ (stepAlpha β (shiftPath x s₀)) u.toNNReal : ℝ≥0) : ℝ)) (t : ℝ)) :
    stepReg β x (t + r) - stepReg β x t =
      stepCat s₀ (stepReg β x) (stepReg β (shiftPath x s₀)) (t + r) -
        stepCat s₀ (stepReg β x) (stepReg β (shiftPath x s₀)) t := by
  have hb : 0 < β.toNNReal := toNNReal_pos'
  have hs : ((t + r : ℝ≥0) : ℝ≥0∞) ≤ min (drivenThit β.toNNReal x t)
      ((s₀ : ℝ≥0∞) + drivenThit β.toNNReal (shiftPath x s₀) (t - s₀)) :=
    le_min (h1.trans (stepThit_le_drivenThit (β := β) (x := x) t))
      (h2.trans (stepThit_shift_le (β := β) s₀ t hts))
  exact (cyc_hit_couple_driven_regen_c hb hx hx₁ hts r hs).1

end ElboimSly.Paper.Step

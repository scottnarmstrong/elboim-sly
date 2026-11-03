/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Foundations.Brownian.Tube
import Mathlib

/-!
# Following a segment

Following a segment.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace ElboimSly.Brownian

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} {d : ℕ}
  {B : ℝ≥0 → Ω → (Fin d → ℝ)}

/-- The path `f(u) = x + min(u/T₁, 1)(g - x)` along the segment `[x, g]`. -/
noncomputable def segPath (x g : Fin d → ℝ) (T₁ : ℝ) (u : ℝ) : Fin d → ℝ :=
  x + min (u / T₁) 1 • (g - x)

lemma segPath_lip {x g : Fin d → ℝ} {T₁ ρ K : ℝ} (hT₁ : 0 < T₁) (hρ : 0 < ρ) (hK : 1 ≤ K)
    (hT₁K : ρ ^ 2 / K ≤ T₁) (hg : ‖g - x‖ ≤ K * ρ) (u v : ℝ) :
    ‖segPath x g T₁ u - segPath x g T₁ v‖ ≤ K ^ 2 / ρ * |u - v| := by
  have hK0 : 0 < K := by linarith
  have e : segPath x g T₁ u - segPath x g T₁ v =
      (min (u / T₁) 1 - min (v / T₁) 1) • (g - x) := by
    simp [segPath, sub_smul]
  rw [e, norm_smul, Real.norm_eq_abs]
  have h1 : |min (u / T₁) 1 - min (v / T₁) 1| ≤ |u / T₁ - v / T₁| := by
    have := abs_min_sub_min_le_max (u / T₁) 1 (v / T₁) 1
    simpa using this
  have h2 : |u / T₁ - v / T₁| = |u - v| / T₁ := by
    rw [← sub_div, abs_div, abs_of_pos hT₁]
  have h3 : 1 / T₁ ≤ K / ρ ^ 2 := by
    rw [div_le_div_iff₀ hT₁ (by positivity)]
    rw [div_le_iff₀ hK0] at hT₁K
    nlinarith
  calc |min (u / T₁) 1 - min (v / T₁) 1| * ‖g - x‖ ≤ (|u - v| / T₁) * (K * ρ) :=
        mul_le_mul (h1.trans h2.le) hg (norm_nonneg _) (by positivity)
    _ = |u - v| * (1 / T₁) * (K * ρ) := by ring
    _ ≤ |u - v| * (K / ρ ^ 2) * (K * ρ) := by gcongr
    _ = K ^ 2 / ρ * |u - v| := by field_simp

/-- Following a segment. -/
theorem segment_follow [IsProbabilityMeasure P] (hB : IsStandardBrownianMotion d B P) {K : ℝ}
    (hK : 1 ≤ K) {σ : ℝ} (hσ1 : 1 ≤ σ) (hσ2 : σ ≤ 2) {ρ : ℝ} (hρ : 0 < ρ) {T₁ : ℝ}
    {T₂ : ℝ≥0} (hT₁ : 0 < T₁) (hT₁₂ : T₁ ≤ T₂) (hT₁K : ρ ^ 2 / K ≤ T₁)
    (hT₂K : (T₂ : ℝ) ≤ K * ρ ^ 2) {x g : Fin d → ℝ} (hg : ‖g - x‖ ≤ K * ρ) :
    ENNReal.ofReal (ctube d (K ^ 2)) ≤
      P {ω | ∀ u : ℝ≥0, u ≤ T₂ → ‖x + σ • B u ω - segPath x g T₁ u‖ ≤ ρ} := by
  have hK0 : 0 < K := by linarith
  have hK2 : 1 ≤ K ^ 2 := by nlinarith
  have hres := tube_lemma_event (K := K ^ 2) hB hK2 hσ1 hσ2 hρ (T := T₂) (f := segPath x g T₁)
    (x := x) ?_ ?_ (fun u _ v _ => segPath_lip hT₁ hρ hK hT₁K hg u v) ?_
  · refine le_trans hres.2.2 (measure_mono ?_)
    exact fun ω hω => hω.1
  · have : ρ ^ 2 / K ≤ T₂ := hT₁K.trans (by exact_mod_cast hT₁₂)
    refine le_trans ?_ this
    rw [div_le_div_iff₀ (by positivity) hK0]
    nlinarith [sq_nonneg ρ, mul_pos hK0 hK0]
  · refine hT₂K.trans ?_
    nlinarith [sq_nonneg ρ, mul_pos hK0 hK0]
  · have : segPath x g T₁ 0 = x := by simp [segPath]
    rw [this, sub_self, norm_zero]
    positivity

end ElboimSly.Brownian

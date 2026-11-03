/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Paper.Avoid.Core1
public import Mathlib

/-!
# ES22 §4, Lemma 4.1 (core form): the hitting time and the pathwise inclusion

ES22 Lemma 4.1, "Inclusion".
-/

@[expose] public section

open Set
open scoped ENNReal NNReal

namespace ElboimSly.Paper

variable {d : ℕ}

/-- The hitting time `τ'` of ES22 Lemma 4.1:
`inf {r > 0 : ∃ s' ∈ (T + r + βℤ) ∩ (a, T), ‖W'(r) - w(s')‖ ≤ 1}`. -/
noncomputable def hitTime (β : ℝ) (w : ℝ → Fin d → ℤ) (a T : ℝ) (Wp : ℝ → Fin d → ℤ) : ℝ≥0∞ :=
  ⨅ r ∈ {r : ℝ | 0 < r ∧ ∃ s' : ℝ, (∃ k : ℤ, s' = T + r + k * β) ∧ a < s' ∧ s' < T ∧
    ‖Wp r - w s'‖ ≤ 1}, ENNReal.ofReal r

/-- Pathwise inclusion `Rel ∩ E₁ ∩ E₂ ⊆ {τ' ≥ 4ⁿ}`: a path `y` that avoids `A_w` and moves away by
`β^δ` after time `β^{3δ}` does not hit the history. -/
theorem no_hit {β b1 b3 : ℝ} (hβ : 0 < β) (hb3 : b3 ≤ β / 2) (hb1 : 2 < b1)
    {w : ℝ → Fin d → ℤ} {a T : ℝ} (hR2 : ∀ s : ℝ, a ≤ s → s ≤ T - b3 → b1 ≤ ‖w T - w s‖)
    {y : ℝ → Fin d → ℤ} {N4 : ℝ}
    (hE1 : ∀ r : ℝ, 0 ≤ r → r ≤ N4 → y r ∉ histSet (visitedSet w a T) (w T) (b1 / 2))
    (hE2 : ∀ r : ℝ, b3 ≤ r → r ≤ N4 → b1 ≤ ‖y r‖) :
    ENNReal.ofReal N4 ≤ hitTime β w a T (fun r => w T + y r) := by
  refine le_iInf₂ fun r hr => ?_
  obtain ⟨hr0, s', ⟨k, hk⟩, has, hsT, hle⟩ := hr
  by_cases hrN : N4 ≤ r
  · exact ENNReal.ofReal_le_ofReal hrN
  exfalso
  push Not at hrN
  have hv : w s' ∈ visitedSet w a T := ⟨s', ⟨has.le, hsT.le⟩, rfl⟩
  have hy1 : ‖y r‖ < b1 / 2 := by
    by_contra hcon
    push Not at hcon
    apply hE1 r hr0.le hrN.le
    refine ⟨hcon, w s', hv, ?_⟩
    have : y r + w T - w s' = w T + y r - w s' := by abel
    rw [this]; exact hle
  have hr3 : r < b3 := by
    by_contra hcon
    push Not at hcon
    have := hE2 r hcon hrN.le
    linarith
  have hk1 : k ≤ -1 := by
    by_contra hcon
    push Not at hcon
    have : (0 : ℝ) ≤ k := by exact_mod_cast hcon
    nlinarith
  have hkR : (k : ℝ) ≤ -1 := by exact_mod_cast hk1
  have hs' : s' ≤ T - b3 := by nlinarith
  have h2 := hR2 s' has.le hs'
  have h3 : ‖w T - w s'‖ ≤ ‖y r‖ + ‖w T + y r - w s'‖ := by
    calc ‖w T - w s'‖ = ‖(w T + y r - w s') - y r‖ := by congr 1; abel
      _ ≤ _ := (norm_sub_le _ _).trans_eq (add_comm _ _)
  linarith

end ElboimSly.Paper

end

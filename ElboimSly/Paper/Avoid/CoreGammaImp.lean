/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Paper.Avoid.CoreGamma
public import Mathlib

/-!
# ES22 §4, Lemma 4.1 (core form): the cylinder good event implies no hitting

ES22 Lemma 4.1, "Inclusion", for right-continuous history and continuation.
-/

@[expose] public section

open MeasureTheory Set
open scoped ENNReal NNReal

namespace ElboimSly.Paper

variable {d : ℕ}

/-- If `(u, y) ∈ Γ` for the recorded history `u = (h, T - a, w(T))` and right-continuous `h`, `y`,
then `y` does not hit the history before time `N4`. -/
theorem good_imp_nohit {β b1 b3 : ℝ} (hβ : 0 < β) (hb30 : 0 ≤ b3) (hb3 : b3 ≤ β / 2)
    (hb1 : 2 < b1) {w : ℝ → Fin d → ℤ} {a T : ℝ} (haT : a ≤ T)
    (hR2 : ∀ s : ℝ, a ≤ s → s ≤ T - b3 → b1 ≤ ‖w T - w s‖)
    (hh : IsRCPath (fun s : ℝ≥0 => w (min (a + s) T))) {y : ℝ≥0 → Fin d → ℤ}
    (hy : IsRCPath y) {N4 : ℝ} (hN4 : b3 ≤ N4)
    (hΓ : (((fun s : ℝ≥0 => w (min (a + s) T)), (T - a).toNNReal, w T), y) ∈
      cylGamma d (b1 / 2) b1 b3.toNNReal N4.toNNReal) :
    ENNReal.ofReal N4 ≤ hitTime β w a T (fun r => w T + y r.toNNReal) := by
  obtain ⟨hG1, hG2⟩ := hΓ
  dsimp only at hG1 hG2
  have hN40 : 0 ≤ N4 := hb30.trans hN4
  refine no_hit hβ hb3 hb1 hR2 (y := fun r => y r.toNNReal) ?_ ?_
  · intro r hr0 hrN hmem
    obtain ⟨hnorm, v, ⟨s, ⟨has, hsT⟩, rfl⟩, hv⟩ := hmem
    have hr' : r.toNNReal ≤ N4.toNNReal := Real.toNNReal_le_toNNReal hrN
    obtain ⟨q, hq, hqy⟩ := exists_qSet hy (bot_le : (0 : ℝ≥0) ≤ r.toNNReal) hr'
    set σ : ℝ≥0 := (s - a).toNNReal with hσ
    have hσR : (σ : ℝ) = s - a := Real.coe_toNNReal _ (by linarith)
    have hlR : (((T - a).toNNReal : ℝ≥0) : ℝ) = T - a := Real.coe_toNNReal _ (by linarith)
    have hσl : σ ≤ (T - a).toNNReal := by
      rw [← NNReal.coe_le_coe, hσR, hlR]; linarith
    obtain ⟨q', hq', hq'h⟩ := exists_qSet hh (bot_le : (0 : ℝ≥0) ≤ σ) hσl
    have hhσ : w (min (a + σ) T) = w s := by
      congr 1
      rw [hσR, show a + (s - a) = s by ring]
      exact min_eq_left hsT
    refine hG1 q hq ⟨by rw [hqy]; exact hnorm, ?_⟩
    rw [hqy]
    rcases hq' with ⟨-, hq'l, hq'r⟩ | hq'e
    · refine ⟨w s, Or.inr ⟨q', hq'r, hq'l, ?_⟩, hv⟩
      show w (min (a + q') T) = w s
      rw [← hhσ]; exact hq'h
    · refine ⟨w s, Or.inl ?_, hv⟩
      show w s = w T
      have e1 : w (min (a + q') T) = w s := by rw [← hhσ]; exact hq'h
      rw [hq'e] at e1
      have : min (a + (((T - a).toNNReal : ℝ≥0) : ℝ)) T = T := by
        rw [hlR]; simp
      rw [this] at e1
      exact e1.symm
  · intro r hr hrN
    have hr' : b3.toNNReal ≤ r.toNNReal := Real.toNNReal_le_toNNReal hr
    have hr'' : r.toNNReal ≤ N4.toNNReal := Real.toNNReal_le_toNNReal hrN
    obtain ⟨q, hq, hqy⟩ := exists_qSet hy hr' hr''
    have := hG2 q hq
    rwa [hqy] at this

end ElboimSly.Paper

end

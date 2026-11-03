/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Paper.Step.StepRegEvents
public import Mathlib

/-!
# The second piece of `W̃^∞` on the global time axis

ES22 Lemma 7.1, Step 0.

For a path `g` with regeneration function `αy` and an offset `s₀`, put
`g^{(s₀)}(t) = g(t - s₀)` and `α^{(s₀)}(t) = 0` for `t < s₀`, `s₀ + αy(t - s₀)` otherwise. Local event
finiteness is preserved (`stepEventsFiniteW_shift`).
-/

@[expose] public section

open MeasureTheory Set Filter Topology
open scoped ENNReal NNReal

namespace ElboimSly.Paper.Step

open ElboimSly.Paper

variable {d : ℕ}

/-- The regeneration function of the shifted piece. -/
noncomputable def shiftAlpha (s₀ : ℝ≥0) (αy : ℝ≥0 → ℝ≥0) (t : ℝ≥0) : ℝ≥0 :=
  if t < s₀ then 0 else s₀ + αy (t - s₀)

theorem toNNReal_sub_nn (r : ℝ) (s₀ : ℝ≥0) : r.toNNReal - s₀ = (r - s₀).toNNReal := by
  rcases le_total (s₀ : ℝ) r with h | h
  · have hle : s₀ ≤ r.toNNReal := (Real.le_toNNReal_iff_coe_le (le_trans (NNReal.coe_nonneg _) h)).2 h
    rw [← NNReal.coe_inj, NNReal.coe_sub hle,
      Real.coe_toNNReal _ ((NNReal.coe_nonneg _).trans h), Real.coe_toNNReal _ (by linarith)]
  · rw [tsub_eq_zero_of_le (Real.toNNReal_le_iff_le_coe.2 h),
      Real.toNNReal_of_nonpos (by linarith)]

theorem eventsW_shift {G : ℝ → Fin d → ℤ} {A : ℝ → ℝ} (h : StepEventsFiniteW G A)
    (hneg : ∀ a b : ℝ, a ≤ b → b ≤ 0 → G b = G a) (s₀ : ℝ≥0) :
    StepEventsFiniteW (fun r => G (r - s₀))
      (fun r => if r.toNNReal < s₀ then 0 else (s₀ : ℝ) + A (r - s₀)) := by
  classical
  refine ⟨fun e he => ?_, fun M => ?_⟩
  · by_cases hlt : e.toNNReal < s₀
    · simp [hlt, he]
    · simp only [hlt, ite_false]
      have hs : (s₀ : ℝ) ≤ e := by
        rw [not_lt, Real.le_toNNReal_iff_coe_le he] at hlt; exact hlt
      have h1 := h.1 (e - s₀) (by linarith)
      exact ⟨by linarith [h1.1, NNReal.coe_nonneg s₀], by linarith [h1.2]⟩
  · obtain ⟨E, h0, hpos, htop, hpiece⟩ := h.2 (M - s₀)
    refine ⟨insert 0 (E.image fun x => x + s₀), by simp, ?_, ?_, ?_⟩
    · intro x hx
      simp only [Finset.mem_insert, Finset.mem_image] at hx
      rcases hx with rfl | ⟨y, hy, rfl⟩
      · exact le_rfl
      · exact add_nonneg (hpos y hy) (NNReal.coe_nonneg _)
    · obtain ⟨x, hx, hMx⟩ := htop
      exact ⟨x + s₀, by simp only [Finset.mem_insert, Finset.mem_image]; exact Or.inr ⟨x, hx, rfl⟩,
        by linarith⟩
    · intro e he s hes hsM hno
      by_cases hmain : ∃ e0 ∈ E, e = e0 + s₀
      · obtain ⟨e0, he0, rfl⟩ := hmain
        have hs0 : (s₀ : ℝ) ≤ s := by linarith [hpos e0 he0]
        have hs0' : ¬ s.toNNReal < s₀ := by
          rw [not_lt, Real.le_toNNReal_iff_coe_le (by linarith [NNReal.coe_nonneg s₀])]; exact hs0
        have he0' : ¬ (e0 + s₀).toNNReal < s₀ := by
          rw [not_lt, Real.le_toNNReal_iff_coe_le (by linarith [hpos e0 he0, NNReal.coe_nonneg s₀])]
          linarith [hpos e0 he0]
        have hp := hpiece e0 he0 (s - s₀) (by linarith) (by linarith) fun x hx => by
          have := hno (x + s₀) (by
            simp only [Finset.mem_insert, Finset.mem_image]; exact Or.inr ⟨x, hx, rfl⟩)
          rcases this with h1 | h1
          · exact Or.inl (by linarith)
          · exact Or.inr (by linarith)
        refine ⟨?_, ?_⟩
        · simp only [add_sub_cancel_right]; exact hp.1
        · simp only [hs0', he0', ite_false, add_sub_cancel_right, hp.2]
      · have hes0 : e = 0 := by
          simp only [Finset.mem_insert, Finset.mem_image] at he
          rcases he with rfl | ⟨y, hy, rfl⟩
          · rfl
          · exact absurd ⟨y, hy, rfl⟩ hmain
        subst hes0
        have hs0pos : (0 : ℝ≥0) < s₀ := by
          by_contra hcon
          have h00 : s₀ = 0 := le_antisymm (not_lt.1 hcon) zero_le
          exact hmain ⟨0, h0, by simp [h00]⟩
        have hlt : s < s₀ := by
          have := hno s₀ (by
            simp only [Finset.mem_insert, Finset.mem_image]; exact Or.inr ⟨0, h0, by simp⟩)
          rcases this with h1 | h1
          · exact absurd h1 (not_le.2 (by exact_mod_cast hs0pos))
          · exact h1
        have h2 : (0 : ℝ).toNNReal < s₀ := by simpa using hs0pos
        have h3 : s.toNNReal < s₀ := (Real.toNNReal_lt_iff_lt_coe (by linarith)).2 hlt
        refine ⟨?_, by show (if s.toNNReal < s₀ then (0:ℝ) else _) = (if (0:ℝ).toNNReal < s₀ then (0:ℝ) else _); rw [ite_eq_left h3, ite_eq_left h2]⟩
        rcases le_total (s - s₀) (0 - s₀) with hh | hh
        · exact hneg (s - s₀) (0 - s₀) hh (by linarith) |>.symm
        · exact hneg (0 - s₀) (s - s₀) hh (by linarith)

end ElboimSly.Paper.Step

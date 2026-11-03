/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import Mathlib

/-!
# Averaging a window count

Supports ES22 Corollary 6.10 (the "Averaging" step).

For a measurable `T ⊆ ℝ`, `tk ≥ 0` and `a ≤ b`,
`∫_{[a, b]} |T ∩ [s - tk, s]| ds ≤ tk · |T ∩ [a - tk, b]|`  (Tonelli).
-/

@[expose] public section

open MeasureTheory Set
open scoped ENNReal

namespace ElboimSly.Paper

theorem lintegral_window_le {T : Set ℝ} (hT : MeasurableSet T) {tk a b : ℝ} (_htk : 0 ≤ tk) :
    ∫⁻ s in Icc a b, volume (T ∩ Icc (s - tk) s) ≤
      ENNReal.ofReal tk * volume (T ∩ Icc (a - tk) b) := by
  set P : Set (ℝ × ℝ) := {p | p.2 ∈ T ∧ p.1 - tk ≤ p.2 ∧ p.2 ≤ p.1} with hP
  have hPm : MeasurableSet P := by
    have h1 : MeasurableSet {p : ℝ × ℝ | p.2 ∈ T} := measurable_snd hT
    have h2 : MeasurableSet {p : ℝ × ℝ | p.1 - tk ≤ p.2} :=
      measurableSet_le (measurable_fst.sub_const _) measurable_snd
    have h3 : MeasurableSet {p : ℝ × ℝ | p.2 ≤ p.1} := measurableSet_le measurable_snd measurable_fst
    exact h1.inter (h2.inter h3)
  have hsec : ∀ s : ℝ, volume (T ∩ Icc (s - tk) s) = ∫⁻ x, P.indicator 1 (s, x) := by
    intro s
    have : (fun x => P.indicator (1 : ℝ × ℝ → ℝ≥0∞) (s, x)) =
        (T ∩ Icc (s - tk) s).indicator 1 := by
      funext x
      by_cases hx : x ∈ T ∩ Icc (s - tk) s
      · have hp : (s, x) ∈ P := ⟨hx.1, hx.2.1, hx.2.2⟩
        rw [indicator_of_mem hp, indicator_of_mem hx]
        rfl
      · have : (s, x) ∉ P := fun hp => hx ⟨hp.1, hp.2.1, hp.2.2⟩
        simp [indicator, this, hx]
    rw [this, lintegral_indicator_one (hT.inter measurableSet_Icc)]
  simp_rw [hsec]
  rw [lintegral_lintegral_swap (by
    exact (measurable_const.indicator hPm).aemeasurable)]
  calc ∫⁻ x, ∫⁻ s in Icc a b, P.indicator 1 (s, x)
      ≤ ∫⁻ x, (T ∩ Icc (a - tk) b).indicator (fun _ => ENNReal.ofReal tk) x := by
        refine lintegral_mono fun x => ?_
        by_cases hx : x ∈ T ∩ Icc (a - tk) b
        · rw [indicator_of_mem hx]
          calc ∫⁻ s in Icc a b, P.indicator 1 (s, x)
              ≤ ∫⁻ s in Icc x (x + tk), (1 : ℝ≥0∞) := by
                rw [← lintegral_indicator measurableSet_Icc,
                  ← lintegral_indicator measurableSet_Icc]
                refine lintegral_mono fun s => ?_
                by_cases hs1 : s ∈ Icc a b
                · by_cases hs2 : s ∈ Icc x (x + tk)
                  · rw [indicator_of_mem hs1, indicator_of_mem hs2]
                    by_cases hp : (s, x) ∈ P <;> simp [hp]
                  · have hp : (s, x) ∉ P := by
                      intro hp
                      exact hs2 ⟨hp.2.2, by linarith [hp.2.1]⟩
                    rw [indicator_of_mem hs1]
                    simp [hp]
                · rw [indicator_of_notMem hs1]
                  exact bot_le
            _ = ENNReal.ofReal tk := by simp
        · rw [indicator_of_notMem hx]
          have : ∀ s ∈ Icc a b, (s, x) ∉ P := by
            intro s hs hp
            apply hx
            exact ⟨hp.1, by linarith [hp.2.1, hs.1], by linarith [hp.2.2, hs.2]⟩
          have : ∫⁻ s in Icc a b, P.indicator 1 (s, x) = ∫⁻ s in Icc a b, 0 := by
            refine setLIntegral_congr_fun measurableSet_Icc fun s hs => ?_
            simp [indicator, this s hs]
          simp [this]
    _ = ENNReal.ofReal tk * volume (T ∩ Icc (a - tk) b) := by
        rw [lintegral_indicator (hT.inter measurableSet_Icc), setLIntegral_const]

end ElboimSly.Paper

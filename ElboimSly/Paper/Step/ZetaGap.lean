/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Paper.Step.ZetaPath
public import ElboimSly.Paper.Step.ZetaWindow
public import ElboimSly.Paper.Step.ZetaRelax
public import Mathlib

/-!
# Step 5 of Lemma 7.1: the gaps `ζ_{i+1} - ζ'_i` are at most `t_n^ε`

ES22 Lemma 7.1, Step 5.

`WinOK T h n S` is the event of ES22 Theorem 6.1: every window `[t, t + h] ⊆ [0, T]` carries measure at
least `(0.9 + 2/n) h` of `S`. If it holds for the relaxed sets of `W` and of `Z₂`, then on the
whole of `[s₀, T]`, `ζ_{i+1} ≤ ζ'_i + h` whenever `ζ'_i + h ≤ T` (`zetaN_le_of_window`).
-/

@[expose] public section

open MeasureTheory Set ElboimSly.SRW
open scoped ENNReal NNReal

namespace ElboimSly.Paper.Step

open ElboimSly.Paper

/-- The event of ES22 Theorem 6.1 for a set `S` of relaxed times. -/
def WinOK (T h : ℝ) (n : ℕ) (S : Set ℝ) : Prop :=
  ∀ t : ℝ, 0 ≤ t → t + h ≤ T →
    ENNReal.ofReal ((9 / 10 + 2 / (n : ℝ)) * h) ≤ volume (S ∩ Icc t (t + h))

variable {d : ℕ} {Ω : Type*} {m : MeasurableSpace Ω} {f : Filtration ℝ≥0 m} {β : ℝ}
  {w₁ w₂ : ℝ≥0 → Ω → Fin d → ℤ} {α₁ α₂ : ℝ≥0 → Ω → ℝ≥0}

theorem le_zetaP (hd : 1 ≤ d) (hβ : 1 < β) (h₁ : ZetaProc f w₁ α₁) (h₂ : ZetaProc f w₂ α₂)
    (s₀ : ℝ≥0) (i : ℕ) (ω : Ω) : (s₀ : WithTop ℝ≥0) ≤ zetaP β w₁ α₁ w₂ α₂ s₀ i ω := by
  induction i with
  | zero => exact le_rfl
  | succ i ih =>
    by_cases h : zetaN β w₁ α₁ w₂ α₂ s₀ i ω = ⊤
    · have : zetaP β w₁ α₁ w₂ α₂ s₀ (i + 1) ω = ⊤ := by
        show min (stepThitStop β w₁ α₁ (zetaN β w₁ α₁ w₂ α₂ s₀ i) ω : WithTop ℝ≥0)
          (stepThitStop β w₂ α₂ (zetaN β w₁ α₁ w₂ α₂ s₀ i) ω : WithTop ℝ≥0) = ⊤
        simp [stepThitStop, h]
      rw [this]; exact le_top
    · exact (ih.trans (zetaP_le_zetaN s₀ i ω)).trans
        (zetaN_lt_zetaP hd hβ h₁ h₂ s₀ i h).le

/-- If the windows of both relaxed sets are dense, `ζ_{i+1} ≤ ζ'_i + h`. -/
theorem zetaN_le_of_window (hd : 1 ≤ d) (hβ : 1 < β) (h₁ : ZetaProc f w₁ α₁)
    (h₂ : ZetaProc f w₂ α₂) (s₀ : ℝ≥0) (i : ℕ) (ω : Ω) {T h : ℝ} {n : ℕ} (hh : 0 < h)
    (hn : 1 ≤ n)
    (W₁ : WinOK T h n (stepRelaxedSetOf β w₁ α₁ ω))
    (W₂ : ∀ t : ℝ, (s₀ : ℝ) ≤ t → t + h ≤ T →
      ENNReal.ofReal ((9 / 10 + 2 / (n : ℝ)) * h) ≤
        volume (stepRelaxedSetOf β w₂ α₂ ω ∩ Icc t (t + h)))
    {t : ℝ≥0} (ht : zetaP β w₁ α₁ w₂ α₂ s₀ i ω = (t : WithTop ℝ≥0)) (htT : (t : ℝ) + h ≤ T) :
    zetaN β w₁ α₁ w₂ α₂ s₀ i ω ≤ ((t + h.toNNReal : ℝ≥0) : WithTop ℝ≥0) := by
  have hs0 : (s₀ : ℝ) ≤ t := by
    have := le_zetaP hd hβ h₁ h₂ s₀ i ω
    rw [ht] at this
    exact_mod_cast this
  have hq : (1 / 2 : ℝ) < 9 / 10 + 2 / (n : ℝ) := by
    have : (0 : ℝ) < 2 / (n : ℝ) := by
      have : (0 : ℝ) < n := by exact_mod_cast hn
      positivity
    linarith
  have hne := window_inter_nonempty (isLocIco_stepRelaxedSet' hd hβ (h₁.fin ω))
    (isLocIco_stepRelaxedSet' hd hβ (h₂.fin ω)) t.2 hh hq (W₁ t t.2 htT)
    (W₂ t hs0 htT)
  obtain ⟨u, ⟨hu1, hu2⟩, hu3, hu4⟩ := hne
  have hu0 : 0 ≤ u := t.2.trans hu3
  have hmemU : (u.toNNReal : ℝ) ∈ zetaU β w₁ α₁ w₂ α₂ ω := by
    rw [Real.coe_toNNReal _ hu0]; exact ⟨hu1, hu2⟩
  unfold zetaN
  refine (stepNextIn_le_iff (zetaU_loc hd hβ h₁ h₂ ω) _ _).2 ⟨u.toNNReal, hmemU, ?_, ?_⟩
  · rw [ht]
    exact WithTop.coe_le_coe.2 (Real.toNNReal_coe (r := t) ▸ Real.toNNReal_mono hu3)
  · rw [← NNReal.coe_le_coe]
    push_cast
    rw [Real.coe_toNNReal _ hu0, Real.coe_toNNReal _ hh.le]
    exact hu4

/-- Transfer of the window event from `Z₂` to the globally shifted piece. -/
theorem window_shift {β : ℝ} [Fact (0 < β)] {Y : Ω → PathSpace d} (a s₀ : ℝ≥0) (ω : Ω)
    (hy : Y ω ∈ StepPath d) {T h : ℝ} {n : ℕ}
    (W : WinOK T h n (stepRelaxedSet β (stepWr β (a + s₀) Y ω) (stepAr β (a + s₀) Y ω))) :
    ∀ t : ℝ, (s₀ : ℝ) ≤ t → t + h ≤ T →
      ENNReal.ofReal ((9 / 10 + 2 / (n : ℝ)) * h) ≤
        volume (stepRelaxedSetOf β (zw2 β a s₀ Y) (za2 β a s₀ Y) ω ∩ Icc t (t + h)) := by
  intro t hts htT
  have h0 : 0 ≤ t - s₀ := by linarith
  have hW := W (t - s₀) h0 (by linarith)
  refine hW.trans ?_
  rw [← measure_preimage_add_right volume (s₀ : ℝ)
    (stepRelaxedSetOf β (zw2 β a s₀ Y) (za2 β a s₀ Y) ω ∩ Icc t (t + h))]
  refine measure_mono fun x hx => ?_
  obtain ⟨hxR, hx1, hx2⟩ := hx
  refine ⟨?_, ?_, ?_⟩
  · have := (relaxed_shift_iff (β := β) a s₀ ω hy (x := x + s₀) (by linarith [hx1, h0])).2
    rw [add_sub_cancel_right] at this
    exact this hxR
  · show t ≤ x + s₀
    linarith
  · show x + s₀ ≤ t + h
    linarith

end ElboimSly.Paper.Step

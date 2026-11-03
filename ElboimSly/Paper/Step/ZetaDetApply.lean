/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Paper.Step.ZetaDet
public import ElboimSly.Paper.Step.ZetaGap
public import ElboimSly.Paper.Step.ZetaCouple
public import ElboimSly.Paper.Step.ZetaCount
public import ElboimSly.Paper.Step.FastDisp
public import ElboimSly.Paper.Step.Trunc
public import Mathlib

/-!
# The pathwise argument of Lemma 7.1

ES22 Lemma 7.1, Steps 2, 3, 5, 6.

On the complement of the bad events (`ζ_{n³+1} ≤ t_n`, a failure of the window event for `W` or
`Z₂`, `τ_fast ≤ t_n` for `W` or `Z₂`, a non-coincidence-free driver) one has
`‖W(u) - W̃(u)‖ ≤ 2 (n³ + 1) n³ (t_n^ε + 1)` for all `u ≤ t_n`.
-/

@[expose] public section

open MeasureTheory Set ElboimSly.Cyclic ElboimSly.SRW
open scoped ENNReal NNReal

namespace ElboimSly.Paper.Step

open ElboimSly.Paper

variable {d : ℕ}

/-- `(4ⁿ)`-free chain facts: `ζ_{i+1} ≤ ζ'_{i+1}` always. -/
theorem zetaN_le_zetaP_succ {Ω : Type*} {m : MeasurableSpace Ω} {f : Filtration ℝ≥0 m} {β : ℝ}
    {w₁ w₂ : ℝ≥0 → Ω → Fin d → ℤ} {α₁ α₂ : ℝ≥0 → Ω → ℝ≥0} (hd : 1 ≤ d) (hβ : 1 < β)
    (h₁ : ZetaProc f w₁ α₁) (h₂ : ZetaProc f w₂ α₂) (s₀ : ℝ≥0) (i : ℕ) (ω : Ω) :
    zetaN β w₁ α₁ w₂ α₂ s₀ i ω ≤ zetaP β w₁ α₁ w₂ α₂ s₀ (i + 1) ω := by
  by_cases h : zetaN β w₁ α₁ w₂ α₂ s₀ i ω = ⊤
  · have : zetaP β w₁ α₁ w₂ α₂ s₀ (i + 1) ω = ⊤ := by
      show min (stepThitStop β w₁ α₁ (zetaN β w₁ α₁ w₂ α₂ s₀ i) ω : WithTop ℝ≥0)
        (stepThitStop β w₂ α₂ (zetaN β w₁ α₁ w₂ α₂ s₀ i) ω : WithTop ℝ≥0) = ⊤
      simp [stepThitStop, h]
    rw [this]; exact le_top
  · exact (zetaN_lt_zetaP hd hβ h₁ h₂ s₀ i h).le

/-- The gaps `ζ_{i+1} - ζ'_i`, truncated at `T`, are at most `h`. -/
theorem zeta_gap_trunc {Ω : Type*} {m : MeasurableSpace Ω} {f : Filtration ℝ≥0 m} {β : ℝ}
    {w₁ w₂ : ℝ≥0 → Ω → Fin d → ℤ} {α₁ α₂ : ℝ≥0 → Ω → ℝ≥0} (hd : 1 ≤ d) (hβ : 1 < β)
    (h₁ : ZetaProc f w₁ α₁) (h₂ : ZetaProc f w₂ α₂) (s₀ : ℝ≥0) (i : ℕ) (ω : Ω) {T : ℝ≥0}
    {h : ℝ} {n : ℕ} (hh : 0 < h) (hn : 1 ≤ n)
    (W₁ : WinOK (T : ℝ) h n (stepRelaxedSetOf β w₁ α₁ ω))
    (W₂ : ∀ t : ℝ, (s₀ : ℝ) ≤ t → t + h ≤ (T : ℝ) →
      ENNReal.ofReal ((9 / 10 + 2 / (n : ℝ)) * h) ≤
        volume (stepRelaxedSetOf β w₂ α₂ ω ∩ Icc t (t + h))) :
    (trT T (zetaN β w₁ α₁ w₂ α₂ s₀ i ω) : ℝ) - trT T (zetaP β w₁ α₁ w₂ α₂ s₀ i ω) ≤ h := by
  have hzn : (trT T (zetaN β w₁ α₁ w₂ α₂ s₀ i ω) : ℝ) ≤ T := by exact_mod_cast trT_le _ _
  by_cases hP : zetaP β w₁ α₁ w₂ α₂ s₀ i ω = ⊤
  · rw [hP, trT_top]; linarith
  obtain ⟨t, ht⟩ := WithTop.ne_top_iff_exists.1 hP
  by_cases htT : (t : ℝ) + h ≤ T
  · have hle := zetaN_le_of_window hd hβ h₁ h₂ s₀ i ω hh hn W₁ W₂ ht.symm htT
    have htT' : t ≤ T := by
      have : (t : ℝ) ≤ T := by linarith
      exact_mod_cast this
    have e1 : trT T (zetaP β w₁ α₁ w₂ α₂ s₀ i ω) = t := trT_eq_of_le ht.symm htT'
    have e2 := trT_mono T hle
    rw [trT_coe] at e2
    rw [e1]
    have : ((min (t + h.toNNReal) T : ℝ≥0) : ℝ) ≤ (t : ℝ) + h := by
      have h3 : min (t + h.toNNReal) T ≤ t + h.toNNReal := min_le_left _ _
      have h4 : ((t + h.toNNReal : ℝ≥0) : ℝ) = t + h := by
        push_cast; rw [Real.coe_toNNReal _ hh.le]
      calc ((min (t + h.toNNReal) T : ℝ≥0) : ℝ) ≤ ((t + h.toNNReal : ℝ≥0) : ℝ) := by
            exact_mod_cast h3
        _ = t + h := h4
    have h5 : (trT T (zetaN β w₁ α₁ w₂ α₂ s₀ i ω) : ℝ) ≤ ((min (t + h.toNNReal) T : ℝ≥0) : ℝ) := by
      exact_mod_cast e2
    linarith
  · rw [not_le] at htT
    by_cases htT2 : T ≤ t
    · rw [← ht, trT_coe, min_eq_right htT2]
      linarith
    · rw [not_le] at htT2
      rw [← ht, trT_coe, min_eq_left htT2.le]
      linarith

end ElboimSly.Paper.Step

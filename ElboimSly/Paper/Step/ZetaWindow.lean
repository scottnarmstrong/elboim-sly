/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Paper.Step.LocIco
public import Mathlib

/-!
# Two dense relaxed sets meet in every window

ES22 Lemma 7.1, Step 5 ("hence `|𝒯 ∩ 𝒯̃ ∩ [t, t + t_n^ε]| > 0`").

If `S₁`, `S₂` are locally of type `[l, r)` and each has Lebesgue measure at least
`(0.9 + 2/n) h` in the window `[t, t + h]`, then `S₁ ∩ S₂` meets the window.
-/

@[expose] public section

open MeasureTheory Set
open scoped ENNReal

namespace ElboimSly.Paper.Step

open ElboimSly.Paper

theorem measurableSet_locIco_inter_Icc {S : Set ℝ} (hS : IsLocIco S) {a b : ℝ} (ha : 0 ≤ a) :
    MeasurableSet (S ∩ Icc a b) := by
  obtain ⟨L, -, hL⟩ := hS b
  have h1 : MeasurableSet (S ∩ Icc 0 b) := by
    rw [hL]
    exact (Finset.measurableSet_biUnion L fun p _ => measurableSet_Ico).inter measurableSet_Icc
  have : S ∩ Icc a b = (S ∩ Icc 0 b) ∩ Icc a b := by
    ext x
    simp only [mem_inter_iff, mem_Icc]
    constructor
    · rintro ⟨hx, h2, h3⟩; exact ⟨⟨hx, ha.trans h2, h3⟩, h2, h3⟩
    · rintro ⟨⟨hx, -, -⟩, h2, h3⟩; exact ⟨hx, h2, h3⟩
  rw [this]
  exact h1.inter measurableSet_Icc

theorem window_inter_nonempty {S₁ S₂ : Set ℝ} (h₁ : IsLocIco S₁) (h₂ : IsLocIco S₂) {t h q : ℝ}
    (ht : 0 ≤ t) (hh : 0 < h) (hq : 1 / 2 < q)
    (m₁ : ENNReal.ofReal (q * h) ≤ volume (S₁ ∩ Icc t (t + h)))
    (m₂ : ENNReal.ofReal (q * h) ≤ volume (S₂ ∩ Icc t (t + h))) :
    (S₁ ∩ S₂ ∩ Icc t (t + h)).Nonempty := by
  by_contra hne
  rw [not_nonempty_iff_eq_empty] at hne
  have mA := measurableSet_locIco_inter_Icc h₁ (a := t) (b := t + h) ht
  have mB := measurableSet_locIco_inter_Icc h₂ (a := t) (b := t + h) ht
  have hinter : (S₁ ∩ Icc t (t + h)) ∩ (S₂ ∩ Icc t (t + h)) = ∅ := by
    rw [← hne]
    ext x
    simp only [mem_inter_iff]
    tauto
  have hu := measure_union_add_inter (μ := volume) (S₁ ∩ Icc t (t + h)) mB
  rw [hinter, measure_empty, add_zero] at hu
  have hJ : volume ((S₁ ∩ Icc t (t + h)) ∪ (S₂ ∩ Icc t (t + h))) ≤ ENNReal.ofReal h := by
    refine (measure_mono (t := Icc t (t + h)) ?_).trans (le_of_eq ?_)
    · exact union_subset inter_subset_right inter_subset_right
    · rw [Real.volume_Icc]; congr 1; ring
  have h3 : ENNReal.ofReal (q * h) + ENNReal.ofReal (q * h) ≤ ENNReal.ofReal h := by
    calc ENNReal.ofReal (q * h) + ENNReal.ofReal (q * h)
        ≤ volume (S₁ ∩ Icc t (t + h)) + volume (S₂ ∩ Icc t (t + h)) := add_le_add m₁ m₂
      _ = _ := hu.symm
      _ ≤ ENNReal.ofReal h := hJ
  rw [← ENNReal.ofReal_add (by nlinarith) (by nlinarith)] at h3
  have := (ENNReal.ofReal_le_ofReal_iff hh.le).1 h3
  nlinarith

end ElboimSly.Paper.Step

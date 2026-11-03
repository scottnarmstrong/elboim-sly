/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import Mathlib

/-!
# Covering `[0, T]` by windows

The induction step, (H1): cover `[0, t_n]` by the disjoint windows `[jL, (j+1)L)`.

`window_cover`: if every window `[t, t + L] ⊆ [0, T]` carries measure at least `a L` of a set `S`,
then `S ∩ [0, T]` has measure at least `a (T - L)`. (No measurability of `S` is assumed.)
-/

@[expose] public section

open MeasureTheory Set
open scoped ENNReal

namespace ElboimSly.Paper.Step

theorem window_cover_nat (S : Set ℝ) {L a : ℝ} (hL : 0 < L) (ha : 0 ≤ a) {T : ℝ}
    (hwin : ∀ t : ℝ, 0 ≤ t → t + L ≤ T → ENNReal.ofReal (a * L) ≤ volume (S ∩ Icc t (t + L))) :
    ∀ k : ℕ, (k : ℝ) * L ≤ T →
      ENNReal.ofReal (a * L * k) ≤ volume (S ∩ Icc 0 (k * L)) := by
  intro k
  induction k with
  | zero => intro _; simp
  | succ k ih =>
    intro hk
    push_cast at hk ⊢
    have hk' : (k : ℝ) * L ≤ T := by nlinarith
    have h1 := ih hk'
    have h2 := hwin (k * L) (by positivity) (by nlinarith)
    have hmeas : MeasurableSet (Icc (0 : ℝ) (k * L)) := measurableSet_Icc
    have hsplit := measure_inter_add_sdiff (μ := volume) (S ∩ Icc 0 ((k + 1) * L)) hmeas
    have e1 : S ∩ Icc 0 ((k + 1) * L) ∩ Icc 0 (k * L) = S ∩ Icc 0 (k * L) := by
      ext x; simp only [mem_inter_iff, mem_Icc]
      constructor
      · rintro ⟨⟨a, -⟩, b⟩; exact ⟨a, b⟩
      · rintro ⟨a, b⟩; exact ⟨⟨a, b.1, by nlinarith [b.2]⟩, b⟩
    have e2 : S ∩ Icc (k * L) (k * L + L) ⊆
        (SDiff.sdiff (S ∩ Icc 0 ((k + 1) * L)) (Icc 0 (k * L))) ∪ {(k : ℝ) * L} := by
      intro x hx
      simp only [mem_inter_iff, mem_Icc, mem_union, mem_sdiff, mem_singleton_iff] at hx ⊢
      by_cases hxe : x = k * L
      · exact Or.inr hxe
      · refine Or.inl ⟨⟨hx.1, ?_, by nlinarith [hx.2.2]⟩, ?_⟩
        · have : 0 ≤ (k : ℝ) * L := by positivity
          linarith [hx.2.1]
        · rintro ⟨-, h⟩
          exact hxe (le_antisymm h hx.2.1)
    have h3 : volume (S ∩ Icc (k * L) (k * L + L)) ≤
        volume (SDiff.sdiff (S ∩ Icc 0 ((k + 1) * L)) (Icc 0 (k * L))) := by
      refine (measure_mono e2).trans ((measure_union_le _ _).trans ?_)
      simp
    rw [e1] at hsplit
    have h4 : ENNReal.ofReal (a * L * k) + ENNReal.ofReal (a * L) ≤
        volume (S ∩ Icc 0 ((k + 1) * L)) := by
      rw [← hsplit]; exact add_le_add h1 (h2.trans h3)
    rw [← ENNReal.ofReal_add (by positivity) (by positivity)] at h4
    convert h4 using 2; ring

theorem window_cover (S : Set ℝ) {L a T : ℝ} (hL : 0 < L) (ha : 0 ≤ a) (hT : 0 ≤ T)
    (hwin : ∀ t : ℝ, 0 ≤ t → t + L ≤ T → ENNReal.ofReal (a * L) ≤ volume (S ∩ Icc t (t + L))) :
    ENNReal.ofReal (a * (T - L)) ≤ volume (S ∩ Icc 0 T) := by
  set m := ⌊T / L⌋₊ with hm
  have h1 : (m : ℝ) ≤ T / L := Nat.floor_le (by positivity)
  have h2 : T / L < m + 1 := Nat.lt_floor_add_one _
  have h1' : (m : ℝ) * L ≤ T := by rwa [le_div_iff₀ hL] at h1
  have h2' : T < (m + 1) * L := by rwa [div_lt_iff₀ hL] at h2
  have := window_cover_nat S hL ha hwin m h1'
  refine le_trans (ENNReal.ofReal_le_ofReal ?_) (this.trans (measure_mono ?_))
  · nlinarith
  · intro x hx; exact ⟨hx.1, hx.2.1, hx.2.2.trans h1'⟩

end ElboimSly.Paper.Step

end

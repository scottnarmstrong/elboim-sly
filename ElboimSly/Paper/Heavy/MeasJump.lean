/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Paper.Heavy.MeasStop
public import ElboimSly.Paper.Heavy.JumpEvents
public import ElboimSly.Paper.Heavy.Attained
public import ElboimSly.Paper.Heavy.BadClosed

/-!
# `τ_jump` is a stopping time

Measurability (c).

* `rationalTimes T`: the set `{T} ∪ (ℚ ∩ (0, T))` (just `ℚ ∩ (0, T)` when `T = 0`).
* `pathTjump_le_iff_rational`: `τ_jump ≤ T` iff the jump count of the unit window ending at some
  `t ∈ rationalTimes T` is `≥ L`.  (Shifting the window by a small amount changes neither the jumps
  inside it nor the right-continuity data.)
* `AdaptedCyclic.isStoppingTime_pathTjump`.
-/

@[expose] public section

open MeasureTheory Set Filter Topology
open scoped ENNReal NNReal

namespace ElboimSly.Paper

open ElboimSly

variable {d : ℕ} {w : ℝ → Fin d → ℤ}

/-- `{T} ∪ (ℚ ∩ (0, T))`, the test times for `{τ ≤ T}` (without `T` if `T = 0`). -/
def rationalTimes (T : ℝ) : Set ℝ := {t | (0 < T ∧ t = T) ∨ ∃ q : ℚ, 0 < (q : ℝ) ∧ (q : ℝ) < T ∧ t = q}

theorem rationalTimes_countable (T : ℝ) : (rationalTimes T).Countable := by
  refine (((Set.countable_singleton T).union
    (Set.countable_range (fun q : ℚ => (q : ℝ)))).mono ?_)
  rintro t (⟨-, rfl⟩ | ⟨q, -, -, rfl⟩)
  · exact Or.inl rfl
  · exact Or.inr ⟨q, rfl⟩

theorem rationalTimes_pos {T t : ℝ} (ht : t ∈ rationalTimes T) : 0 < t ∧ t ≤ T := by
  rcases ht with ⟨h, rfl⟩ | ⟨q, h0, h1, rfl⟩
  · exact ⟨h, le_rfl⟩
  · exact ⟨h0, h1.le⟩

theorem cycJumpCount_max_zero (a b : ℝ) : cycJumpCount w a b = cycJumpCount w (max a 0) b := by
  unfold cycJumpCount
  congr 1
  ext r
  simp only [mem_inter_iff, mem_Ioc, cycJumpSet, mem_ofPred_eq]
  constructor
  · rintro ⟨hr, h1, h2⟩
    exact ⟨hr, max_lt h1 hr.1, h2⟩
  · rintro ⟨hr, h1, h2⟩
    exact ⟨hr, (le_max_left _ _).trans_lt h1, h2⟩

/-- Shifting the unit window by a small `δ` does not change the jump set in it. -/
theorem exists_shift_jumpSet (hw : IsCyclicPath w) (t : ℝ) :
    ∃ δ0 > 0, ∀ δ, 0 < δ → δ < δ0 →
      cycJumpSet w ∩ Ioc (t + δ - 1) (t + δ) = cycJumpSet w ∩ Ioc (t - 1) t := by
  have hF : (cycJumpSet w ∩ Iic (t + 1)).Finite := hw.fin _
  have h1 := eventually_lt_of_finite hF id (fun x => t - 1 < x) (t - 1) (fun x _ h => h)
  have h2 := eventually_lt_of_finite hF id (fun x => t < x) t (fun x _ h => h)
  obtain ⟨δ0, ⟨hall, h01⟩, hδ0⟩ := (((h1.and h2).and (Ioo_mem_nhdsGT (zero_lt_one : (0 : ℝ) < 1))).and self_mem_nhdsWithin).exists
  refine ⟨δ0, hδ0, fun δ hδ hδ0' => ?_⟩
  obtain ⟨H1, H2⟩ := hall
  ext x
  simp only [mem_inter_iff, mem_Ioc]
  constructor
  · rintro ⟨hx, hx1, hx2⟩
    have hxF : x ∈ cycJumpSet w ∩ Iic (t + 1) := ⟨hx, show x ≤ t + 1 by linarith [h01.2]⟩
    refine ⟨hx, by linarith, ?_⟩
    by_contra hc
    have := H2 x hxF (not_le.1 hc)
    simp only [id] at this
    linarith
  · rintro ⟨hx, hx1, hx2⟩
    have hxF : x ∈ cycJumpSet w ∩ Iic (t + 1) := ⟨hx, show x ≤ t + 1 by linarith [h01.2]⟩
    have := H1 x hxF hx1
    simp only [id] at this
    exact ⟨hx, by linarith, by linarith⟩

theorem pathTjump_le_iff_rational (hw : IsCyclicPath w) {L : ℝ} (hL : 0 < L) {T : ℝ}
    (hT : 0 ≤ T) :
    pathTjump w L ≤ ENNReal.ofReal T ↔
      ∃ t ∈ rationalTimes T, L ≤ (cycJumpCount w (t - 1) t : ℝ) := by
  constructor
  · intro h
    have hnot : ¬ ENNReal.ofReal T < pathTjump w L := not_lt.2 h
    rw [ofReal_lt_pathTjump_iff hw hL] at hnot
    push Not at hnot
    obtain ⟨t, ht0, htT, htL⟩ := hnot
    rcases htT.eq_or_lt with rfl | hlt
    · exact ⟨t, Or.inl ⟨ht0, rfl⟩, htL⟩
    · obtain ⟨δ0, hδ0, hshift⟩ := exists_shift_jumpSet hw t
      obtain ⟨q, hq1, hq2⟩ := exists_rat_btwn (show t < min T (t + δ0) from
        lt_min hlt (by linarith))
      refine ⟨q, Or.inr ⟨q, by linarith, hq2.trans_le (min_le_left _ _), rfl⟩, ?_⟩
      have := hshift (q - t) (by linarith) (by linarith [hq2.trans_le (min_le_right T (t + δ0))])
      have e : cycJumpCount w (q - 1) q = cycJumpCount w (t - 1) t := by
        unfold cycJumpCount
        have e1 : (q : ℝ) = t + (q - t) := by ring
        rw [e1, show t + (q - t) - 1 = t + (q - t) - 1 from rfl, this]
      rw [e]; exact htL
  · rintro ⟨t, ht, hLt⟩
    obtain ⟨ht0, htT⟩ := rationalTimes_pos ht
    exact (iInf₂_le (f := fun t (_ : t ∈ tjumpSet w L) => ENNReal.ofReal t) t
      ⟨ht0, hLt⟩).trans (ENNReal.ofReal_le_ofReal htT)

end ElboimSly.Paper

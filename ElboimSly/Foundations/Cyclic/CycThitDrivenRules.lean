/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Foundations.Cyclic.CycRegenShift
public import ElboimSly.Foundations.Cyclic.DrivenWd
public import Mathlib

/-!
# Transferring the driving rules to a shifted path

ES22 Lemma 2.1, Step 2 ("same rules"). If `W` follows the rules
(D1)--(D3) for `x` at `t + s`, no index is forced for `W` at `t + s`, and the extra history of `W`
before time `t` does not block a (D2) jump, then `W(t + ·) - W(t)` follows the rules for
`x(t + ·) - x(t)` at `s`.
-/

@[expose] public section

open Filter Topology Set MeasureTheory
open scoped ENNReal NNReal

namespace ElboimSly.Cyclic

variable {d : ℕ} {x W : ℝ≥0 → Fin d → ℤ} {b : ℝ≥0}

theorem shiftPath_apply (f : ℝ≥0 → Fin d → ℤ) (a s : ℝ≥0) : shiftPath f a s = f (a + s) - f a :=
  rfl

theorem mem_CDisc_shiftPath {f : ℝ≥0 → Fin d → ℤ} (hf : IsRegPath f) {a s : ℝ≥0} (hs : 0 < s) :
    s ∈ CDisc (shiftPath f a) ↔ a + s ∈ CDisc f := by
  rw [(isRegPath_shiftPath hf a).mem_CDisc_iff, hf.mem_CDisc_iff, leftVal_shiftPath hf a hs]
  simp only [shiftPath_apply, ne_eq, sub_left_inj]
  exact ⟨fun h => ⟨add_pos_of_nonneg_of_pos zero_le hs, h.2⟩, fun h => ⟨hs, h.2⟩⟩

theorem jumpSize_shiftPath {f : ℝ≥0 → Fin d → ℤ} (hf : IsRegPath f) (a : ℝ≥0) {s : ℝ≥0}
    (hs : 0 < s) :
    shiftPath f a s - leftVal (shiftPath f a) s = f (a + s) - leftVal f (a + s) := by
  rw [leftVal_shiftPath hf a hs, shiftPath_apply]; abel

theorem add_sub_delay {t s : ℝ≥0} {k : ℕ} (h : (k : ℝ≥0) * b ≤ s) :
    t + (s - k * b) = t + s - k * b :=
  (add_tsub_assoc_of_le h t).symm

theorem forcedAt_of_shift {W : ℝ≥0 → Fin d → ℤ} (hW : IsRegPath W) (t : ℝ≥0) {s : ℝ≥0}
    (hs : 0 < s) {k : ℕ} (hk : ForcedAt b (shiftPath W t) s k) : ForcedAt b W (t + s) k := by
  obtain ⟨⟨h1, h2⟩, h3, h4⟩ := hk
  have h3' := mem_CDisc_of_shiftPath t h3
  rw [add_sub_delay h2] at h3'
  refine ⟨⟨h1, h2.trans le_add_self⟩, h3', ?_⟩
  have h4' := h4
  rw [shiftPath_apply, leftVal_shiftPath hW t hs, add_sub_delay h2] at h4'
  exact sub_left_inj.1 h4'

theorem forcedAt_shift_of {W : ℝ≥0 → Fin d → ℤ} (hW : IsRegPath W) (t : ℝ≥0) {s : ℝ≥0}
    (hs : 0 < s) {k : ℕ} (hk : ForcedAt b W (t + s) k) (hks : (k : ℝ≥0) * b < s) :
    ForcedAt b (shiftPath W t) s k := by
  obtain ⟨⟨h1, h2⟩, h3, h4⟩ := hk
  have hpos : 0 < s - k * b := tsub_pos_of_lt hks
  refine ⟨⟨h1, hks.le⟩, ?_, ?_⟩
  · rw [mem_CDisc_shiftPath hW hpos, add_sub_delay hks.le]; exact h3
  · rw [shiftPath_apply, leftVal_shiftPath hW t hs, add_sub_delay hks.le, h4]

theorem shift_rules {x W : ℝ≥0 → Fin d → ℤ} (hW : IsRegPath W) (hx : IsRegPath x) (t : ℝ≥0)
    {s : ℝ≥0} (hs : 0 < s)
    (hF : ∀ k, ForcedAt b W (t + s) k → (k : ℝ≥0) * b < s)
    (hD1 : DrivenD1 b W (t + s)) (hD2 : DrivenD2 b x W (t + s)) (hD3 : DrivenD3 b x W (t + s))
    (hExtra : t + s ∈ CDisc x → ∀ k, IsDelayIdx b (t + s) k → ¬ ((k : ℝ≥0) * b ≤ s) →
      leftVal W (t + s) + (x (t + s) - leftVal x (t + s)) ≠ W (t + s - k * b)) :
    DrivenD1 b (shiftPath W t) s ∧ DrivenD2 b (shiftPath x t) (shiftPath W t) s ∧
      DrivenD3 b (shiftPath x t) (shiftPath W t) s := by
  have hlv : leftVal (shiftPath W t) s = leftVal W (t + s) - W t := leftVal_shiftPath hW t hs
  have hFW : ((∀ k, ¬ ForcedAt b (shiftPath W t) s k) → ∀ k, ¬ ForcedAt b W (t + s) k) :=
    fun h k hk => h k (forcedAt_shift_of hW t hs hk (hF k hk))
  have hjump : ∀ s' : ℝ≥0, 0 < s' → shiftPath x t s' - leftVal (shiftPath x t) s' =
      x (t + s') - leftVal x (t + s') := fun s' hs' => jumpSize_shiftPath hx t hs'
  refine ⟨fun k hk hmin => ?_, fun hFp hsx => ?_, fun hFp hsx => ?_⟩
  · have hkW := forcedAt_of_shift hW t hs hk
    have hmin' : ∀ k' < k, ¬ ForcedAt b W (t + s) k' := fun k' hk' hk'W =>
      hmin k' hk' (forcedAt_shift_of hW t hs hk'W (hF k' hk'W))
    have h1 := hD1 k hkW hmin'
    have hpos : 0 < s - k * b := hk.2.1.1
    rw [shiftPath_apply, h1, leftVal_shiftPath hW t hpos, add_sub_delay hk.1.2]
  · have hsx' : t + s ∈ CDisc x := (mem_CDisc_shiftPath hx hs).1 hsx
    have hW2 := hD2 (hFW hFp) hsx'
    have hiff : TakenAt b (shiftPath x t) (shiftPath W t) s ↔ TakenAt b x W (t + s) := by
      constructor
      · intro hT k hk
        by_cases hkb : (k : ℝ≥0) * b ≤ s
        · have := hT k ⟨hk.1, hkb⟩
          rw [hlv, hjump s hs, shiftPath_apply, add_sub_delay hkb] at this
          intro heq
          apply this
          rw [← heq]; abel
        · exact hExtra hsx' k hk hkb
      · intro hT k hk
        have := hT k ⟨hk.1, hk.2.trans le_add_self⟩
        rw [hlv, hjump s hs, shiftPath_apply, add_sub_delay hk.2]
        intro heq
        apply this
        have : leftVal W (t + s) + (x (t + s) - leftVal x (t + s)) - W t =
            W (t + s - k * b) - W t := by
          rw [← heq]; abel
        exact sub_left_inj.1 this
    by_cases hT : TakenAt b x W (t + s)
    · rw [ite_eq_left hT] at hW2
      rw [ite_eq_left (hiff.2 hT), hlv, hjump s hs, shiftPath_apply, hW2]; abel
    · rw [ite_eq_right hT] at hW2
      rw [ite_eq_right (fun h => hT (hiff.1 h)), hlv, shiftPath_apply, hW2]
  · have hsx' : t + s ∉ CDisc x := fun h => hsx ((mem_CDisc_shiftPath hx hs).2 h)
    have := hD3 (hFW hFp) hsx'
    rw [hlv, shiftPath_apply, this]

end ElboimSly.Cyclic

end

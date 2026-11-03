/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Foundations.Cyclic.CycThitDrivenHit
public import ElboimSly.Foundations.Cyclic.CycThitDrivenRules
public import ElboimSly.Foundations.Cyclic.DrivenClosing
public import Mathlib

/-!
# ES22 Lemma 2.1: Step 2 (same rules)

ES22 Lemma 2.1, Step 2. Up to `t_hit(t)`, the extra history of `W = w^x` in
`[0, t]` never triggers a rule, so `W(t + ·) - W(t)` is the walk driven by `x(t + ·) - x(t)`.
-/

@[expose] public section

open Filter Topology Set MeasureTheory
open scoped ENNReal NNReal

namespace ElboimSly.Cyclic

variable {d : ℕ} {b : ℝ≥0} {x : ℝ≥0 → Fin d → ℤ}

/-- A (D1) index of `W` at a time `t + s ≤ t_hit` refers to a time after `t`. -/
theorem forced_late (hb : 0 < b) (hx : x ∈ CycCF b) {t : ℝ≥0} (ht0 : 0 < t)
    (htτ : (t : ℝ≥0∞) < drivenTreg b x) {s : ℝ≥0} (hs : 0 < s)
    (hsh : ((t + s : ℝ≥0) : ℝ≥0∞) ≤ drivenThit b x t) {k : ℕ}
    (hk : ForcedAt b (drivenWalk b x) (t + s) k) : (k : ℝ≥0) * b < s := by
  by_contra hks
  rw [not_lt] at hks
  obtain ⟨⟨h1, h2⟩, hJ, heq⟩ := hk
  have hu''t : t + s - k * b ≤ t := by
    rw [tsub_le_iff_right]; exact add_le_add le_rfl hks
  have hu : t + s = (t + s - k * b) + k * b := (tsub_add_cancel_of_le h2).symm
  refine step1 hb hx ht0 htτ (j := k) (u := t + s) (u' := t + s - k * b)
    (lt_add_of_pos_right t hs) hsh hJ.1 hu''t hu ?_
  have hunit := drivenWalk_unit hx.1 hb _ hJ
  have : leftVal (drivenWalk b x) (t + s) - leftVal (drivenWalk b x) (t + s - k * b) =
      drivenWalk b x (t + s - k * b) - leftVal (drivenWalk b x) (t + s - k * b) := by
    rw [← heq]
  rw [this]; exact norm_le_one_of_unit hunit

/-- The extra history of `W` before `t` never blocks a (D2) jump. -/
theorem extra_history (hb : 0 < b) (hx : x ∈ CycCF b) {t : ℝ≥0} (ht0 : 0 < t)
    (htτ : (t : ℝ≥0∞) < drivenTreg b x) {s : ℝ≥0} (hs : 0 < s)
    (hsh : ((t + s : ℝ≥0) : ℝ≥0∞) ≤ drivenThit b x t) :
    t + s ∈ CDisc x → ∀ k, IsDelayIdx b (t + s) k → ¬ ((k : ℝ≥0) * b ≤ s) →
      leftVal (drivenWalk b x) (t + s) + (x (t + s) - leftVal x (t + s)) ≠
        drivenWalk b x (t + s - k * b) := by
  intro hxu k hk hkb heq
  have hxr : IsRegPath x := hx.1.toIsRegPath
  have hW := drivenWalk_isRegPath hxr hb
  have hu''t : t + s - k * b < t := by
    rw [tsub_lt_iff_right hk.2]; exact add_lt_add_of_le_of_lt le_rfl (not_le.1 hkb)
  by_cases h0 : t + s - k * b = 0
  · have : t + s = k * b := le_antisymm (tsub_eq_zero_iff_le.1 h0) hk.2
    exact hx.2.2 k hk.1 (this ▸ hxu)
  have hpos : 0 < t + s - k * b := pos_iff_ne_zero.2 h0
  have hu : t + s = (t + s - k * b) + k * b := (tsub_add_cancel_of_le hk.2).symm
  by_cases hJ : t + s - k * b ∈ CDisc (drivenWalk b x)
  · have hle : ((t + s - k * b : ℝ≥0) : ℝ≥0∞) ≤ drivenTreg b x :=
      ((by exact_mod_cast hu''t.le : ((t + s - k * b : ℝ≥0) : ℝ≥0∞) ≤ t)).trans htτ.le
    obtain ⟨t0, j, ht0x, he, -⟩ := (drivenSol hxr hb).root hx.2.1 _ hJ hle
    refine hx.2.1 t0 ht0x (t + s) hxu (j + k) (by have := hk.1; omega) ?_
    calc t + s = (t + s - k * b) + k * b := hu
      _ = _ := by rw [he]; push_cast; ring
  · have hno := hW.leftVal_eq_of_not_mem hpos hJ
    refine step1 hb hx ht0 htτ (j := k) (u := t + s) (u' := t + s - k * b)
      (lt_add_of_pos_right t hs) hsh hpos hu''t.le hu ?_
    have h1 : leftVal (drivenWalk b x) (t + s) - leftVal (drivenWalk b x) (t + s - k * b) =
        -(x (t + s) - leftVal x (t + s)) := by
      calc _ = (leftVal (drivenWalk b x) (t + s) + (x (t + s) - leftVal x (t + s))) -
            leftVal (drivenWalk b x) (t + s - k * b) - (x (t + s) - leftVal x (t + s)) := by abel
        _ = _ := by rw [heq, hno]; abel
    rw [h1, norm_neg]
    exact norm_le_one_of_unit (hx.1.unit _ hxu)

/-- **Step 2**: up to `t_hit(t)`, `W(t + s) - W(t) = W'(s)` where `W' = w^{x(t + ·) - x(t)}`. -/
theorem step2 (hb : 0 < b) (hx : x ∈ CycCF b) {t : ℝ≥0} (ht0 : 0 < t)
    (htτ : (t : ℝ≥0∞) < drivenTreg b x) {T : ℝ≥0}
    (hT : ((t + T : ℝ≥0) : ℝ≥0∞) ≤ drivenThit b x t) :
    ∀ s ≤ T, drivenWalk b x (t + s) - drivenWalk b x t = drivenWalk b (shiftPath x t) s := by
  have hxr : IsRegPath x := hx.1.toIsRegPath
  have hW := drivenWalk_isRegPath hxr hb
  have hx' := isRegPath_shiftPath hxr t
  have key := drivenWalk_unique hx' hb (T := T) (p := shiftPath (drivenWalk b x) t)
    (fun s _ => (isRegPath_shiftPath hW t).rc s) (by simp [shiftPath_apply])
    (fun s hs hsT => by
      have hsh : ((t + s : ℝ≥0) : ℝ≥0∞) ≤ drivenThit b x t :=
        le_trans (by exact_mod_cast add_le_add le_rfl hsT) hT
      have hD := drivenWalk_D123 hxr hb (t := t + s) (lt_of_lt_of_le hs le_add_self)
      exact shift_rules hW hxr t hs
        (fun k hk => forced_late hb hx ht0 htτ hs hsh hk) hD.1 hD.2.1 hD.2.2
        (extra_history hb hx ht0 htτ hs hsh))
  intro s hs
  exact key s hs

end ElboimSly.Cyclic

end

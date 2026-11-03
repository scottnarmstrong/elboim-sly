/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Foundations.Cyclic.DrivenEvents
import Mathlib

/-!
# The driven walk is a step function satisfying the rules

Well-definedness and measurability of the driven construction (a).

For a regular path `x`, the driven walk `drivenWalk β x` is a step function: it equals
`drivenVal β x n` on `[e_n, e_{n+1})` where `e_n = drivenTimes β x n`.  From this we get that it is
right-continuous with jumps in the event set, and that it satisfies (D1)--(D3) at every `t > 0`.
-/

@[expose] public section

open Filter Topology Set MeasureTheory
open scoped ENNReal NNReal

namespace ElboimSly.Cyclic

variable {d : ℕ} {x : ℝ≥0 → Fin d → ℤ} {β : ℝ≥0}

/-- The value of the driven walk on `[e_n, e_{n+1})`. -/
noncomputable def drivenVal (β : ℝ≥0) (x : ℝ≥0 → Fin d → ℤ) : ℕ → Fin d → ℤ
  | 0 => 0
  | n + 1 => drivenRuleVal β x (drivenStage β x n) (drivenTimes β x (n + 1)).toNNReal

theorem drivenStage_succ_of_lt {n : ℕ} {s : ℝ≥0} (h : (s : ℝ≥0∞) < drivenTimes β x (n + 1)) :
    drivenStage β x (n + 1) s = drivenStage β x n s := by
  simp only [drivenStage, ite_eq_left h]

theorem drivenStage_ge {n : ℕ} {s : ℝ≥0} (h : drivenTimes β x n ≤ s) :
    drivenStage β x n s = drivenVal β x n := by
  cases n with
  | zero => simp [drivenStage, drivenVal]
  | succ n =>
    simp only [drivenStage, drivenVal, ite_eq_right (not_lt.2 h)]

theorem drivenStage_stable (hx : IsRegPath x) (hβ : 0 < β) {n : ℕ} {s : ℝ≥0}
    (h : (s : ℝ≥0∞) < drivenTimes β x (n + 1)) :
    ∀ m, n ≤ m → drivenStage β x m s = drivenStage β x n s := by
  intro m hm
  induction m, hm using Nat.le_induction with
  | base => rfl
  | succ m hnm ih =>
    rw [drivenStage_succ_of_lt (lt_of_lt_of_le h (drivenTimes_mono hx hβ (by omega))), ih]

theorem drivenWalk_eq_stage (hx : IsRegPath x) (hβ : 0 < β) {n : ℕ} {s : ℝ≥0}
    (h : (s : ℝ≥0∞) < drivenTimes β x (n + 1)) :
    drivenWalk β x s = drivenStage β x n s := by
  classical
  have hex : ∃ n, (s : ℝ≥0∞) < drivenTimes β x (n + 1) := ⟨n, h⟩
  unfold drivenWalk
  rw [dite_eq_left hex]
  have hNn : Nat.find hex ≤ n := Nat.find_min' hex h
  exact (drivenStage_stable hx hβ (Nat.find_spec hex) n hNn).symm

theorem drivenWalk_eq_val (hx : IsRegPath x) (hβ : 0 < β) {n : ℕ} {s : ℝ≥0}
    (h1 : drivenTimes β x n ≤ s) (h2 : (s : ℝ≥0∞) < drivenTimes β x (n + 1)) :
    drivenWalk β x s = drivenVal β x n := by
  rw [drivenWalk_eq_stage hx hβ h2, drivenStage_ge h1]

theorem drivenWalk_zero (hx : IsRegPath x) (hβ : 0 < β) : drivenWalk β x 0 = 0 := by
  have h : ((0 : ℝ≥0) : ℝ≥0∞) < drivenTimes β x (0 + 1) := by
    have := drivenTimes_lt_succ hx hβ (n := 0) (by simp [drivenTimes_zero])
    simpa [drivenTimes_zero] using this
  rw [drivenWalk_eq_stage hx hβ h]
  simp [drivenStage]

theorem mem_events_of_mem_CDisc (hx : IsRegPath x) (hβ : 0 < β) {s : ℝ≥0}
    (hs : s ∈ CDisc (drivenWalk β x)) : s ∈ drivenEvents β x := by
  obtain ⟨n, hn1, hn2⟩ := exists_interval hx hβ s
  have hs0 : 0 < s := hs.1
  by_cases heq : drivenTimes β x n = s
  · cases n with
    | zero =>
      rw [drivenTimes_zero] at heq
      have : (s : ℝ≥0∞) = 0 := heq.symm
      exact absurd (by exact_mod_cast this : s = 0) hs0.ne'
    | succ m =>
      obtain ⟨t, ht, hte⟩ := drivenTimes_succ_mem hx hβ (n := m)
        (by rw [heq]; exact ENNReal.coe_lt_top)
      have : t = s := by
        rw [heq] at hte
        exact_mod_cast hte.symm
      exact this ▸ ht
  · exfalso
    apply hs.2
    have hlt : drivenTimes β x n < s := lt_of_le_of_ne hn1 heq
    have hfin : drivenTimes β x n ≠ ⊤ := ne_top_of_lt hlt
    have hm : ((drivenTimes β x n).toNNReal : ℝ≥0∞) = drivenTimes β x n :=
      ENNReal.coe_toNNReal hfin
    have hms : (drivenTimes β x n).toNNReal < s := by
      rw [← hm] at hlt
      exact_mod_cast hlt
    filter_upwards [Ioo_mem_nhdsLT hms] with u hu
    have hu1 : drivenTimes β x n ≤ u := by
      rw [← hm]; exact_mod_cast hu.1.le
    have hu2 : (u : ℝ≥0∞) < drivenTimes β x (n + 1) :=
      lt_trans (by exact_mod_cast hu.2) hn2
    rw [drivenWalk_eq_val hx hβ hu1 hu2, drivenWalk_eq_val hx hβ hn1 hn2]

theorem drivenWalk_isRegPath (hx : IsRegPath x) (hβ : 0 < β) : IsRegPath (drivenWalk β x) := by
  refine ⟨fun s => ?_, fun T => ?_⟩
  · obtain ⟨n, hn1, hn2⟩ := exists_interval hx hβ s
    obtain ⟨b, hb1, hb2⟩ := ENNReal.lt_iff_exists_nnreal_btwn.1 hn2
    have hsb : s < b := by exact_mod_cast hb1
    filter_upwards [Ico_mem_nhdsGE hsb] with u hu
    have hu1 : drivenTimes β x n ≤ u := hn1.trans (by exact_mod_cast hu.1)
    have hu2 : (u : ℝ≥0∞) < drivenTimes β x (n + 1) :=
      lt_trans (by exact_mod_cast hu.2) hb2
    rw [drivenWalk_eq_val hx hβ hu1 hu2, drivenWalk_eq_val hx hβ hn1 hn2]
  · exact (drivenEvents_finite hx hβ T).subset fun s hs =>
      ⟨mem_events_of_mem_CDisc hx hβ hs.1, hs.2⟩

theorem drivenWalk_rule (hx : IsRegPath x) (hβ : 0 < β) {t : ℝ≥0} (ht : 0 < t) :
    drivenWalk β x t = drivenRuleVal β x (drivenWalk β x) t := by
  by_cases hE : t ∈ drivenEvents β x
  · obtain ⟨n, hn⟩ := drivenEvents_eq_times hx hβ hE
    have hlt : (t : ℝ≥0∞) < drivenTimes β x (n + 1 + 1) := by
      have := drivenTimes_lt_succ hx hβ (n := n + 1) (by rw [hn]; exact ENNReal.coe_lt_top)
      rwa [hn] at this
    rw [drivenWalk_eq_val hx hβ (n := n + 1) (by rw [hn]) hlt]
    simp only [drivenVal, hn, ENNReal.toNNReal_coe]
    refine drivenRuleVal_congr β hβ (fun _ _ => rfl) fun s hs => ?_
    have : (s : ℝ≥0∞) < drivenTimes β x (n + 1) := by rw [hn]; exact_mod_cast hs
    rw [drivenWalk_eq_stage hx hβ this]
  · have hreg := drivenWalk_isRegPath hx hβ
    have hnoJ : t ∉ CDisc (drivenWalk β x) := fun h => hE (mem_events_of_mem_CDisc hx hβ h)
    have hnoX : t ∉ CDisc x := fun h => hE ⟨t, h, 0, by simp⟩
    have hnoF : ¬ ∃ k, ForcedAt β (drivenWalk β x) t k := by
      rintro ⟨k, hk, hkJ, -⟩
      obtain ⟨s, hs, j, hsj⟩ := mem_events_of_mem_CDisc hx hβ hkJ
      refine hE ⟨s, hs, j + k, ?_⟩
      have : t = (t - k * β) + k * β := (tsub_add_cancel_of_le hk.2).symm
      rw [this, hsj]; push_cast; ring
    rw [drivenRuleVal, ite_eq_right hnoF, ite_eq_right hnoX]
    exact (hreg.leftVal_eq_of_not_mem ht hnoJ).symm

/-- Uniqueness of solutions of (D1)--(D3): two right-continuous paths on `[0, T]` with the same
starting value that satisfy the rules for drivers that agree on `[0, T]` agree on `[0, T]`. -/
theorem eq_on_of_rules (hβ : 0 < β) {x y p q : ℝ≥0 → Fin d → ℤ} {T : ℝ≥0}
    (hxy : ∀ s ≤ T, x s = y s)
    (hp : ∀ s < T, ∀ᶠ u in 𝓝[≥] s, p u = p s) (hq : ∀ s < T, ∀ᶠ u in 𝓝[≥] s, q u = q s)
    (h0 : p 0 = q 0)
    (hpr : ∀ t, 0 < t → t ≤ T → p t = drivenRuleVal β x p t)
    (hqr : ∀ t, 0 < t → t ≤ T → q t = drivenRuleVal β y q t) :
    ∀ s ≤ T, p s = q s := by
  by_contra hcon
  push Not at hcon
  set S : Set ℝ≥0 := {s | s ≤ T ∧ p s ≠ q s} with hS
  have hne : S.Nonempty := by obtain ⟨s, hs, h⟩ := hcon; exact ⟨s, hs, h⟩
  set r := sInf S with hr
  have hbelow : ∀ u < r, p u = q u := by
    intro u hu
    by_contra hne'
    have hrT : r ≤ T := by
      obtain ⟨s, hs⟩ := hne
      exact (csInf_le (OrderBot.bddBelow S) hs).trans hs.1
    exact absurd (csInf_le (OrderBot.bddBelow S) ⟨(hu.trans_le hrT).le, hne'⟩) (not_le.2 hu)
  have hrT : r ≤ T := by
    obtain ⟨s, hs⟩ := hne
    exact (csInf_le (OrderBot.bddBelow S) hs).trans hs.1
  by_cases hrS : r ∈ S
  · have hr0 : 0 < r := by
      rcases eq_zero_or_pos r with h | h
      · exact absurd (h ▸ h0) hrS.2
      · exact h
    apply hrS.2
    rw [hpr r hr0 hrT, hqr r hr0 hrT]
    exact drivenRuleVal_congr β hβ (fun s hs => hxy s (hs.trans hrT)) hbelow
  · have hpq : p r = q r := by
      by_contra hh; exact hrS ⟨hrT, hh⟩
    have hrlt : r < T := by
      refine lt_of_le_of_ne hrT fun hrt => ?_
      -- r = T: every element of S is ≥ r = T and ≤ T, so equals T = r ∈ S
      obtain ⟨s, hs⟩ := hne
      have hsr : r ≤ s := csInf_le (OrderBot.bddBelow S) hs
      have : s = r := le_antisymm (hs.1.trans hrt.symm.le) hsr
      exact hrS (this ▸ hs)
    obtain ⟨u', hu', hsub⟩ := mem_nhdsGE_iff_exists_Ico_subset.1
      ((hp r hrlt).and (hq r hrlt))
    have hall : ∀ s ∈ S, u' ≤ s := by
      intro s hs
      by_contra hlt
      rw [not_le] at hlt
      rcases lt_or_ge s r with hsr | hsr
      · exact hs.2 (hbelow s hsr)
      · have := hsub ⟨hsr, hlt⟩
        exact hs.2 (by rw [this.1, this.2, hpq])
    have : u' ≤ r := le_csInf hne hall
    exact absurd hu' (not_lt.2 this)

end ElboimSly.Cyclic

end

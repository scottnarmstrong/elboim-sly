/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Foundations.Cyclic.DrivenBasic
import Mathlib

/-!
# The driven construction: the event set

Well-definedness and measurability of the driven construction (a), first sentence: `E(x)` is locally finite.  We show that the
enumeration `drivenTimes β x` of `{0} ∪ E(x)` is strictly increasing until it reaches `⊤`, takes
values in `E(x)`, misses no event, and exceeds every finite time.
-/

@[expose] public section

open Filter Topology Set MeasureTheory
open scoped ENNReal NNReal

namespace ElboimSly.Cyclic

variable {d : ℕ} {x : ℝ≥0 → Fin d → ℤ} {β : ℝ≥0}

theorem drivenEvents_pos {t : ℝ≥0} (ht : t ∈ drivenEvents β x) : 0 < t := by
  obtain ⟨s, hs, k, rfl⟩ := ht
  exact lt_of_lt_of_le hs.1 le_self_add

/-- Well-definedness and measurability of the driven construction (a): `E(x)` is locally finite. -/
theorem drivenEvents_finite (hx : IsRegPath x) (hβ : 0 < β) (T : ℝ≥0) :
    (drivenEvents β x ∩ Iic T).Finite := by
  refine (((hx.fin T).prod (Set.finite_Iic ⌈T / β⌉₊)).image
    (fun q : ℝ≥0 × ℕ => q.1 + q.2 * β)).subset ?_
  rintro t ⟨⟨s, hs, k, rfl⟩, ht⟩
  have ht' : s + k * β ≤ T := ht
  refine ⟨(s, k), ⟨⟨hs, ?_⟩, ?_⟩, rfl⟩
  · exact ((le_self_add : s ≤ s + k * β).trans ht' : s ≤ T)
  · have h1 : (k : ℝ≥0) * β ≤ T := ((le_add_self : (k : ℝ≥0) * β ≤ s + k * β).trans ht')
    have h2 : (k : ℝ≥0) ≤ T / β := by rwa [le_div_iff₀ hβ]
    have h3 : (k : ℝ≥0) ≤ ⌈T / β⌉₊ := h2.trans (Nat.le_ceil _)
    exact_mod_cast h3

theorem nextEvent_top : nextEvent β x ⊤ = ⊤ := by
  unfold nextEvent
  have : {e | ∃ t ∈ drivenEvents β x, (t : ℝ≥0∞) = e ∧ (⊤ : ℝ≥0∞) < e} = ∅ := by
    ext e; simp
  rw [this, sInf_empty]

theorem nextEvent_spec (hx : IsRegPath x) (hβ : 0 < β) {r : ℝ≥0∞} (_hr : r < ⊤) :
    (nextEvent β x r = ⊤ ∧ ∀ t ∈ drivenEvents β x, ¬ r < (t : ℝ≥0∞)) ∨
      ∃ m ∈ drivenEvents β x, nextEvent β x r = m ∧ r < (m : ℝ≥0∞) ∧
        ∀ t ∈ drivenEvents β x, r < (t : ℝ≥0∞) → m ≤ t := by
  classical
  by_cases hS : ∃ t ∈ drivenEvents β x, r < (t : ℝ≥0∞)
  · right
    obtain ⟨t0, ht0, hrt0⟩ := hS
    have hfin : (drivenEvents β x ∩ Iic t0).Finite := drivenEvents_finite hx hβ t0
    have hfin' : {t | t ∈ drivenEvents β x ∧ t ≤ t0 ∧ r < (t : ℝ≥0∞)}.Finite :=
      hfin.subset fun t ht => ⟨ht.1, ht.2.1⟩
    have hne : hfin'.toFinset.Nonempty := ⟨t0, hfin'.mem_toFinset.2 ⟨ht0, le_rfl, hrt0⟩⟩
    set m := hfin'.toFinset.min' hne with hm
    have hmmem : m ∈ drivenEvents β x ∧ m ≤ t0 ∧ r < (m : ℝ≥0∞) := by
      exact hfin'.mem_toFinset.1 (hfin'.toFinset.min'_mem hne)
    have hmin : ∀ t ∈ drivenEvents β x, r < (t : ℝ≥0∞) → m ≤ t := by
      intro t ht hrt
      rcases le_total t t0 with htt | htt
      · exact hfin'.toFinset.min'_le t (hfin'.mem_toFinset.2 ⟨ht, htt, hrt⟩)
      · exact hmmem.2.1.trans htt
    refine ⟨m, hmmem.1, ?_, hmmem.2.2, hmin⟩
    unfold nextEvent
    refine le_antisymm (sInf_le ⟨m, hmmem.1, rfl, hmmem.2.2⟩) (le_sInf ?_)
    rintro e ⟨t, ht, rfl, hrt⟩
    exact_mod_cast hmin t ht hrt
  · left
    push Not at hS
    refine ⟨?_, fun t ht => not_lt.2 (hS t ht)⟩
    unfold nextEvent
    have : {e | ∃ t ∈ drivenEvents β x, (t : ℝ≥0∞) = e ∧ r < e} = ∅ := by
      ext e
      simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false, not_exists, not_and]
      rintro t ht rfl
      exact not_lt.2 (hS t ht)
    rw [this, sInf_empty]

theorem drivenTimes_zero : drivenTimes β x 0 = 0 := rfl

theorem drivenTimes_succ (n : ℕ) : drivenTimes β x (n + 1) = nextEvent β x (drivenTimes β x n) :=
  rfl

theorem drivenTimes_lt_succ (hx : IsRegPath x) (hβ : 0 < β) {n : ℕ}
    (h : drivenTimes β x n < ⊤) : drivenTimes β x n < drivenTimes β x (n + 1) := by
  rw [drivenTimes_succ]
  rcases nextEvent_spec hx hβ h with ⟨h1, _⟩ | ⟨m, _, h1, h2, _⟩
  · rw [h1]; exact h
  · rw [h1]; exact h2

theorem drivenTimes_le_succ (hx : IsRegPath x) (hβ : 0 < β) (n : ℕ) :
    drivenTimes β x n ≤ drivenTimes β x (n + 1) := by
  by_cases h : drivenTimes β x n < ⊤
  · exact (drivenTimes_lt_succ hx hβ h).le
  · rw [not_lt, top_le_iff] at h
    rw [drivenTimes_succ, h, nextEvent_top]

theorem drivenTimes_mono (hx : IsRegPath x) (hβ : 0 < β) : Monotone (drivenTimes β x) :=
  monotone_nat_of_le_succ (drivenTimes_le_succ hx hβ)

theorem drivenTimes_succ_mem (hx : IsRegPath x) (hβ : 0 < β) {n : ℕ}
    (h : drivenTimes β x (n + 1) < ⊤) :
    ∃ m ∈ drivenEvents β x, drivenTimes β x (n + 1) = m := by
  have hn : drivenTimes β x n < ⊤ := by
    refine lt_of_le_of_lt ?_ h
    exact drivenTimes_le_succ hx hβ n
  rcases nextEvent_spec hx hβ hn with ⟨h1, _⟩ | ⟨m, hm, h1, _⟩
  · rw [drivenTimes_succ, h1] at h; exact absurd h (lt_irrefl _)
  · exact ⟨m, hm, by rw [drivenTimes_succ, h1]⟩

theorem not_event_between (hx : IsRegPath x) (hβ : 0 < β) {n : ℕ} {t : ℝ≥0}
    (ht : t ∈ drivenEvents β x) (h1 : drivenTimes β x n < t) :
    drivenTimes β x (n + 1) ≤ t := by
  have hn : drivenTimes β x n < ⊤ := lt_of_lt_of_le h1 le_top
  rcases nextEvent_spec hx hβ hn with ⟨_, h2⟩ | ⟨m, _, h1', _, h3⟩
  · exact absurd h1 (h2 t ht)
  · rw [drivenTimes_succ, h1']
    exact_mod_cast h3 t ht h1

theorem exists_times_gt (hx : IsRegPath x) (hβ : 0 < β) (T : ℝ≥0) :
    ∃ n, (T : ℝ≥0∞) < drivenTimes β x (n + 1) := by
  by_contra hcon
  push Not at hcon
  have hlt : ∀ n, drivenTimes β x (n + 1) < ⊤ := fun n =>
    lt_of_le_of_lt (hcon n) ENNReal.coe_lt_top
  have hmem : ∀ n, ∃ m ∈ drivenEvents β x, drivenTimes β x (n + 1) = m :=
    fun n => drivenTimes_succ_mem hx hβ (hlt n)
  choose g hgE hg using hmem
  have hstrict : StrictMono g := by
    refine strictMono_nat_of_lt_succ fun n => ?_
    have := drivenTimes_lt_succ hx hβ (hlt n)
    rw [hg n, hg (n + 1)] at this
    exact_mod_cast this
  have hfin := drivenEvents_finite hx hβ T
  have hsub : ∀ n, g n ∈ drivenEvents β x ∩ Iic T := fun n => by
    refine ⟨hgE n, ?_⟩
    have := hcon n
    rw [hg n] at this
    exact_mod_cast this
  exact Set.infinite_range_of_injective hstrict.injective
    (hfin.subset (by rintro _ ⟨n, rfl⟩; exact hsub n))

theorem drivenEvents_eq_times (hx : IsRegPath x) (hβ : 0 < β) {t : ℝ≥0}
    (ht : t ∈ drivenEvents β x) : ∃ n, drivenTimes β x (n + 1) = t := by
  classical
  have hex : ∃ n, (t : ℝ≥0∞) ≤ drivenTimes β x (n + 1) := by
    obtain ⟨n, hn⟩ := exists_times_gt hx hβ t
    exact ⟨n, hn.le⟩
  set n := Nat.find hex with hn
  have hle : (t : ℝ≥0∞) ≤ drivenTimes β x (n + 1) := Nat.find_spec hex
  have hge : drivenTimes β x n < t := by
    rcases Nat.eq_zero_or_pos n with h0 | hpos
    · rw [h0, drivenTimes_zero]; exact_mod_cast drivenEvents_pos ht
    · obtain ⟨m, hm⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
      have := Nat.find_min hex (show m < n by omega)
      rw [hm]; exact not_le.1 this
  refine ⟨n, le_antisymm ?_ hle⟩
  exact_mod_cast not_event_between hx hβ ht hge

theorem exists_interval (hx : IsRegPath x) (hβ : 0 < β) (s : ℝ≥0) :
    ∃ n, drivenTimes β x n ≤ s ∧ (s : ℝ≥0∞) < drivenTimes β x (n + 1) := by
  classical
  have hex : ∃ n, (s : ℝ≥0∞) < drivenTimes β x (n + 1) := exists_times_gt hx hβ s
  refine ⟨Nat.find hex, ?_, Nat.find_spec hex⟩
  rcases Nat.eq_zero_or_pos (Nat.find hex) with h0 | hpos
  · rw [h0, drivenTimes_zero]; exact bot_le
  · obtain ⟨m, hm⟩ : ∃ m, Nat.find hex = m + 1 := ⟨Nat.find hex - 1, by omega⟩
    have := Nat.find_min hex (show m < Nat.find hex by omega)
    rw [hm]; exact not_lt.1 this

end ElboimSly.Cyclic

end

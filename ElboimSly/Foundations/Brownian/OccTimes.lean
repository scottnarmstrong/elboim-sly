/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import Mathlib

/-!
# Return times with a gap, a deterministic lemma

ES22 Lemma 9.3: occupation of a cube at integer times, Step 2 and Step 3.

For a predicate `h : ℕ → Prop` (the visits of a path) and a gap `T₀`, `occTimes T₀ h k` is the
`k`-th time, in `ℕ ∪ {∞}`, of the chain `κ_0 = inf {i | h i}`,
`κ_{k+1} = inf {i ≥ κ_k + T₀ | h i}`, with `κ_{k+1} = ∞` if `κ_k = ∞`.
-/

@[expose] public section

namespace ElboimSly.Brownian

open Classical in
/-- The first index `≥ a` at which `h` holds, in `ℕ ∪ {∞}`. -/
noncomputable def nxt (h : ℕ → Prop) (a : ℕ) : ℕ∞ :=
  if H : ∃ i, a ≤ i ∧ h i then ((Nat.find H : ℕ) : ℕ∞) else ⊤

lemma nxt_eq_iff (h : ℕ → Prop) (a j : ℕ) :
    nxt h a = (j : ℕ∞) ↔ a ≤ j ∧ h j ∧ ∀ i, a ≤ i → i < j → ¬ h i := by
  classical
  unfold nxt
  split_ifs with H
  · rw [Nat.cast_inj]
    constructor
    · rintro rfl
      exact ⟨(Nat.find_spec H).1, (Nat.find_spec H).2, fun i hai hij hi =>
        Nat.find_min H hij ⟨hai, hi⟩⟩
    · rintro ⟨haj, hj, hmin⟩
      refine le_antisymm (Nat.find_min' H ⟨haj, hj⟩) ?_
      by_contra hlt
      exact hmin _ (Nat.find_spec H).1 (not_le.1 hlt) (Nat.find_spec H).2
  · constructor
    · intro h0; exact absurd h0 (by simp)
    · rintro ⟨haj, hj, -⟩; exact absurd ⟨j, haj, hj⟩ H

lemma nxt_eq_top (h : ℕ → Prop) (a : ℕ) : nxt h a = ⊤ ↔ ∀ i, a ≤ i → ¬ h i := by
  classical
  unfold nxt
  split_ifs with H
  · simp only [ENat.natCast_ne_top, false_iff]
    push Not
    obtain ⟨i, hai, hi⟩ := H
    exact ⟨i, hai, hi⟩
  · simp only [true_iff]
    intro i hai hi
    exact H ⟨i, hai, hi⟩

lemma nxt_le {h : ℕ → Prop} {a i : ℕ} (hai : a ≤ i) (hi : h i) : nxt h a ≤ (i : ℕ∞) := by
  have hne : nxt h a ≠ ⊤ := fun htop => (nxt_eq_top h a).1 htop i hai hi
  obtain ⟨n, hn⟩ := ENat.ne_top_iff_exists.1 hne
  obtain ⟨-, -, hmin⟩ := (nxt_eq_iff h a n).1 hn.symm
  rw [← hn]
  exact_mod_cast not_lt.1 fun hlt => hmin i hai hlt hi

/-- One step of the chain. -/
noncomputable def occStep (T₀ : ℕ) (h : ℕ → Prop) (e : ℕ∞) : ℕ∞ :=
  if e = ⊤ then ⊤ else nxt h (e.toNat + T₀)

/-- The chain of return times `κ_k`. -/
noncomputable def occTimes (T₀ : ℕ) (h : ℕ → Prop) : ℕ → ℕ∞
  | 0 => nxt h 0
  | k + 1 => occStep T₀ h (occTimes T₀ h k)

lemma occTimes_succ_of_eq {T₀ : ℕ} {h : ℕ → Prop} {k n : ℕ} (hk : occTimes T₀ h k = n) :
    occTimes T₀ h (k + 1) = nxt h (n + T₀) := by
  simp [occTimes, occStep, hk]

lemma occTimes_succ_of_top {T₀ : ℕ} {h : ℕ → Prop} {k : ℕ} (hk : occTimes T₀ h k = ⊤) :
    occTimes T₀ h (k + 1) = ⊤ := by
  simp [occTimes, occStep, hk]

lemma occTimes_top_of_le {T₀ : ℕ} {h : ℕ → Prop} {m : ℕ} (hm : occTimes T₀ h m = ⊤) :
    ∀ k, m ≤ k → occTimes T₀ h k = ⊤ := by
  intro k hk
  induction k, hk using Nat.le_induction with
  | base => exact hm
  | succ k _ ih => exact occTimes_succ_of_top ih

lemma occTimes_spec {T₀ : ℕ} {h : ℕ → Prop} {k : ℕ} (hk : occTimes T₀ h k ≠ ⊤) :
    ∃ n : ℕ, occTimes T₀ h k = n ∧ h n := by
  cases k with
  | zero =>
    obtain ⟨n, hn⟩ := ENat.ne_top_iff_exists.1 hk
    exact ⟨n, hn.symm, ((nxt_eq_iff h 0 n).1 hn.symm).2.1⟩
  | succ k =>
    have hk' : occTimes T₀ h k ≠ ⊤ := fun htop => hk (occTimes_succ_of_top htop)
    obtain ⟨n0, hn0⟩ := ENat.ne_top_iff_exists.1 hk'
    rw [occTimes_succ_of_eq hn0.symm] at hk ⊢
    obtain ⟨n, hn⟩ := ENat.ne_top_iff_exists.1 hk
    exact ⟨n, hn.symm, ((nxt_eq_iff h _ n).1 hn.symm).2.1⟩

/-- `κ_{k+1} < ∞` iff `κ_k = n < ∞` and `h` holds at some index `≥ n + T₀`. -/
lemma occTimes_succ_ne_top_iff {T₀ : ℕ} {h : ℕ → Prop} {k : ℕ} :
    occTimes T₀ h (k + 1) ≠ ⊤ ↔
      ∃ n : ℕ, occTimes T₀ h k = n ∧ ∃ i, n + T₀ ≤ i ∧ h i := by
  constructor
  · intro hk
    have hk' : occTimes T₀ h k ≠ ⊤ := fun htop => hk (occTimes_succ_of_top htop)
    obtain ⟨n, hn⟩ := ENat.ne_top_iff_exists.1 hk'
    refine ⟨n, hn.symm, ?_⟩
    rw [occTimes_succ_of_eq hn.symm] at hk
    by_contra hcon
    push Not at hcon
    exact hk ((nxt_eq_top h _).2 fun i hi => hcon i hi)
  · rintro ⟨n, hn, i, hi, hhi⟩
    rw [occTimes_succ_of_eq hn]
    exact fun htop => (nxt_eq_top h _).1 htop i hi hhi

/-- Every visit lies in a window `[κ_k, κ_k + T₀)` with `k < m`, if `κ_m = ∞`. -/
lemma exists_window {T₀ : ℕ} {h : ℕ → Prop} {m : ℕ} (hm : occTimes T₀ h m = ⊤) {i : ℕ}
    (hi : h i) : ∃ k < m, ∃ n : ℕ, occTimes T₀ h k = n ∧ n ≤ i ∧ i < n + T₀ := by
  classical
  have hP : ∀ k, k ≥ m → ¬ occTimes T₀ h k ≤ (i : ℕ∞) := fun k hk hle => by
    rw [occTimes_top_of_le hm k hk] at hle
    exact absurd hle (by simp)
  have h0 : occTimes T₀ h 0 ≤ (i : ℕ∞) := nxt_le (Nat.zero_le _) hi
  have hm0 : 0 < m := by
    rcases Nat.eq_zero_or_pos m with rfl | h'
    · exact absurd h0 (hP 0 le_rfl)
    · exact h'
  set k := Nat.findGreatest (fun k => occTimes T₀ h k ≤ (i : ℕ∞)) m with hk
  have hkP : occTimes T₀ h k ≤ (i : ℕ∞) := Nat.findGreatest_spec (P := fun k => occTimes T₀ h k ≤ (i : ℕ∞))
    (Nat.zero_le m) h0
  have hkm : k ≤ m := Nat.findGreatest_le m
  have hkm' : k < m := lt_of_le_of_ne hkm fun heq => hP k (heq ▸ le_rfl) hkP
  have hne : occTimes T₀ h k ≠ ⊤ := fun htop => by rw [htop] at hkP; exact absurd hkP (by simp)
  obtain ⟨n, hn, -⟩ := occTimes_spec hne
  refine ⟨k, hkm', n, hn, ?_, ?_⟩
  · rw [hn] at hkP; exact_mod_cast hkP
  · by_contra hcon
    have hin : n + T₀ ≤ i := not_lt.1 hcon
    have hle : occTimes T₀ h (k + 1) ≤ (i : ℕ∞) := by
      rw [occTimes_succ_of_eq hn]; exact nxt_le hin hi
    have := Nat.findGreatest_is_greatest (P := fun k => occTimes T₀ h k ≤ (i : ℕ∞)) (Nat.lt_succ_self k)
      (hkm'.le |>.trans' le_rfl |> fun _ => Nat.succ_le_of_lt hkm')
    exact this hle

open scoped ENNReal in
/-- ES22 Lemma 9.3: occupation of a cube at integer times, Step 3: if `κ_m = ∞` then the number of visits is at most
`m T₀`. -/
lemma tsum_indicator_le {T₀ : ℕ} {h : ℕ → Prop} {m : ℕ} (hm : occTimes T₀ h m = ⊤) :
    ∑' i : ℕ, {i | h i}.indicator (1 : ℕ → ℝ≥0∞) i ≤ ((m * T₀ : ℕ) : ℝ≥0∞) := by
  classical
  set S : Finset ℕ := (Finset.range m).biUnion fun k =>
    Finset.Ico (occTimes T₀ h k).toNat ((occTimes T₀ h k).toNat + T₀) with hS
  have hsub : ∀ i, h i → i ∈ S := by
    intro i hi
    obtain ⟨k, hk, n, hn, hni, hin⟩ := exists_window hm hi
    refine Finset.mem_biUnion.2 ⟨k, Finset.mem_range.2 hk, ?_⟩
    rw [hn, ENat.toNat_natCast]
    exact Finset.mem_Ico.2 ⟨hni, hin⟩
  calc ∑' i : ℕ, {i | h i}.indicator (1 : ℕ → ℝ≥0∞) i
      ≤ ∑' i : ℕ, (S : Set ℕ).indicator (1 : ℕ → ℝ≥0∞) i :=
        ENNReal.tsum_le_tsum fun i => by
          by_cases hi : h i
          · rw [Set.indicator_of_mem (show i ∈ {i | h i} from hi),
              Set.indicator_of_mem (show i ∈ (S : Set ℕ) from hsub i hi)]
          · rw [Set.indicator_of_notMem (show i ∉ {i | h i} from hi)]; exact zero_le
    _ = ∑ i ∈ S, (1 : ℝ≥0∞) := by
        rw [tsum_eq_sum (s := S) (fun i hi => Set.indicator_of_notMem (by simpa using hi) _)]
        refine Finset.sum_congr rfl fun i hi => ?_
        rw [Set.indicator_of_mem (by simpa using hi)]; rfl
    _ = (S.card : ℝ≥0∞) := by simp
    _ ≤ ((m * T₀ : ℕ) : ℝ≥0∞) := by
        norm_cast
        calc S.card ≤ ∑ k ∈ Finset.range m, (Finset.Ico (occTimes T₀ h k).toNat
              ((occTimes T₀ h k).toNat + T₀)).card := Finset.card_biUnion_le
          _ = m * T₀ := by simp

end ElboimSly.Brownian

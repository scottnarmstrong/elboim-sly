/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Foundations.Cyclic.NextRing
public import ElboimSly.Foundations.Interchange.RingPathN
import Mathlib

/-!
# Greedy ring paths

Measurability, Step 0 (the sets `F_{v,j}`).

A ring path along a fixed vertex sequence `v` inside a window `[lo, hi]` exists iff the greedy
(earliest) choice of ring times exists and stays below `hi`. The greedy times are measurable
functions of the configuration, which replaces the rational-separation argument of the written proof.
-/

@[expose] public section

open MeasureTheory Set ElboimSly.Interchange
open scoped ENNReal

namespace ElboimSly.Cyclic

variable {d : ℕ} {β : ℝ} [Fact (0 < β)] {ν : Measure (RingSpace d β)}

/-- The edges `e` with `e = {a, b}` (at most one). -/
def pathE (v : ℕ → Fin d → ℤ) (i : ℕ) : Set (Edge d) := {e | e.1 = s(v i, v (i + 1))}

theorem pathE_finite (v : ℕ → Fin d → ℤ) (i : ℕ) : (pathE v i).Finite :=
  Set.Subsingleton.finite (fun _a ha _b hb => Subtype.ext (ha.trans hb.symm))

open scoped Classical in
/-- The greedy ring times: the first ring of `E 0` at or after `lo`, then successively the first
ring of `E (i+1)` strictly after the previous time. -/
noncomputable def gtime (lo : ℝ) (E : ℕ → Set (Edge d)) :
    ℕ → Measure (RingSpace d β) → ℝ
  | 0, ν => if RingsIn ν (E 0) lo then lo else nxtJ ν (E 0) lo
  | i + 1, ν => nxtJ ν (E (i + 1)) (gtime lo E i ν)

/-- The greedy choice exists for `n` steps and stays below `hi`. -/
def GreedyOK (lo hi : ℝ) (E : ℕ → Set (Edge d)) (n : ℕ) (ν : Measure (RingSpace d β)) : Prop :=
  (∀ i, i < n → HasRing ν (E i)) ∧ ∀ i, i + 1 = n → gtime lo E i ν ≤ hi

section

variable {lo hi : ℝ} {E : ℕ → Set (Edge d)}

theorem gtime_ring (hν : Nice ν) (hE : ∀ i, (E i).Finite) :
    ∀ i, HasRing ν (E i) → RingsIn ν (E i) (gtime lo E i ν) ∧
      (i = 0 → lo ≤ gtime lo E i ν) := by
  intro i hH
  cases i with
  | zero =>
    by_cases h : RingsIn ν (E 0) lo
    · simp [gtime, h]
    · simp only [gtime, h, ite_false, nxtJ_of_hasRing _ hH]
      have := isLeast_nxt hν (hE 0) lo hH
      exact ⟨this.1.2, fun _ => this.1.1.le⟩
  | succ i =>
    simp only [gtime, nxtJ_of_hasRing _ hH]
    exact ⟨(isLeast_nxt hν (hE _) _ hH).1.2, fun h => absurd h (by omega)⟩

theorem gtime_lt (hν : Nice ν) (hE : ∀ i, (E i).Finite) (i : ℕ) (hH : HasRing ν (E (i + 1))) :
    gtime lo E i ν < gtime lo E (i + 1) ν := by
  simp only [gtime, nxtJ_of_hasRing _ hH]
  exact (isLeast_nxt hν (hE _) _ hH).1.1

theorem gtime_le (hν : Nice ν) (hE : ∀ i, (E i).Finite) {n : ℕ}
    (hH : ∀ i, i < n → HasRing ν (E i)) {i j : ℕ} (hij : i ≤ j) (hj : j < n) :
    gtime lo E i ν ≤ gtime lo E j ν := by
  induction j, hij using Nat.le_induction with
  | base => exact le_rfl
  | succ j hij ih =>
    exact (ih (by omega)).trans (gtime_lt hν hE j (hH _ hj)).le

theorem greedy_iff (hν : Nice ν) (hE : ∀ i, (E i).Finite) (n : ℕ) (v : ℕ → Fin d → ℤ)
    (hEv : E = pathE v) :
    (∃ t : ℕ → ℝ, NRingPath ν (Icc lo hi) n v t) ↔ GreedyOK lo hi E n ν := by
  subst hEv
  constructor
  · rintro ⟨t, hmono, hJ, hring⟩
    have hH : ∀ i, i < n → HasRing ν (pathE v i) := fun i hi => by
      obtain ⟨e, he, hr⟩ := hring i hi
      exact ⟨t i, e, he, hr⟩
    have key : ∀ i, i < n → gtime lo (pathE v) i ν ≤ t i := by
      intro i
      induction i with
      | zero =>
        intro hi
        by_cases h : RingsIn ν (pathE v 0) lo
        · simp only [gtime, h, ite_true]; exact (hJ 0 hi).1
        · simp only [gtime, h, ite_false, nxtJ_of_hasRing _ (hH 0 hi)]
          rw [nxt_le_iff hν (hE 0) _ _ (hH 0 hi)]
          obtain ⟨e, he, hr⟩ := hring 0 hi
          refine ⟨t 0, lt_of_le_of_ne (hJ 0 hi).1 ?_, le_rfl, e, he, hr⟩
          intro heq
          exact h ⟨e, he, heq ▸ hr⟩
      | succ i ih =>
        intro hi
        simp only [gtime, nxtJ_of_hasRing _ (hH _ hi)]
        rw [nxt_le_iff hν (hE _) _ _ (hH _ hi)]
        obtain ⟨e, he, hr⟩ := hring (i + 1) hi
        exact ⟨t (i + 1), (ih (by omega)).trans_lt (hmono i (i + 1) (by omega) hi), le_rfl,
          e, he, hr⟩
    exact ⟨hH, fun i hi => (key i (by omega)).trans (hJ i (by omega)).2⟩
  · rintro ⟨hH, hhi⟩
    refine ⟨fun i => gtime lo (pathE v) i ν, ?_, ?_, ?_⟩
    · intro i j hij hj
      induction j, hij.le using Nat.le_induction with
      | base => exact absurd hij (lt_irrefl _)
      | succ j hij' ih =>
        rcases Nat.lt_or_ge i j with h | h
        · exact (ih h (by omega)).trans (gtime_lt hν hE j (hH _ hj))
        · have : i = j := by omega
          subst this
          exact gtime_lt hν hE i (hH _ hj)
    · intro i hlt
      have hlo : lo ≤ gtime lo (pathE v) i ν := by
        have h0 := (gtime_ring (lo := lo) hν hE 0 (hH 0 (by omega))).2 rfl
        exact h0.trans (gtime_le hν hE hH (Nat.zero_le i) hlt)
      have hup : gtime lo (pathE v) i ν ≤ hi :=
        (gtime_le hν hE hH (show i ≤ n - 1 by omega) (by omega)).trans
          (hhi (n - 1) (by omega))
      exact ⟨hlo, hup⟩
    · intro i hlt
      exact (gtime_ring hν hE i (hH i hlt)).1

end

end ElboimSly.Cyclic

end

/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Foundations.Cyclic.CycFinalNth
public import ElboimSly.Foundations.Cyclic.CycFinalSpec
public import Mathlib

/-!
# The environment scheme (b): entries of the final record, for any `K`

World-lines of a plan; joint exploration filtration (a). `CycPlan.Cont`: walk `n` is appended by the recursion (`n < K` and all
earlier world-lines finite). `cycFinal_nth_gen`: entry `k` of `cycFinal` is `E k` if `Cont k` and absent
otherwise (the version of `cycFinal_nth` without `K = ∞`).
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped ENNReal NNReal

namespace ElboimSly.Cyclic
namespace CycPlan
variable {I : Type*} [MeasurableSpace I] {d : ℕ} {β : ℝ} [Fact (0 < β)]
variable (P : CycPlan I d β) (path : PathRule I d)

/-- Walk `n` (0-indexed) is appended by the recursion: `n < K` and all earlier world-lines are
finite. -/
def Cont (n : ℕ) : Prop := (n : ℕ∞) < P.K ∧ P.AllFin path n

omit [Fact (0 < β)] in
theorem Cont.anti {m n : ℕ} (h : m ≤ n) (hn : P.Cont path n) : P.Cont path m :=
  ⟨lt_of_le_of_lt (by exact_mod_cast h) hn.1, fun i hi => hn.2 i (by omega)⟩

omit [Fact (0 < β)] in
theorem ended_ideal_iff (m : ℕ) (hall : ∀ i < m, P.Cont path i) :
    P.Ended (Sum.inl ⟨m, P.ideal path m⟩) ↔ ¬ P.Cont path m := by
  unfold Ended Cont
  constructor
  · rintro (h | ⟨h0, h⟩) ⟨h1, h2⟩
    · exact absurd h1 (not_lt.2 h)
    · have := h2 (m - 1) (by omega)
      rw [P.ideal_apply] at h
      simp only at h
      rw [h] at this
      exact absurd this (lt_irrefl _)
  · intro h
    by_cases hK : P.K ≤ m
    · exact Or.inl hK
    · right
      have hm : (m : ℕ∞) < P.K := not_le.1 hK
      have hnfin : ¬ P.AllFin path m := fun hh => h ⟨hm, hh⟩
      unfold AllFin at hnfin
      push Not at hnfin
      obtain ⟨i, hi, hle⟩ := hnfin
      have hm0 : 0 < m := by omega
      refine ⟨hm0, ?_⟩
      rw [P.ideal_apply]
      have himm : i = m - 1 := by
        by_contra hne
        have : i < m - 1 := by omega
        have := (hall (m - 1) (by omega)).2 i this
        exact absurd hle (not_le.2 this)
      subst himm
      exact top_unique (by simpa using hle)

omit [Fact (0 < β)] in
theorem cycState_char (n : ℕ) :
    ∃ m : ℕ, P.cycState path n = Sum.inl ⟨m, P.ideal path m⟩ ∧ m ≤ n ∧
      (∀ i < m, P.Cont path i) ∧ (m = n ∨ ¬ P.Cont path m) := by
  induction n with
  | zero => exact ⟨0, rfl, le_rfl, fun i hi => absurd hi (by omega), Or.inl rfl⟩
  | succ n ih =>
    obtain ⟨m, hS, hmn, hall, hcase⟩ := ih
    rw [cycState_succ, hS]
    by_cases hE : P.Ended (Sum.inl ⟨m, P.ideal path m⟩)
    · refine ⟨m, ?_, by omega, hall, Or.inr ((ended_ideal_iff P path m hall).1 hE)⟩
      simp only [cycStep, ite_eq_left hE]
    · have hc : P.Cont path m := by
        by_contra hh; exact hE ((ended_ideal_iff P path m hall).2 hh)
      have hmn' : m = n := hcase.resolve_right (not_not.2 hc)
      refine ⟨m + 1, ?_, by omega, ?_, Or.inl (by omega)⟩
      · simp only [cycStep, ite_eq_right hE]
        rfl
      · intro i hi
        rcases Nat.lt_succ_iff_lt_or_eq.1 hi with h | rfl
        · exact hall i h
        · exact hc

open scoped Classical in
omit [Fact (0 < β)] in
/-- The entries of the final record, for any `K`: entry `k` is `E k` iff walk `k` is appended. -/
theorem cycFinal_nth_gen (k : ℕ) :
    (P.cycFinal path).nth k = if P.Cont path k then some (P.E path k) else none := by
  classical
  unfold cycFinal
  by_cases hh : ∃ n, P.Ended (P.cycState path n)
  · rw [dite_eq_left hh]
    obtain ⟨m, hS, -, hall, -⟩ := cycState_char P path (Nat.find hh)
    have hend := Nat.find_spec hh
    rw [hS] at hend
    have hnc : ¬ P.Cont path m := (ended_ideal_iff P path m hall).1 hend
    rw [hS]
    by_cases hk : P.Cont path k
    · have hkm : k < m := by
        by_contra hge
        exact hnc (Cont.anti P path (not_lt.1 hge) hk)
      rw [ite_eq_left hk]
      simp only [CycRec.nth, dite_eq_left hkm]
      congr 1
      exact P.ideal_apply path m ⟨k, hkm⟩
    · rw [ite_eq_right hk]
      have hkm : ¬ k < m := fun h => hk (hall k h)
      simp only [CycRec.nth, dite_eq_right hkm]
  · rw [dite_eq_right hh]
    push Not at hh
    have hstuck : ∀ n, ∃ m, P.cycState path n = Sum.inl ⟨m, P.ideal path m⟩ ∧ m = n := fun n => by
      obtain ⟨m, hS, hmn, hall, hcase⟩ := cycState_char P path n
      rcases hcase with h | hnc
      · exact ⟨m, hS, h⟩
      · exact absurd (hS ▸ (ended_ideal_iff P path m hall).2 hnc) (hh n)
    have hcont : ∀ n, P.Cont path n := fun n => by
      obtain ⟨m, hS, hmn, hall, hcase⟩ := cycState_char P path n
      rcases hcase with rfl | hnc
      · by_contra hnc'
        exact hh m (hS ▸ (ended_ideal_iff P path m hall).2 hnc')
      · exact absurd (hS ▸ (ended_ideal_iff P path m hall).2 hnc) (hh n)
    rw [ite_eq_left (hcont k)]
    obtain ⟨m, hS, hm⟩ := hstuck (k + 1)
    subst hm
    show some ((P.cycState path (k + 1)).nth k |>.getD P.junk) = _
    rw [hS]
    simp only [CycRec.nth, dite_eq_left (Nat.lt_succ_self k), Option.getD_some]
    congr 1
    exact P.ideal_apply path (k + 1) ⟨k, Nat.lt_succ_self k⟩

end CycPlan
end ElboimSly.Cyclic

end

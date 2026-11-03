/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Foundations.Cyclic.CycLines
public import Mathlib

/-!
# The entries of the final record of a plan with infinitely many walks

World-lines of a plan; joint exploration filtration (a), the recursion for the final record, for a plan with `K = ∞`.

`CycPlan.nextEntry` is the world-line appended by one step of the recursion, `CycPlan.ideal` is the
record obtained by always appending, and `CycPlan.E` its `k`-th entry. The final record
`cycFinal` has the entry `E k` at position `k` if and only if all earlier world-lines have finite
length (`cycFinal_nth`).
-/

@[expose] public section

open MeasureTheory Set Filter Topology
open scoped ENNReal NNReal

namespace ElboimSly.Cyclic

variable {I : Type*} [MeasurableSpace I] {d : ℕ} {β : ℝ} [Fact (0 < β)]

namespace CycPlan

variable (P : CycPlan I d β) (path : PathRule I d)

/-- The world-line appended by one step of the recursion. -/
noncomputable def nextEntry (k : ℕ) (ρ : CycRecN I d k) : CycEntry I d :=
  (P.start k ρ, (path k ρ).cut (P.stopLen k ρ (path k ρ)))

/-- The record of the first `k` world-lines if the recursion never stops. -/
noncomputable def ideal : ∀ k : ℕ, CycRecN I d k
  | 0 => Fin.elim0
  | k + 1 => CycRec.snoc (ideal k) (P.nextEntry path k (ideal k))

/-- The `k`-th world-line if the recursion never stops. -/
noncomputable def E (k : ℕ) : CycEntry I d := P.nextEntry path k (P.ideal path k)

omit [Fact (0 < β)] in
theorem ideal_apply : ∀ (k : ℕ) (i : Fin k), P.ideal path k i = P.E path i
  | 0, i => i.elim0
  | k + 1, i => by
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simp [ideal, CycRec.snoc, E]
    · simp only [ideal, CycRec.snoc, Fin.snoc_castSucc]
      exact ideal_apply k j

/-- All world-lines before the `n`-th one have finite length. -/
def AllFin (n : ℕ) : Prop := ∀ i < n, (P.E path i).len < ⊤

omit [Fact (0 < β)] in
theorem state_inv (hK : P.K = ⊤) (n : ℕ) :
    ∃ (m : ℕ) (f : CycRecN I d m), P.cycState path n = Sum.inl ⟨m, f⟩ ∧
      (∀ i : Fin m, f i = P.E path i) ∧
      ((P.AllFin path n ∧ m = n) ∨
        (∃ L, L < n ∧ (P.E path L).len = ⊤ ∧ (∀ i < L, (P.E path i).len < ⊤) ∧ m = L + 1)) := by
  induction n with
  | zero =>
    refine ⟨0, Fin.elim0, rfl, fun i => i.elim0, Or.inl ⟨fun i hi => absurd hi (by omega), rfl⟩⟩
  | succ n ih =>
    obtain ⟨m, f, hS, hf, hcase⟩ := ih
    have hstate : P.cycState path (n + 1) = P.cycStep path (P.cycState path n) := by
      simp only [cycState, Function.iterate_succ_apply']
    rcases hcase with ⟨hfin, rfl⟩ | ⟨L, hL, hLinf, hLfin, rfl⟩
    · have hnend : ¬ P.Ended (Sum.inl ⟨m, f⟩) := by
        rintro (h | ⟨h0, h⟩)
        · simp [hK] at h
        · have := hfin (m - 1) (by omega)
          rw [hf ⟨m - 1, by omega⟩] at h
          simp only at h
          rw [h] at this
          exact absurd this (lt_irrefl _)
      have hfeq : f = P.ideal path m := funext fun i => (hf i).trans (P.ideal_apply path m i).symm
      refine ⟨m + 1, CycRec.snoc f (P.nextEntry path m f), ?_, ?_, ?_⟩
      · rw [hstate, hS, cycStep, ite_eq_right hnend]; rfl
      · intro i
        refine Fin.lastCases ?_ (fun j => ?_) i
        · simp only [CycRec.snoc, Fin.snoc_last, E, nextEntry]
          rw [hfeq]; rfl
        · simp only [CycRec.snoc, Fin.snoc_castSucc]
          exact hf j
      · by_cases hE : (P.E path m).len < ⊤
        · exact Or.inl ⟨fun i hi => by
            rcases Nat.lt_succ_iff_lt_or_eq.1 hi with h | h
            · exact hfin i h
            · rw [h]; exact hE, rfl⟩
        · refine Or.inr ⟨m, by omega, ?_, hfin, rfl⟩
          exact top_unique (not_lt.1 hE)
    · have hend : P.Ended (Sum.inl ⟨L + 1, f⟩) := by
        refine Or.inr ⟨by omega, ?_⟩
        rw [hf ⟨L + 1 - 1, by omega⟩]
        simpa using hLinf
      refine ⟨L + 1, f, ?_, hf, Or.inr ⟨L, by omega, hLinf, hLfin, rfl⟩⟩
      rw [hstate, hS, cycStep, ite_eq_left hend]

omit [Fact (0 < β)] in
theorem not_ended_of_allFin (hK : P.K = ⊤) {m : ℕ} {f : CycRecN I d m}
    (hf : ∀ i : Fin m, f i = P.E path i) (hfin : P.AllFin path m) :
    ¬ P.Ended (Sum.inl ⟨m, f⟩) := by
  rintro (h | ⟨h0, h⟩)
  · simp [hK] at h
  · have := hfin (m - 1) (by omega)
    rw [hf ⟨m - 1, by omega⟩] at h
    simp only at h
    rw [h] at this
    exact absurd this (lt_irrefl _)

open scoped Classical in
omit [Fact (0 < β)] in
/-- The entries of the final record of a plan with `K = ∞`: the entry `E k` is present iff all
earlier world-lines have finite length. -/
theorem cycFinal_nth (hK : P.K = ⊤) (k : ℕ) :
    (P.cycFinal path).nth k = if P.AllFin path k then some (P.E path k) else none := by
  classical
  unfold cycFinal
  by_cases hh : ∃ n, P.Ended (P.cycState path n)
  · rw [dite_eq_left hh]
    obtain ⟨m, f, hS, hf, hcase⟩ := P.state_inv path hK (Nat.find hh)
    have hend := Nat.find_spec hh
    rw [hS] at hend
    rcases hcase with ⟨hfin, rfl⟩ | ⟨L, hL, hLinf, hLfin, rfl⟩
    · exact absurd hend (P.not_ended_of_allFin path hK hf hfin)
    · rw [hS]
      by_cases hk : k < L + 1
      · have hA : P.AllFin path k := fun i hi => hLfin i (by omega)
        rw [ite_eq_left hA]
        simp only [CycRec.nth, dite_eq_left hk, hf]
      · have hA : ¬ P.AllFin path k := fun h => by
          have := h L (by omega)
          rw [hLinf] at this
          exact lt_irrefl _ this
        rw [ite_eq_right hA]
        simp only [CycRec.nth, dite_eq_right hk]
  · rw [dite_eq_right hh]
    push Not at hh
    have hcase : ∀ n, P.AllFin path n := fun n => by
      obtain ⟨m, f, hS, hf, hc⟩ := P.state_inv path hK n
      rcases hc with ⟨hfin, -⟩ | ⟨L, hL, hLinf, hLfin, rfl⟩
      · exact hfin
      · exfalso
        refine hh n ?_
        rw [hS]
        refine Or.inr ⟨by omega, ?_⟩
        rw [hf ⟨L + 1 - 1, by omega⟩]
        simpa using hLinf
    rw [ite_eq_left (hcase k)]
    obtain ⟨m, f, hS, hf, hc⟩ := P.state_inv path hK (k + 1)
    have hm : m = k + 1 := by
      rcases hc with ⟨-, h⟩ | ⟨L, hL, hLinf, hLfin, rfl⟩
      · exact h
      · exfalso
        have := hcase (k + 1) (L) hL
        rw [hLinf] at this
        exact lt_irrefl _ this
    subst hm
    simp only [CycRec.nth, hS, dite_eq_left (Nat.lt_succ_self k), hf, Option.getD_some]

end CycPlan

end ElboimSly.Cyclic

end

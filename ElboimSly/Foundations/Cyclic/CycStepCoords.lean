/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Foundations.Cyclic.CycLines
public import ElboimSly.Foundations.Cyclic.CycRecCoords
public import ElboimSly.Foundations.Cyclic.CycRecMeasStop
public import Mathlib

/-!
# Coordinates of one step of the recursion

Measurability of record functionals (d), auxiliary. `num` and `coord` of `cycStep`.
-/

@[expose] public section

open MeasureTheory Set Filter Topology
open scoped ENNReal NNReal

namespace ElboimSly.Cyclic

variable {I : Type*} [MeasurableSpace I] {d : ℕ} {β : ℝ} [Fact (0 < β)]

namespace CycPlan

variable (P : CycPlan I d β)

/-- The entry appended by `cycStep` to a finite record. -/
noncomputable def newEntry (path : PathRule I d) : CycRec I d → CycEntry I d
  | Sum.inl ⟨k, f⟩ => (P.start k f, (path k f).cut (P.stopLen k f (path k f)))
  | Sum.inr _ => P.junk

open scoped Classical in
omit [Fact (0 < β)] in
theorem num_cycStep (path : PathRule I d) (ρ : CycRec I d) :
    (P.cycStep path ρ).num = if P.Ended ρ then ρ.num else ρ.num + 1 := by
  rcases ρ with ⟨k, f⟩ | f
  · unfold cycStep
    by_cases h : P.Ended (Sum.inl ⟨k, f⟩) <;> simp [h, CycRec.num]
  · simp [cycStep, Ended, CycRec.num]

open scoped Classical in
omit [Fact (0 < β)] in
theorem coord_cycStep (path : PathRule I d) (ρ : CycRec I d) (j : ℕ) :
    (P.cycStep path ρ).coord P.junk j =
      if ¬ P.Ended ρ ∧ (j : ℕ∞) = ρ.num then P.newEntry path ρ else ρ.coord P.junk j := by
  rcases ρ with ⟨k, f⟩ | f
  · by_cases h : P.Ended (Sum.inl ⟨k, f⟩)
    · simp [cycStep, h]
    · simp only [cycStep, h, ite_false, CycRec.coord, CycRec.nth, CycRec.num, CycRec.snoc,
        not_false_eq_true, true_and, Nat.cast_inj]
      rcases lt_trichotomy j k with hj | hj | hj
      · have h1 : j < k + 1 := by omega
        simp only [h1, hj, dite_true, Option.getD_some, ne_of_lt hj, ite_false]
        have := Fin.snoc_castSucc (α := fun _ => CycEntry I d) (P.newEntry path (Sum.inl ⟨k, f⟩))
          f ⟨j, hj⟩
        simpa [newEntry] using this
      · subst hj
        simp only [lt_add_iff_pos_right, dite_true, Option.getD_some, ite_true,
          newEntry, Nat.lt_irrefl, dite_false, Option.getD_none, zero_lt_one]
        exact Fin.snoc_last (α := fun _ => CycEntry I d) _ _
      · have h1 : ¬ j < k + 1 := by omega
        simp [h1, hj.ne', not_lt.mpr hj.le]
  · simp [cycStep, Ended, CycRec.coord, CycRec.nth, CycRec.num]

omit [Fact (0 < β)] in
theorem measurableSet_ended : MeasurableSet {ρ : CycRec I d | P.Ended ρ} := by
  classical
  rw [measurableSet_sum_iff]
  refine ⟨MeasurableSpace.measurableSet_iInf.mpr fun k => ?_, ?_⟩
  · show MeasurableSet {f : Fin k → CycEntry I d | P.Ended (Sum.inl ⟨k, f⟩)}
    by_cases hK : P.K ≤ k
    · have : {f : Fin k → CycEntry I d | P.Ended (Sum.inl ⟨k, f⟩)} = univ := by
        ext f; simp [Ended, hK]
      rw [this]; exact MeasurableSet.univ
    · by_cases hk : 0 < k
      · have : {f : Fin k → CycEntry I d | P.Ended (Sum.inl ⟨k, f⟩)} =
            {f | (f ⟨k - 1, by omega⟩).len = ⊤} := by
          ext f; simp [Ended, hK, hk]
        rw [this]
        have hm : Measurable fun f : Fin k → CycEntry I d => (f ⟨k - 1, by omega⟩).len :=
          (CPath.measurable_len.comp (measurable_subtype_coe.comp measurable_snd)).comp
            (measurable_pi_apply _)
        exact hm (measurableSet_singleton _)
      · have : {f : Fin k → CycEntry I d | P.Ended (Sum.inl ⟨k, f⟩)} = ∅ := by
          ext f; simp [Ended, hK, hk]
        rw [this]; exact MeasurableSet.empty
  · have : Sum.inr ⁻¹' {ρ : CycRec I d | P.Ended ρ} = univ := by ext; simp [Ended]
    rw [this]; exact MeasurableSet.univ

section meas

variable {α : Type*} [MeasurableSpace α] {path : α → PathRule I d}
  (hpath : ∀ k, Measurable fun q : α × CycRecN I d k => path q.1 k q.2)
  {g : α → CycRec I d} (hg : Measurable g)
include hpath hg

omit [Fact (0 < β)] in
theorem measurable_newEntry : Measurable fun a => P.newEntry (path a) (g a) := by
  have hfk : ∀ k, Measurable fun a => fun i : Fin k => (g a).coord P.junk i := fun k =>
    measurable_pi_iff.mpr fun i => (CycRec.measurable_coord P.junk i).comp hg
  refine measurable_dispatch (F := fun k a => (P.start k (fun i : Fin k => (g a).coord P.junk i),
      (path a k (fun i : Fin k => (g a).coord P.junk i)).cut
        (P.stopLen k (fun i : Fin k => (g a).coord P.junk i)
          (path a k (fun i : Fin k => (g a).coord P.junk i))))) (num := fun a => (g a).num)
    (CycRec.measurable_num.comp hg) (fun k => ?_) P.junk (fun a => ?_)
  · have hp : Measurable fun a => path a k (fun i : Fin k => (g a).coord P.junk i) :=
      (hpath k).comp (measurable_id.prodMk (hfk k))
    exact ((P.measurable_start k).comp (hfk k)).prodMk
      (measurable_cycPath_cut.comp (hp.prodMk ((P.measurable_stopLen k).comp
        ((hfk k).prodMk hp))))
  · by_cases h : (g a).num = ⊤
    · rw [ite_eq_left h, CycRec.eq_inr_of_num (junk := P.junk) h]; rfl
    · rw [ite_eq_right h]
      obtain ⟨k, hk⟩ := ENat.ne_top_iff_exists.mp h
      have h' : (g a).num = (k : ℕ∞) := hk.symm
      rw [← hk, ENat.toNat_natCast]
      conv_lhs => rw [CycRec.eq_inl_of_num (junk := P.junk) h']
      rfl

open scoped Classical in
omit [Fact (0 < β)] in
theorem measurable_cycStep : Measurable fun a => P.cycStep (path a) (g a) := by
  have hend : MeasurableSet {a | P.Ended (g a)} := hg (P.measurableSet_ended)
  refine measurable_cycRec_of_coords _ P.junk ?_ fun j => ?_
  · have : (fun a => (P.cycStep (path a) (g a)).num) =
        fun a => if P.Ended (g a) then (g a).num else (g a).num + 1 := funext fun a =>
      P.num_cycStep (path a) (g a)
    rw [this]
    refine Measurable.ite hend (CycRec.measurable_num.comp hg) ?_
    exact (measurable_from_top (f := fun x : ℕ∞ => x + 1)).comp (CycRec.measurable_num.comp hg)
  · have : (fun a => (P.cycStep (path a) (g a)).coord P.junk j) =
        fun a => if ¬ P.Ended (g a) ∧ (j : ℕ∞) = (g a).num then P.newEntry (path a) (g a)
          else (g a).coord P.junk j := funext fun a => P.coord_cycStep (path a) (g a) j
    rw [this]
    have hj : MeasurableSet {a | (j : ℕ∞) = (g a).num} := by
      have := (CycRec.measurable_num.comp hg) (measurableSet_singleton (j : ℕ∞))
      convert this using 1
      ext a; simp [eq_comm]
    exact Measurable.ite (hend.compl.inter hj) (P.measurable_newEntry hpath hg)
      ((CycRec.measurable_coord P.junk j).comp hg)

end meas

section meas2

variable {α : Type*} [MeasurableSpace α] {path : α → PathRule I d}
  (hpath : ∀ k, Measurable fun q : α × CycRecN I d k => path q.1 k q.2)
include hpath

omit [Fact (0 < β)] in
theorem measurable_cycState (n : ℕ) : Measurable fun a => P.cycState (path a) n := by
  induction n with
  | zero => exact measurable_const
  | succ n ih =>
    have := P.measurable_cycStep hpath ih
    simpa [CycPlan.cycState, Function.iterate_succ_apply'] using this

open scoped Classical in
omit [Fact (0 < β)] in
/-- Measurability of record functionals (d), the recursion: the final record is measurable in the
parameter, for any measurable family of path rules. -/
theorem measurable_cycFinal : Measurable fun a => P.cycFinal (path a) := by
  have hS := P.measurable_cycState hpath
  have hend : ∀ n, MeasurableSet {a | P.Ended (P.cycState (path a) n)} := fun n =>
    (hS n) (P.measurableSet_ended)
  let N : α → ℕ := fun a => if h : ∃ n, P.Ended (P.cycState (path a) n) then Nat.find h else 0
  have hex : MeasurableSet {a | ∃ n, P.Ended (P.cycState (path a) n)} := by
    have : {a | ∃ n, P.Ended (P.cycState (path a) n)} =
        ⋃ n, {a | P.Ended (P.cycState (path a) n)} := by ext; simp
    rw [this]; exact MeasurableSet.iUnion hend
  have hN : ∀ n, MeasurableSet {a | N a = n} := fun n => by
    have : {a | N a = n} = ({a | P.Ended (P.cycState (path a) n)} ∩
        ⋂ m ∈ Finset.range n, {a | P.Ended (P.cycState (path a) m)}ᶜ) ∪
        ({a | ∃ n, P.Ended (P.cycState (path a) n)}ᶜ ∩ {_a | n = 0}) := by
      ext a
      simp only [N, mem_ofPred_eq, mem_union, mem_inter_iff, mem_iInter, Finset.mem_range,
        mem_compl_iff]
      by_cases h : ∃ n, P.Ended (P.cycState (path a) n)
      · simp only [h, dite_true, not_true_eq_false, false_and, or_false]
        rw [Nat.find_eq_iff]
      · simp only [h, dite_false, not_false_eq_true, true_and]
        constructor
        · intro h0; right; exact h0.symm
        · rintro (⟨h1, -⟩ | h2)
          · exact absurd ⟨n, h1⟩ h
          · exact h2.symm
    rw [this]
    refine ((hend n).inter (MeasurableSet.biInter (Finset.range n).countable_toSet
      fun m _ => (hend m).compl)).union (hex.compl.inter (MeasurableSet.const _))
  have hG : Measurable fun a => P.cycState (path a) (N a) := by
    intro B hB
    have : (fun a => P.cycState (path a) (N a)) ⁻¹' B = ⋃ n, ({a | N a = n} ∩
        (fun a => P.cycState (path a) n) ⁻¹' B) := by
      ext a; simp
    rw [this]
    exact MeasurableSet.iUnion fun n => (hN n).inter (hS n hB)
  have hinf : Measurable fun a => (Sum.inr fun k : ℕ =>
      (P.cycState (path a) (k + 1)).coord P.junk k : CycRec I d) :=
    measurable_inr.comp (measurable_pi_iff.mpr fun k =>
      (CycRec.measurable_coord P.junk k).comp (hS (k + 1)))
  have : (fun a => P.cycFinal (path a)) = fun a =>
      if ∃ n, P.Ended (P.cycState (path a) n) then P.cycState (path a) (N a)
      else (Sum.inr fun k : ℕ => (P.cycState (path a) (k + 1)).coord P.junk k : CycRec I d) := by
    funext a
    unfold CycPlan.cycFinal
    by_cases h : ∃ n, P.Ended (P.cycState (path a) n)
    · simp [h, N]
    · simp [h, CycRec.coord]
  rw [this]
  exact Measurable.ite hex hG hinf

end meas2

end CycPlan

end ElboimSly.Cyclic

end

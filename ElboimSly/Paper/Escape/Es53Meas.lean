/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Paper.Escape.Es53Region
public import ElboimSly.Paper.Escape.Es53Events
public import ElboimSly.Foundations.Cyclic.CycMultiMain
public import ElboimSly.Foundations.Cyclic.CycRecCoords
public import Mathlib

/-!
# The set `A` as a function of the record at `Λ_{i-1}`

ES22 Lemma 5.3, "the `𝒢_{i-1}`-measurable set `A = {0} ∪ A'`".  `A'` is read off the record
`cycRec(Λ_m)`: `visPred` is its countable form, and `escA_iff` identifies it with
`{0} ∪ escVisNbr`, so that `{ω | z ∈ A(ω)}` is measurable for the stopped σ-algebra.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal

namespace ElboimSly.Paper.Escape

open ElboimSly ElboimSly.Cyclic ElboimSly.Paper

variable {k : ℕ} {β : ℝ} [Fact (0 < β)] {n : ℕ} {u : Fin (k + 2) → ℤ} {b : ℕ}
  {hlog : 1 < Real.log β}

section qset

variable {α : Type*} [MeasurableSpace α]

theorem measurableSet_exists_qSet' {T : α → ℝ≥0} (hT : Measurable T) {P : α → ℝ≥0 → Prop}
    (hP : ∀ f : α → ℝ≥0, Measurable f → MeasurableSet {a | P a (f a)}) :
    MeasurableSet {a | ∃ q ∈ qSet 0 (T a), P a q} := by
  have : {a | ∃ q ∈ qSet 0 (T a), P a q} =
      (⋃ r : ℚ, ⋃ (_ : (0 : ℝ) ≤ r), {a | Real.toNNReal r ≤ T a} ∩ {a | P a (Real.toNNReal r)}) ∪
        {a | P a (T a)} := by
    ext a
    simp only [mem_ofPred_eq, mem_union, mem_iUnion, mem_inter_iff, exists_prop]
    constructor
    · rintro ⟨q, hq, hPq⟩
      rcases hq with ⟨-, hqT, r, hr⟩ | rfl
      · left
        have hr0 : (0 : ℝ) ≤ r := by rw [← hr]; exact q.2
        have hqr : q = Real.toNNReal r := by
          rw [← NNReal.coe_inj, Real.coe_toNNReal _ hr0, hr]
        exact ⟨r, hr0, hqr ▸ hqT, hqr ▸ hPq⟩
      · right; exact hPq
    · rintro (⟨r, hr0, hrT, hPr⟩ | h)
      · refine ⟨Real.toNNReal r, Or.inl ⟨bot_le, hrT, r, ?_⟩, hPr⟩
        rw [Real.coe_toNNReal _ hr0]
      · exact ⟨T a, Or.inr rfl, h⟩
  rw [this]
  refine MeasurableSet.union (MeasurableSet.iUnion fun r => MeasurableSet.iUnion fun _ => ?_) ?_
  · refine MeasurableSet.inter ?_ ?_
    · exact measurableSet_le measurable_const hT
    · exact hP (fun _ => Real.toNNReal r) measurable_const
  · exact hP T hT

end qset

/-- The vertices visited by an entry up to its length, seen at test times. -/
def escEntryVis (e : CycEntry ℕ (k + 2)) (y : Fin (k + 2) → ℤ) : Prop :=
  ∃ s ∈ qSet 0 e.len.toNNReal, e.path.fn s = y

theorem measurableSet_escEntryVis (y : Fin (k + 2) → ℤ) :
    MeasurableSet {e : CycEntry ℕ (k + 2) | escEntryVis e y} := by
  refine measurableSet_exists_qSet' (T := fun e : CycEntry ℕ (k + 2) => e.len.toNNReal)
    (ENNReal.measurable_toNNReal.comp measurable_entry_len) (P := fun e s => e.path.fn s = y) ?_
  intro f hf
  exact (measurable_fn_at (fun e : CycEntry ℕ (k + 2) => e.path) measurable_entry_path f hf)
    (measurableSet_singleton y)

theorem escEntryVis_iff {e : CycEntry ℕ (k + 2)} (hlen : e.len ≠ ⊤) (y : Fin (k + 2) → ℤ) :
    escEntryVis e y ↔ ∃ s : ℝ≥0, (s : ℝ≥0∞) ≤ e.len ∧ e.path.fn s = y := by
  constructor
  · rintro ⟨s, hs, hsy⟩
    refine ⟨s, ?_, hsy⟩
    have := (mem_qSet_Icc bot_le hs).2
    rw [← ENNReal.coe_toNNReal hlen]
    exact_mod_cast this
  · rintro ⟨s, hs, hsy⟩
    have hs' : s ≤ e.len.toNNReal := by
      rw [← ENNReal.coe_le_coe, ENNReal.coe_toNNReal hlen]; exact hs
    obtain ⟨q, hq, hqe⟩ := exists_qSet (x := e.path.fn) (a := 0) (fun t => e.path.rc t)
      bot_le hs'
    exact ⟨q, hq, hqe.trans hsy⟩

/-- The countable form of `A'` read off a record with `m` complete earlier entries. -/
def visPred (m : ℕ) (junk : CycEntry ℕ (k + 2)) (ρ : CycRec ℕ (k + 2))
    (z : Fin (k + 2) → ℤ) : Prop :=
  ∃ j : ℕ, j < m ∧ ∃ y, escEntryVis (ρ.coord junk j) y ∧ ‖z - y‖ ≤ 1

theorem measurableSet_visPred (m : ℕ) (junk : CycEntry ℕ (k + 2)) (z : Fin (k + 2) → ℤ) :
    MeasurableSet {ρ : CycRec ℕ (k + 2) | visPred m junk ρ z} := by
  have : {ρ : CycRec ℕ (k + 2) | visPred m junk ρ z} =
      ⋃ j ∈ Finset.range m, ⋃ y : Fin (k + 2) → ℤ,
        {ρ | escEntryVis (ρ.coord junk j) y} ∩ {_ρ | ‖z - y‖ ≤ 1} := by
    ext ρ; simp [visPred]
  rw [this]
  refine MeasurableSet.biUnion (Finset.countable_toSet _) fun j _ =>
    MeasurableSet.iUnion fun y => MeasurableSet.inter ?_ (MeasurableSet.const _)
  exact (measurableSet_escEntryVis y).preimage (CycRec.measurable_coord junk j)

/-- The set `A = {0} ∪ A'`. -/
def escA (n : ℕ) (u : Fin (k + 2) → ℤ) (b : ℕ) (hlog : 1 < Real.log β) {Ω : Type*}
    (N : Ω → Measure (CycS ℕ (k + 2) β)) (m : ℕ) (ω : Ω) : Set (Fin (k + 2) → ℤ) :=
  {0} ∪ escVisNbr n u b hlog (cycNgood N ω) m

theorem recT_coord {Ω : Type*} (N : Ω → Measure (CycS ℕ (k + 2) β)) {m : ℕ}
    (hm : m < escIstar n (escJ n)) (ω : Ω) {j : ℕ} (hj : j < m) :
    (cycRecStop (planA n β u b hlog) (cycNgood N) (escLam n u b hlog N m) ω).coord
      (planA n β u b hlog).junk j = escEntry n u b hlog (cycNgood N ω) j := by
  set ν := cycNgood N ω with hν
  set R := (planA n β u b hlog).envFinal ν with hR
  have hs : ElboimSly.SRW.stopReal (escLam n u b hlog N m) ω = (R.cum m).toNNReal := rfl
  unfold cycRecStop
  rw [hs]
  have hjI : j < escIstar n (escJ n) := hj.trans hm
  obtain ⟨mm, hmm, hiff, hcoord, -⟩ := CycRec.trunc_spec (planA n β u b hlog).junk
    (R.cum m).toNNReal R
  have hfin : R.cum m ≠ ⊤ := cum_envFinal_ne_top ν hm.le
  have hsurv : j ∈ R.surv (R.cum m).toNNReal := by
    refine ⟨?_, ?_⟩
    · rw [num_envFinal]; exact_mod_cast hjI
    · rw [ENNReal.coe_toNNReal hfin]
      exact CycRec.cum_mono R hj.le
  rw [hcoord j hsurv]
  unfold CycRec.truncEntry
  have hc : R.cum (j + 1) ≤ ((R.cum m).toNNReal : ℝ≥0∞) := by
    rw [ENNReal.coe_toNNReal hfin]; exact CycRec.cum_mono R hj
  rw [ite_eq_left hc]
  unfold CycRec.coord
  rw [envFinal_nth, ite_eq_left hjI]; rfl

theorem escA_iff {Ω : Type*} (N : Ω → Measure (CycS ℕ (k + 2) β)) {m : ℕ}
    (hm : m < escIstar n (escJ n)) (ω : Ω) (z : Fin (k + 2) → ℤ) :
    z ∈ escA n u b hlog N m ω ↔ z = 0 ∨ visPred m (planA n β u b hlog).junk
      (cycRecStop (planA n β u b hlog) (cycNgood N) (escLam n u b hlog N m) ω) z := by
  unfold escA
  simp only [mem_union, mem_singleton_iff]
  refine or_congr Iff.rfl ?_
  constructor
  · rintro ⟨j, hj, s, hs, hz⟩
    refine ⟨j, hj, (escEntry n u b hlog (cycNgood N ω) j).path.fn s, ?_, hz⟩
    rw [recT_coord N hm ω hj]
    exact (escEntryVis_iff (escEntry_len_ne_top j) _).2 ⟨s, hs, rfl⟩
  · rintro ⟨j, hj, y, hy, hz⟩
    rw [recT_coord N hm ω hj] at hy
    obtain ⟨s, hs, hsy⟩ := (escEntryVis_iff (escEntry_len_ne_top j) y).1 hy
    exact ⟨j, hj, s, hs, by rw [hsy]; exact hz⟩

end ElboimSly.Paper.Escape

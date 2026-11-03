/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Foundations.Cyclic.CycRingPiece
public import Mathlib

/-!
# Measurability of record functionals (a), part 3: the ring measure as a first-occurrence sum

The known rings of a record are the points `ringPt (coord k) a` over the valid indices
`n = ⟨k, a⟩` (`Nat.unpair`). Counting each point once is the sum over the *first occurrences*,
which is the written proof's formula for `RM(ρ)(B)`.
-/

@[expose] public section

open MeasureTheory Set Filter Topology
open scoped ENNReal NNReal

namespace ElboimSly.Cyclic

variable {I : Type*} [MeasurableSpace I] {d : ℕ} {β : ℝ} [Fact (0 < β)]

namespace CycRec

/-- Index `n = ⟨k, a⟩` is a valid ring index of `ρ`: entry `k` exists and has a jump `a + 1`. -/
def ringIdx (junk : CycEntry I d) (ρ : CycRec I d) (n : ℕ) : Prop :=
  ((Nat.unpair n).1 : ℕ∞) < ρ.num ∧ ringValid (ρ.coord junk (Nat.unpair n).1) (Nat.unpair n).2

/-- The ring at index `n`. -/
noncomputable def ringAt (e0 : Edge d) (junk : CycEntry I d) (ρ : CycRec I d) (n : ℕ) :
    I × RingSpace d β :=
  ringPt e0 (ρ.coord junk (Nat.unpair n).1) (Nat.unpair n).2

/-- The index `n` is the first valid index with its point. -/
def ringFirst (e0 : Edge d) (junk : CycEntry I d) (ρ : CycRec I d) (n : ℕ) : Prop :=
  ρ.ringIdx junk n ∧ ∀ m < n, ¬ (ρ.ringIdx junk m ∧
    ρ.ringAt (β := β) e0 junk m = ρ.ringAt (β := β) e0 junk n)

omit [MeasurableSpace I] in
theorem exists_entry_iff (junk : CycEntry I d) (ρ : CycRec I d) (P : CycEntry I d → Prop) :
    (∃ e, ρ.IsEntry e ∧ P e) ↔ ∃ j : ℕ, (j : ℕ∞) < ρ.num ∧ P (ρ.coord junk j) := by
  constructor
  · rintro ⟨e, ⟨j, hj⟩, hx⟩
    have hlt : (j : ℕ∞) < ρ.num := by
      rcases ρ with ⟨n, f⟩ | f
      · simp only [CycRec.nth] at hj
        split_ifs at hj with h
        · simpa [CycRec.num] using h
      · simp [CycRec.num]
    refine ⟨j, hlt, ?_⟩
    simp only [CycRec.coord, hj, Option.getD_some]
    exact hx
  · rintro ⟨j, hlt, hx⟩
    refine ⟨ρ.coord junk j, ⟨j, ?_⟩, hx⟩
    rcases ρ with ⟨n, f⟩ | f
    · have h : j < n := by simpa [CycRec.num] using hlt
      simp [CycRec.nth, CycRec.coord, h]
    · simp [CycRec.nth, CycRec.coord]

omit [MeasurableSpace I] [Fact (0 < β)] in
theorem mem_ringSet_iff (e0 : Edge d) (junk : CycEntry I d) (ρ : CycRec I d)
    (x : I × RingSpace d β) :
    x ∈ ρ.ringSet β ↔ ∃ n, ρ.ringIdx junk n ∧ x = ρ.ringAt e0 junk n := by
  unfold CycRec.ringSet
  simp only [mem_ofPred_eq]
  rw [exists_entry_iff junk ρ (fun e => x ∈ e.ringSet β)]
  constructor
  · rintro ⟨j, hj, hx⟩
    obtain ⟨a, ha, hxa⟩ := (CycEntry.mem_ringSet_iff e0 _ x).mp hx
    refine ⟨Nat.pair j a, ?_, ?_⟩
    · simp [ringIdx, hj, ha]
    · simp [ringAt, hxa]
  · rintro ⟨n, ⟨hj, ha⟩, hx⟩
    exact ⟨_, hj, (CycEntry.mem_ringSet_iff e0 _ x).mpr ⟨_, ha, hx⟩⟩

section Count

variable [MeasurableSingletonClass I]

omit [MeasurableSingletonClass I] in
omit [MeasurableSpace I] [Fact (0 < β)] in
theorem ringSet_countable (e0 : Edge d) (junk : CycEntry I d) (ρ : CycRec I d) :
    (ρ.ringSet β).Countable := by
  refine (Set.countable_range (fun n => ρ.ringAt (β := β) e0 junk n)).mono ?_
  intro x hx
  obtain ⟨n, -, hn⟩ := (mem_ringSet_iff e0 junk ρ x).mp hx
  exact ⟨n, hn.symm⟩

open scoped Classical in
omit [Fact (0 < β)] in
/-- The first-occurrence formula for the ring measure. Measurability of record functionals (a). -/
theorem rm_apply_eq_tsum [Countable I] (e0 : Edge d) (junk : CycEntry I d) (ρ : CycRec I d)
    {B : Set (I × RingSpace d β)} (hB : MeasurableSet B) :
    ρ.rm β B = ∑' n, if ρ.ringFirst (β := β) e0 junk n ∧ ρ.ringAt e0 junk n ∈ B then (1 : ℝ≥0∞) else 0 := by
  have hcount : (B ∩ ρ.ringSet β).Countable := (ringSet_countable e0 junk ρ).mono inter_subset_right
  rw [CycRec.rm, Measure.restrict_apply hB, Measure.count_apply (hcount.measurableSet)]
  set F : Set ℕ := {n | ρ.ringFirst (β := β) e0 junk n ∧ ρ.ringAt (β := β) e0 junk n ∈ B} with hF
  have himg : B ∩ ρ.ringSet β = (fun n => ρ.ringAt (β := β) e0 junk n) '' F := by
    ext x
    constructor
    · rintro ⟨hxB, hxS⟩
      obtain ⟨n, hn, hx⟩ := (mem_ringSet_iff e0 junk ρ x).mp hxS
      have hex : ∃ m, ρ.ringIdx junk m ∧ ρ.ringAt (β := β) e0 junk m = x := ⟨n, hn, hx.symm⟩
      refine ⟨Nat.find hex, ⟨⟨(Nat.find_spec hex).1, fun m hm hm' => ?_⟩, ?_⟩, (Nat.find_spec hex).2⟩
      · exact Nat.find_min hex hm ⟨hm'.1, hm'.2.trans (Nat.find_spec hex).2⟩
      · rw [(Nat.find_spec hex).2]; exact hxB
    · rintro ⟨n, ⟨hfirst, hnB⟩, rfl⟩
      exact ⟨hnB, (mem_ringSet_iff e0 junk ρ _).mpr ⟨n, hfirst.1, rfl⟩⟩
  have hinj : Set.InjOn (fun n => ρ.ringAt (β := β) e0 junk n) F := by
    intro n hn m hm hnm
    by_contra hne
    rcases lt_or_gt_of_ne hne with h | h
    · exact hm.1.2 n h ⟨hn.1.1, hnm⟩
    · exact hn.1.2 m h ⟨hm.1.1, hnm.symm⟩
  rw [himg, hinj.encard_image]
  have : (∑' n, if ρ.ringFirst (β := β) e0 junk n ∧ ρ.ringAt e0 junk n ∈ B then (1 : ℝ≥0∞) else 0) =
      ∑' n, F.indicator (1 : ℕ → ℝ≥0∞) n := by
    congr 1; funext n
    by_cases h : n ∈ F
    · rw [Set.indicator_of_mem h]; simp only [Pi.one_apply]
      exact ite_eq_left h
    · rw [Set.indicator_of_notMem h]
      exact ite_eq_right h
  rw [this, ← tsum_subtype F (1 : ℕ → ℝ≥0∞)]
  exact (ENNReal.tsum_set_one F).symm

end Count

end CycRec

end ElboimSly.Cyclic

end

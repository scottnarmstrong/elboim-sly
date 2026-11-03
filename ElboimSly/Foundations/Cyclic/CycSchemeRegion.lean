/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Foundations.Cyclic.CycSchemeDef
public import Mathlib

/-!
# The explored region along the scheme: record side

The environment scheme (a), the explored-region identity, record side.

For a state with a finite non-empty record whose last entry has finite length (`CycScheme.WF`, true
at `init` and preserved by `upd`), the region of the updated record is the old region together with
the *front region* `CycEntry.frontReg E s* = {(ι, e, c_δ(r + t)) : e ∋ w, t ∈ (0, s*]}`
(`CycScheme.region_upd`). The probe side is in `CycSchemeRegionProbe`.
-/

@[expose] public section

open MeasureTheory Set Filter Topology
open scoped ENNReal NNReal

namespace ElboimSly.Cyclic

variable {I : Type*} [MeasurableSpace I] {d : ℕ} {β : ℝ} [Fact (0 < β)]

namespace CycEntry

/-- The front points `(ι, e, c_δ(r + t))`, `e ∋ w`, `t ∈ (0, s]`, of the current walk. -/
def frontReg (β : ℝ) (E : CycEntry I d) (s : ℝ≥0) : Set (I × RingSpace d β) :=
  {x | ∃ t : ℝ≥0, 0 < t ∧ t ≤ s ∧ x.1 = E.data.copy ∧
    x.2.2 = E.data.clock β (E.time + t) ∧ Edge.Mem E.pos x.2.1}

omit [MeasurableSpace I] in
theorem len_eq_time {E : CycEntry I d} (h : E.len ≠ ⊤) : E.len = (E.time : ℝ≥0∞) := by
  unfold time
  exact (ENNReal.coe_toNNReal h).symm

omit [MeasurableSpace I] in
theorem path_fn_eq_pos {E : CycEntry I d} (h : E.len ≠ ⊤) {u : ℝ≥0} (hu : E.time ≤ u) :
    E.path.fn u = E.pos := by
  have hl := len_eq_time h
  unfold pos
  refine E.path.const _ _ (hl.le.trans ?_) hl.le
  exact_mod_cast hu

omit [Fact (0 < β)] in
omit [MeasurableSpace I] in
/-- The path extended at `time + s`: the new entry has region `region ∪ frontReg`. -/
theorem region_extend {E : CycEntry I d} (h : E.len ≠ ⊤) (s : ℝ≥0) (v : Fin d → ℤ) :
    CycEntry.region β ((E.data, E.2.extend (E.time + s) v) : CycEntry I d) =
      E.region β ∪ E.frontReg β s := by
  have hl := len_eq_time h
  have hl' : (E.2.1).len = (E.time : ℝ≥0∞) := hl
  have hl2 : ((E.2.extend (E.time + s) v).1).len = ((E.time + s : ℝ≥0) : ℝ≥0∞) := rfl
  ext x
  constructor
  · rintro ⟨r, hr0, hrT, hx1, hx2, hx3⟩
    simp only [CycEntry.data, CycEntry.len, CycEntry.path] at hrT hx1 hx2 hx3
    rw [hl2] at hrT
    have hrT' : r ≤ E.time + s := by
      have : (r : ℝ≥0∞) ≤ ((E.time + s : ℝ≥0) : ℝ≥0∞) := hrT
      exact_mod_cast this
    by_cases hrt : r ≤ E.time
    · left
      refine ⟨r, hr0, ?_, hx1, hx2, ?_⟩
      · rw [hl]; exact_mod_cast hrt
      · have := (E.2.1).left_extend_of_lt (E.time + s) v hr0 hrT'
        have h2 : (E.2.extend (E.time + s) v).1.left r = E.path.left r := this
        rw [h2] at hx3; exact hx3
    · right
      push Not at hrt
      refine ⟨r - E.time, tsub_pos_of_lt hrt, ?_, hx1, ?_, ?_⟩
      · exact tsub_le_iff_left.2 hrT'
      · rw [hx2, add_tsub_cancel_of_le hrt.le]; rfl
      · have hleft : (E.2.extend (E.time + s) v).1.left r = E.pos := by
          refine (E.2.extend (E.time + s) v).1.left_eq_of_eventually hr0 ?_
          filter_upwards [Ioo_mem_nhdsLT hrt] with u hu
          have hu1 : E.time < u := hu.1
          show (E.2.1.extend (E.time + s) v).fn u = E.pos
          rw [(E.2.1).extend_fn_of_lt _ v (lt_of_lt_of_le hu.2 hrT')]
          exact path_fn_eq_pos h hu1.le
        rw [hleft] at hx3; exact hx3
  · simp only [CycEntry.region, Set.mem_ofPred_eq, CycEntry.data, CycEntry.len, CycEntry.path]
    rintro (⟨r, hr0, hrl, hx1, hx2, hx3⟩ | ⟨t, ht0, hts, hx1, hx2, hx3⟩)
    · have hrt : r ≤ E.time := by
        rw [hl'] at hrl; exact_mod_cast hrl
      refine ⟨r, hr0, ?_, hx1, hx2, ?_⟩
      · rw [hl2]; exact_mod_cast hrt.trans le_self_add
      · have h2 : (E.2.extend (E.time + s) v).1.left r = E.path.left r :=
          (E.2.1).left_extend_of_lt (E.time + s) v hr0 (hrt.trans le_self_add)
        rw [h2]; exact hx3
    · have hr0 : 0 < E.time + t := lt_of_lt_of_le ht0 le_add_self
      have hrt : E.time < E.time + t := lt_add_of_pos_right _ ht0
      refine ⟨E.time + t, hr0, ?_, hx1, hx2, ?_⟩
      · rw [hl2]; exact_mod_cast add_le_add le_rfl hts
      · have hleft : (E.2.extend (E.time + s) v).1.left (E.time + t) = E.pos := by
          refine (E.2.extend (E.time + s) v).1.left_eq_of_eventually hr0 ?_
          filter_upwards [Ioo_mem_nhdsLT hrt] with u hu
          have hu1 : E.time < u := hu.1
          show (E.2.1.extend (E.time + s) v).fn u = E.pos
          rw [(E.2.1).extend_fn_of_lt _ v (lt_of_lt_of_le hu.2 (add_le_add le_rfl hts))]
          exact path_fn_eq_pos h hu1.le
        rw [hleft]; exact hx3

end CycEntry

namespace CycRec

omit [MeasurableSpace I] in
theorem isEntry_inl {n : ℕ} {f : Fin n → CycEntry I d} {e : CycEntry I d} :
    CycRec.IsEntry (Sum.inl ⟨n, f⟩ : CycRec I d) e ↔ ∃ i, f i = e := by
  constructor
  · rintro ⟨k, hk⟩
    simp only [nth] at hk
    split_ifs at hk with h
    · exact ⟨⟨k, h⟩, Option.some.inj hk⟩
  · rintro ⟨i, rfl⟩
    exact ⟨i.val, by simp [nth, i.2]⟩

omit [Fact (0 < β)] in
omit [MeasurableSpace I] in
theorem mem_region_inl {n : ℕ} {f : Fin n → CycEntry I d} {x : I × RingSpace d β} :
    x ∈ CycRec.region β (Sum.inl ⟨n, f⟩ : CycRec I d) ↔ ∃ i, x ∈ (f i).region β := by
  constructor
  · rintro ⟨e, he, hx⟩
    obtain ⟨i, rfl⟩ := isEntry_inl.1 he
    exact ⟨i, hx⟩
  · rintro ⟨i, hx⟩
    exact ⟨f i, isEntry_inl.2 ⟨i, rfl⟩, hx⟩

omit [Fact (0 < β)] in
omit [MeasurableSpace I] in
theorem region_push_inl {n : ℕ} (f : Fin n → CycEntry I d) (e : CycEntry I d) :
    CycRec.region β (CycRec.push e (Sum.inl ⟨n, f⟩ : CycRec I d)) =
      CycRec.region β (Sum.inl ⟨n, f⟩ : CycRec I d) ∪ e.region β := by
  ext x
  show x ∈ CycRec.region β (Sum.inl ⟨n + 1, CycRec.snoc f e⟩ : CycRec I d) ↔ _
  rw [mem_region_inl, Set.mem_union, mem_region_inl]
  constructor
  · rintro ⟨i, hi⟩
    refine Fin.lastCases ?_ (fun j hj => ?_) i hi
    · intro h
      right; simpa [CycRec.snoc] using h
    · left; exact ⟨j, by simpa [CycRec.snoc] using hj⟩
  · rintro (⟨i, hi⟩ | h)
    · exact ⟨i.castSucc, by simpa [CycRec.snoc] using hi⟩
    · exact ⟨Fin.last n, by simpa [CycRec.snoc] using h⟩

omit [Fact (0 < β)] in
omit [MeasurableSpace I] in
theorem region_setLast_inl {n : ℕ} (f : Fin (n + 1) → CycEntry I d) (e : CycEntry I d)
    (h : (f (Fin.last n)).region β ⊆ e.region β) :
    CycRec.region β (CycRec.setLast e (Sum.inl ⟨n + 1, f⟩ : CycRec I d)) =
      CycRec.region β (Sum.inl ⟨n + 1, f⟩ : CycRec I d) ∪ e.region β := by
  ext x
  show x ∈ CycRec.region β (Sum.inl ⟨n + 1, Function.update f (Fin.last n) e⟩ : CycRec I d) ↔ _
  rw [mem_region_inl, Set.mem_union, mem_region_inl]
  constructor
  · rintro ⟨i, hi⟩
    by_cases hin : i = Fin.last n
    · subst hin; right; simpa using hi
    · left; exact ⟨i, by simpa [Function.update_of_ne hin] using hi⟩
  · rintro (⟨i, hi⟩ | hx)
    · by_cases hin : i = Fin.last n
      · subst hin; exact ⟨Fin.last n, by simpa using h hi⟩
      · exact ⟨i, by simpa [Function.update_of_ne hin] using hi⟩
    · exact ⟨Fin.last n, by simpa using hx⟩

end CycRec

namespace CycScheme

/-- A finite non-empty record whose last entry has finite length. -/
def RecWF (ρ : CycRec I d) : Prop :=
  ∃ (n : ℕ) (f : Fin (n + 1) → CycEntry I d), ρ = Sum.inl ⟨n + 1, f⟩ ∧
    (f (Fin.last n)).len ≠ ⊤

/-- Well-formed states (the part of the invariant needed for the region identity). -/
def WF (st : State I d) : Prop := RecWF st.1

variable (P : CycPlan I d β) (sc : ℝ≥0∞)

omit [Fact (0 < β)] in
theorem cur_inl (n : ℕ) (f : Fin (n + 1) → CycEntry I d) (b : Bool) :
    cur P ((Sum.inl ⟨n + 1, f⟩, b) : State I d) = f (Fin.last n) := by
  have h1 : CycRec.lastIdx (Sum.inl ⟨n + 1, f⟩ : CycRec I d) = n := by
    have h0 : CycRec.num (Sum.inl ⟨n + 1, f⟩ : CycRec I d) = ((n + 1 : ℕ) : ℕ∞) := rfl
    unfold CycRec.lastIdx
    rw [h0, ENat.toNat_natCast]
    rfl
  simp [cur, CycRec.lastEntry, h1, CycRec.coord, CycRec.nth, Fin.last]

omit [MeasurableSpace I] in
theorem newEntry_len_ne_top (δ : CycData I d) : (CycData.newEntry δ).len ≠ ⊤ := by
  have : (CycData.newEntry δ).len = 0 := by
    show (CPath.cut (CycPath.const δ.start).1 0).len = 0
    exact CPath.cut_len _ _
  rw [this]; simp

omit [MeasurableSpace I] [Fact (0 < β)] in
theorem newEntry_region (δ : CycData I d) :
    (CycData.newEntry δ).region β = ∅ := by
  have : (CycData.newEntry δ).len = 0 := by
    show (CPath.cut (CycPath.const δ.start).1 0).len = 0
    exact CPath.cut_len _ _
  ext x
  simp only [CycEntry.region, Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
  rintro ⟨r, hr0, hrl, -⟩
  rw [show CycEntry.len (CycData.newEntry δ) = 0 from this] at hrl
  have : (r : ℝ≥0∞) = 0 := le_antisymm hrl zero_le
  exact hr0.ne' (by exact_mod_cast this)

omit [MeasurableSpace I] in
theorem RecWF.setLast {ρ : CycRec I d} (hρ : RecWF ρ) {e : CycEntry I d} (he : e.len ≠ ⊤) :
    RecWF (CycRec.setLast e ρ) := by
  obtain ⟨n, f, rfl, -⟩ := hρ
  exact ⟨n, Function.update f (Fin.last n) e, rfl, by simpa using he⟩

omit [MeasurableSpace I] in
theorem RecWF.push {ρ : CycRec I d} (hρ : RecWF ρ) {e : CycEntry I d} (he : e.len ≠ ⊤) :
    RecWF (CycRec.push e ρ) := by
  obtain ⟨n, f, rfl, -⟩ := hρ
  exact ⟨n + 1, CycRec.snoc f e, rfl, by simpa [CycRec.snoc] using he⟩

omit [Fact (0 < β)] in
omit [MeasurableSpace I] in
theorem RecWF.region_push {ρ : CycRec I d} (hρ : RecWF ρ) (e : CycEntry I d) :
    (CycRec.push e ρ).region β = ρ.region β ∪ e.region β := by
  obtain ⟨n, f, rfl, -⟩ := hρ
  exact CycRec.region_push_inl _ _

omit [Fact (0 < β)] in
theorem WF.cur_len {st : State I d} (hW : WF st) : (cur P st).len ≠ ⊤ := by
  obtain ⟨ρ, b⟩ := st
  obtain ⟨n, f, h1, h2⟩ := hW
  simp only at h1
  subst h1
  rw [cur_inl]; exact h2

omit [Fact (0 < β)] in
theorem WF.region_cur_subset {st : State I d} (hW : WF st) :
    (cur P st).region β ⊆ st.1.region β := by
  obtain ⟨ρ, b⟩ := st
  obtain ⟨n, f, h1, h2⟩ := hW
  simp only at h1
  subst h1
  rw [cur_inl]
  intro x hx
  exact (CycRec.mem_region_inl).2 ⟨Fin.last n, hx⟩

variable [Countable I] [MeasurableSingletonClass I]

theorem region_newRec_of_wf {st : State I d} (hW : WF st) (o : Outcome (CycS I d β)) :
    (newRec P sc st o).region β =
      st.1.region β ∪ (cur P st).frontReg β (sStar P sc st o) := by
  have hcl := hW.cur_len (P := P)
  have key := CycEntry.region_extend (β := β) hcl (sStar P sc st o) (newV P sc st o)
  have hsub := hW.region_cur_subset (P := P)
  obtain ⟨ρ, b⟩ := st
  obtain ⟨n, f, h1, h2⟩ := hW
  simp only at h1
  subst h1
  have hc := cur_inl (β := β) P n f b
  unfold newRec newEntry
  simp only
  rw [hc] at key ⊢
  rw [CycRec.region_setLast_inl _ _ (by rw [key]; exact Set.subset_union_left)]
  rw [key]
  rw [hc] at hsub
  rw [← Set.union_assoc, Set.union_eq_self_of_subset_right hsub]

theorem newRec_wf {st : State I d} (hW : WF st) (o : Outcome (CycS I d β)) :
    RecWF (newRec P sc st o) := by
  unfold CycScheme.newRec
  refine RecWF.setLast hW ?_
  show (((cur P st).2.extend ((cur P st).time + sStar P sc st o) (newV P sc st o)).1).len ≠ ⊤
  exact ENNReal.coe_ne_top

/-- The region of the updated record: old region plus the front region of the current step. -/
theorem WF.region_upd {st : State I d} (hW : WF st) (o : Outcome (CycS I d β)) :
    (upd P sc st o).1.region β = st.1.region β ∪
      (if st.2 = true then ∅ else (cur P st).frontReg β (sStar P sc st o)) ∧
    WF (upd P sc st o) := by
  have hN := newRec_wf (P := P) (sc := sc) hW o
  have hR := region_newRec_of_wf (P := P) (sc := sc) hW o
  unfold upd
  by_cases hb : st.2 = true
  · simp [hb, hW]
  · simp only [hb, ite_false, Bool.false_eq_true]
    split_ifs with hs hK
    · refine ⟨?_, ?_⟩
      · show (CycRec.push _ (newRec P sc st o)).region β = _
        rw [hN.region_push, newEntry_region, Set.union_empty, hR]
      · exact hN.push (by
          show (CycData.newEntry _).len ≠ ⊤
          exact newEntry_len_ne_top _)
    · exact ⟨hR, hN⟩
    · exact ⟨hR, hN⟩

end CycScheme

end ElboimSly.Cyclic

end

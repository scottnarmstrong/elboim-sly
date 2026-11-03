/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Foundations.Cyclic.CycRecCoords
public import ElboimSly.Foundations.Cyclic.CycArcMeas
public import ElboimSly.Frozen.Defs.EdgeInstCountable
public import ElboimSly.Frozen.Defs.EdgeInstMeasurableSingletonClass
public import Mathlib

/-!
# Measurability of record functionals (a), part 1: the explored region of an entry

Measurability of record functionals (a). We rewrite the explored region of a world-line through its jump
list: `x = (ι', e, θ)` lies in the region iff for some `a` with `ς_a < ∞`,
`ι' = ι`, `e ∋ p(ς_a)` and some `r ∈ (ς_a, ς_{a+1} ∧ ℓ]` has `c_δ(r) = θ`. The arc test is
`exists_arc_iff`.
-/

@[expose] public section

open MeasureTheory Set Filter Topology
open scoped ENNReal NNReal

namespace ElboimSly.Cyclic

variable {V : Type*}

/-- Every `r > 0` lies in some `(ς_a, ς_{a+1}]`. -/
theorem CPath.exists_idx (p : CPath V) {r : ℝ≥0} (hr : 0 < r) :
    ∃ a : ℕ, p.jt a < r ∧ (r : ℝ≥0∞) ≤ p.jt (a + 1) := by
  have hex : ∃ a : ℕ, (r : ℝ≥0∞) ≤ p.jt (a + 1) := by
    refine ⟨p.cnt r, ?_⟩
    by_contra h
    push Not at h
    have := (p.jt_le_iff (p.cnt r + 1) r).mp h.le
    omega
  classical
  refine ⟨Nat.find hex, ?_, Nat.find_spec hex⟩
  rcases hn : Nat.find hex with _ | a
  · have : p.jt 0 ≤ 0 := by
      have := (p.jt_le_iff 0 0).mpr (Nat.zero_le _)
      simpa using this
    exact lt_of_le_of_lt this (by exact_mod_cast hr)
  · have := Nat.find_min hex (show a < Nat.find hex by omega)
    push Not at this
    exact this

variable {I : Type*} [MeasurableSpace I] {d : ℕ} {β : ℝ} [Fact (0 < β)]

/-- The target of the arc test: `c_δ(r) = θ` iff `[r] = arcTarget δ θ`. -/
noncomputable def arcTarget (δ : CycData I d) (θ : AddCircle β) : AddCircle β :=
  open scoped Classical in
  if δ.fwd then θ - ((δ.phase : ℝ) : AddCircle β) else ((δ.phase : ℝ) : AddCircle β) - θ

omit [MeasurableSpace I] [Fact (0 < β)] in
theorem clock_eq_iff (δ : CycData I d) (θ : AddCircle β) (r : ℝ≥0) :
    δ.clock β r = θ ↔ (((r : ℝ≥0) : ℝ) : AddCircle β) = arcTarget δ θ := by
  unfold CycData.clock arcTarget CycData.sgn
  by_cases h : δ.fwd = true
  · simp only [h, ite_true, one_mul, AddCircle.coe_add]
    constructor
    · intro h1; rw [← h1]; abel
    · intro h1; rw [h1]; abel
  · have hf : δ.fwd = false := by simpa using h
    simp only [hf, Bool.false_eq_true, ite_false, neg_mul, one_mul, ← sub_eq_add_neg,
      AddCircle.coe_sub]
    constructor
    · intro h1; rw [← h1]; abel
    · intro h1; rw [h1]; abel

/-- The `a`-th piece of the region of an entry, written through the jump list. -/
def regionPiece (E : CycEntry I d) (x : I × RingSpace d β) (a : ℕ) : Prop :=
  x.1 = E.data.copy ∧ Edge.Mem (E.path.jv a) x.2.1 ∧ E.path.jt a < ⊤ ∧
    E.path.jt a + ENNReal.ofReal (circRep (arcTarget E.data x.2.2 -
      ((((E.path.jt a).toNNReal : ℝ≥0) : ℝ) : AddCircle β))) ≤ min (E.path.jt (a + 1)) E.path.len

omit [MeasurableSpace I] in
theorem CycEntry.mem_region_iff [MeasurableSpace I] (E : CycEntry I d) (x : I × RingSpace d β) :
    x ∈ E.region β ↔ ∃ a, regionPiece E x a := by
  constructor
  · rintro ⟨r, hr0, hrl, h1, h2, h3⟩
    obtain ⟨a, ha1, ha2⟩ := E.path.exists_idx hr0
    have hleft : E.path.left r = E.path.jv a := E.path.left_eq_jv ha1 ha2
    have hlt : E.path.jt a < ⊤ := ha1.trans ENNReal.coe_lt_top
    refine ⟨a, h1, ?_, hlt, ?_⟩
    · rw [← hleft]; exact h3
    · have hr : (E.path.jt a).toNNReal < r := by
        have : ((E.path.jt a).toNNReal : ℝ≥0∞) < r := by rwa [ENNReal.coe_toNNReal hlt.ne]
        exact_mod_cast this
      have hc : (((r : ℝ≥0) : ℝ) : AddCircle β) = arcTarget E.data x.2.2 :=
        (clock_eq_iff E.data x.2.2 r).mp h2.symm
      have := (exists_arc_iff (arcTarget E.data x.2.2) (E.path.jt a).toNNReal
        (min (E.path.jt (a + 1)) E.path.len)).mp ⟨r, hr, le_min ha2 hrl, hc⟩
      rwa [ENNReal.coe_toNNReal hlt.ne] at this
  · rintro ⟨a, h1, h2, hlt, h3⟩
    obtain ⟨r, hr, hrle, hrc⟩ := (exists_arc_iff (arcTarget E.data x.2.2) (E.path.jt a).toNNReal
        (min (E.path.jt (a + 1)) E.path.len)).mpr (by rwa [ENNReal.coe_toNNReal hlt.ne])
    have hja : E.path.jt a < r := by
      have : ((E.path.jt a).toNNReal : ℝ≥0∞) < r := by exact_mod_cast hr
      rwa [ENNReal.coe_toNNReal hlt.ne] at this
    have hr0 : 0 < r := lt_of_le_of_lt bot_le hr
    refine ⟨r, hr0, (le_min_iff.mp hrle).2, h1, ((clock_eq_iff _ _ _).mpr hrc).symm, ?_⟩
    rw [E.path.left_eq_jv hja (le_min_iff.mp hrle).1]
    exact h2

section Meas

variable [MeasurableSingletonClass I] [Countable I]

omit [MeasurableSingletonClass I] [Countable I] in
theorem measurable_entry_copy : Measurable fun E : CycEntry I d => E.data.copy :=
  measurable_fst.comp measurable_fst

omit [MeasurableSingletonClass I] [Countable I] in
theorem measurable_entry_phase : Measurable fun E : CycEntry I d => E.data.phase :=
  measurable_fst.comp (measurable_snd.comp (measurable_snd.comp measurable_fst))

omit [MeasurableSingletonClass I] [Countable I] in
theorem measurable_entry_fwd : Measurable fun E : CycEntry I d => E.data.fwd :=
  measurable_snd.comp (measurable_snd.comp (measurable_snd.comp measurable_fst))

omit [MeasurableSingletonClass I] [Countable I] in
theorem measurable_entry_path : Measurable fun E : CycEntry I d => E.path :=
  measurable_subtype_coe.comp measurable_snd

omit [MeasurableSingletonClass I] [Countable I] in
theorem measurable_entry_jt (a : ℕ) : Measurable fun E : CycEntry I d => E.path.jt a :=
  (CPath.measurable_jt a).comp measurable_entry_path

omit [MeasurableSingletonClass I] [Countable I] in
theorem measurable_entry_jv (a : ℕ) : Measurable fun E : CycEntry I d => E.path.jv a :=
  (CPath.measurable_jv a).comp measurable_entry_path

omit [MeasurableSingletonClass I] [Countable I] in
theorem measurable_entry_len : Measurable fun E : CycEntry I d => E.path.len :=
  CPath.measurable_len.comp measurable_entry_path

omit [Fact (0 < β)] in
omit [MeasurableSingletonClass I] [Countable I] in
theorem measurable_arcTarget :
    Measurable fun z : CycEntry I d × AddCircle β => arcTarget z.1.data z.2 := by
  unfold arcTarget
  have hf : MeasurableSet {z : CycEntry I d × AddCircle β | z.1.data.fwd = true} :=
    (measurable_entry_fwd.comp measurable_fst) (measurableSet_singleton true)
  have hph : Measurable fun z : CycEntry I d × AddCircle β =>
      (((z.1.data.phase : ℝ)) : AddCircle β) :=
    AddCircle.measurable_mk'.comp (measurable_entry_phase.comp measurable_fst)
  refine Measurable.ite hf (measurable_snd.sub hph) (hph.sub measurable_snd)

theorem measurableSet_regionPiece (a : ℕ) :
    MeasurableSet {z : CycEntry I d × (I × RingSpace d β) | regionPiece z.1 z.2 a} := by
  have hE : Measurable fun z : CycEntry I d × (I × RingSpace d β) => z.1 := measurable_fst
  have h1 : MeasurableSet {z : CycEntry I d × (I × RingSpace d β) | z.2.1 = z.1.data.copy} :=
    measurableSet_eq_fun (measurable_fst.comp measurable_snd) (measurable_entry_copy.comp hE)
  have h2 : MeasurableSet {z : CycEntry I d × (I × RingSpace d β) |
      Edge.Mem (z.1.path.jv a) z.2.2.1} := by
    have hg : Measurable fun z : CycEntry I d × (I × RingSpace d β) =>
        (z.1.path.jv a, z.2.2.1) :=
      ((measurable_entry_jv a).comp hE).prodMk
        (measurable_fst.comp (measurable_snd.comp measurable_snd))
    have hS : MeasurableSet {q : (Fin d → ℤ) × Edge d | Edge.Mem q.1 q.2} :=
      (Set.to_countable _).measurableSet
    exact hg hS
  have h3 : MeasurableSet {z : CycEntry I d × (I × RingSpace d β) | z.1.path.jt a < ⊤} :=
    measurableSet_lt ((measurable_entry_jt a).comp hE) measurable_const
  have h4 : MeasurableSet {z : CycEntry I d × (I × RingSpace d β) |
      z.1.path.jt a + ENNReal.ofReal (circRep (arcTarget z.1.data z.2.2.2 -
        ((((z.1.path.jt a).toNNReal : ℝ≥0) : ℝ) : AddCircle β))) ≤
        min (z.1.path.jt (a + 1)) z.1.path.len} := by
    have hj : Measurable fun z : CycEntry I d × (I × RingSpace d β) => z.1.path.jt a :=
      (measurable_entry_jt a).comp hE
    have ht : Measurable fun z : CycEntry I d × (I × RingSpace d β) =>
        arcTarget z.1.data z.2.2.2 :=
      measurable_arcTarget.comp (measurable_fst.prodMk (measurable_snd.comp (measurable_snd.comp measurable_snd)))
    have hc : Measurable fun z : CycEntry I d × (I × RingSpace d β) =>
        ((((z.1.path.jt a).toNNReal : ℝ≥0) : ℝ) : AddCircle β) :=
      AddCircle.measurable_mk'.comp (measurable_coe_nnreal_real.comp
        (ENNReal.measurable_toNNReal.comp hj))
    have hL : Measurable fun z : CycEntry I d × (I × RingSpace d β) =>
        z.1.path.jt a + ENNReal.ofReal (circRep (arcTarget z.1.data z.2.2.2 -
          ((((z.1.path.jt a).toNNReal : ℝ≥0) : ℝ) : AddCircle β))) :=
      hj.add (ENNReal.measurable_ofReal.comp (measurable_circRep.comp (ht.sub hc)))
    exact measurableSet_le hL (((measurable_entry_jt (a + 1)).comp hE).min
      (measurable_entry_len.comp hE))
  exact h1.inter (h2.inter (h3.inter h4))

theorem measurableSet_entry_region :
    MeasurableSet {z : CycEntry I d × (I × RingSpace d β) | z.2 ∈ z.1.region β} := by
  have : {z : CycEntry I d × (I × RingSpace d β) | z.2 ∈ z.1.region β} =
      ⋃ a : ℕ, {z : CycEntry I d × (I × RingSpace d β) | regionPiece z.1 z.2 a} := by
    ext z
    simp only [mem_ofPred_eq, mem_iUnion]
    exact CycEntry.mem_region_iff z.1 z.2
  rw [this]
  exact MeasurableSet.iUnion measurableSet_regionPiece

omit [MeasurableSpace I] [Fact (0 < β)] [MeasurableSingletonClass I] [Countable I] in
theorem CycRec.mem_region_iff (junk : CycEntry I d) (ρ : CycRec I d) (x : I × RingSpace d β) :
    x ∈ ρ.region β ↔ ∃ j : ℕ, (j : ℕ∞) < ρ.num ∧ x ∈ (ρ.coord junk j).region β := by
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

/-- Measurability of record functionals (a): `(ρ, x) ↦ 1{x ∈ R(ρ)}` is measurable. -/
theorem measurableSet_region [Nonempty (CycEntry I d)] :
    MeasurableSet {z : CycRec I d × (I × RingSpace d β) | z.2 ∈ z.1.region β} := by
  obtain ⟨junk⟩ := ‹Nonempty (CycEntry I d)›
  have : {z : CycRec I d × (I × RingSpace d β) | z.2 ∈ z.1.region β} =
      ⋃ j : ℕ, {z | (j : ℕ∞) < z.1.num} ∩
        (fun z : CycRec I d × (I × RingSpace d β) => (z.1.coord junk j, z.2)) ⁻¹'
          {y : CycEntry I d × (I × RingSpace d β) | y.2 ∈ y.1.region β} := by
    ext z
    simp only [mem_ofPred_eq, mem_iUnion, mem_inter_iff, mem_preimage]
    exact CycRec.mem_region_iff junk z.1 z.2
  rw [this]
  refine MeasurableSet.iUnion fun j => ?_
  refine MeasurableSet.inter ?_ ?_
  · have hS : MeasurableSet {n : ℕ∞ | (j : ℕ∞) < n} := (Set.to_countable _).measurableSet
    exact (CycRec.measurable_num.comp measurable_fst) hS
  · exact ((CycRec.measurable_coord junk j).comp measurable_fst).prodMk measurable_snd
      measurableSet_entry_region

end Meas

end ElboimSly.Cyclic

end

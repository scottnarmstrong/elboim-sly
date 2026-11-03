/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Foundations.Cyclic.CycRingMeas
public import Mathlib

/-!
# Measurability of record functionals (a), part 4: measurability of `RM` and `#Ring`

`ρ ↦ RM(ρ)` is measurable into `Measure (I × RingSpace d β)`, `ρ ↦ #Ring(ρ)` is measurable into
`ℕ∞`, and `(ρ, x) ↦ 1{x ∈ R(ρ)}` is measurable (`measurableSet_region` in `CycRegionMeas`).
-/

@[expose] public section

open MeasureTheory Set Filter Topology
open scoped ENNReal NNReal

namespace ElboimSly.Cyclic

variable {I : Type*} [MeasurableSpace I] [MeasurableSingletonClass I] [Countable I] {d : ℕ}
  {β : ℝ} [Fact (0 < β)]

omit [MeasurableSingletonClass I] [Countable I] in
theorem measurable_entry_sgn : Measurable fun E : CycEntry I d => E.data.sgn := by
  unfold CycData.sgn
  have hf : MeasurableSet {E : CycEntry I d | E.data.fwd = true} :=
    measurable_entry_fwd (measurableSet_singleton true)
  exact Measurable.ite hf measurable_const measurable_const

omit [Fact (0 < β)] in
omit [MeasurableSingletonClass I] [Countable I] in
theorem measurable_clock :
    Measurable fun z : CycEntry I d × ℝ≥0 => z.1.data.clock β z.2 := by
  unfold CycData.clock
  have h1 : Measurable fun z : CycEntry I d × ℝ≥0 => z.1.data.phase :=
    measurable_entry_phase.comp measurable_fst
  have h2 : Measurable fun z : CycEntry I d × ℝ≥0 => z.1.data.sgn :=
    measurable_entry_sgn.comp measurable_fst
  have h3 : Measurable fun z : CycEntry I d × ℝ≥0 => ((z.2 : ℝ≥0) : ℝ) :=
    measurable_coe_nnreal_real.comp measurable_snd
  have h4 : Measurable fun z : CycEntry I d × ℝ≥0 => z.1.data.phase + z.1.data.sgn * z.2 :=
    h1.add (h2.mul h3)
  exact AddCircle.measurable_mk'.comp h4

omit [Fact (0 < β)] in
omit [MeasurableSingletonClass I] [Countable I] in
theorem measurable_ringPt (e0 : Edge d) (a : ℕ) :
    Measurable fun E : CycEntry I d => ringPt (β := β) e0 E a := by
  have h1 : Measurable fun E : CycEntry I d => (E.path.jv a, E.path.jv (a + 1)) :=
    (measurable_entry_jv a).prodMk (measurable_entry_jv (a + 1))
  have h2 : Measurable fun E : CycEntry I d => edgeOf e0 (E.path.jv a) (E.path.jv (a + 1)) := by
    refine measurable_to_countable' fun e => ?_
    have hS : MeasurableSet {q : (Fin d → ℤ) × (Fin d → ℤ) | edgeOf e0 q.1 q.2 = e} :=
      (Set.to_countable _).measurableSet
    exact h1 hS
  have h3 : Measurable fun E : CycEntry I d => (E, (E.path.jt (a + 1)).toNNReal) :=
    measurable_id.prodMk (ENNReal.measurable_toNNReal.comp (measurable_entry_jt (a + 1)))
  have h4 : Measurable fun E : CycEntry I d => E.data.clock β (E.path.jt (a + 1)).toNNReal :=
    measurable_clock.comp h3
  have h5 : Measurable fun E : CycEntry I d => (E.data.copy,
      (edgeOf e0 (E.path.jv a) (E.path.jv (a + 1)),
        E.data.clock β (E.path.jt (a + 1)).toNNReal)) :=
    measurable_entry_copy.prodMk (h2.prodMk h4)
  have h6 : (fun E : CycEntry I d => ringPt (β := β) e0 E a) = fun E => (E.data.copy,
      (edgeOf e0 (E.path.jv a) (E.path.jv (a + 1)),
        E.data.clock β (E.path.jt (a + 1)).toNNReal)) := rfl
  rw [h6]
  exact h5

omit [MeasurableSingletonClass I] [Countable I] in
theorem measurableSet_ringValid (a : ℕ) :
    MeasurableSet {E : CycEntry I d | ringValid E a} := by
  have h1 : MeasurableSet {E : CycEntry I d | E.path.jt (a + 1) < ⊤} :=
    measurableSet_lt (measurable_entry_jt (a + 1)) measurable_const
  have h2 : MeasurableSet {E : CycEntry I d | E.path.jt (a + 1) ≤ E.len} :=
    measurableSet_le (measurable_entry_jt (a + 1)) measurable_entry_len
  have h3 : MeasurableSet {E : CycEntry I d | E.path.jv a ≠ E.path.jv (a + 1)} :=
    (measurableSet_eq_fun (measurable_entry_jv a) (measurable_entry_jv (a + 1))).compl
  have h4 : MeasurableSet {E : CycEntry I d |
      LatticeAdj d (E.path.jv a) (E.path.jv (a + 1))} := by
    have hg : Measurable fun E : CycEntry I d => (E.path.jv a, E.path.jv (a + 1)) :=
      (measurable_entry_jv a).prodMk (measurable_entry_jv (a + 1))
    have hS : MeasurableSet {q : (Fin d → ℤ) × (Fin d → ℤ) | LatticeAdj d q.1 q.2} :=
      (Set.to_countable _).measurableSet
    exact hg hS
  exact h1.inter (h2.inter (h3.inter h4))

variable [Nonempty (CycEntry I d)]

omit [Nonempty (CycEntry I d)] in
omit [Fact (0 < β)] in
omit [MeasurableSingletonClass I] [Countable I] in
theorem measurable_ringAt (e0 : Edge d) (junk : CycEntry I d) (n : ℕ) :
    Measurable fun ρ : CycRec I d => ρ.ringAt (β := β) e0 junk n :=
  (measurable_ringPt e0 _).comp (CycRec.measurable_coord junk _)

omit [Nonempty (CycEntry I d)] in
omit [MeasurableSingletonClass I] [Countable I] in
theorem measurableSet_ringIdx (junk : CycEntry I d) (n : ℕ) :
    MeasurableSet {ρ : CycRec I d | ρ.ringIdx junk n} := by
  have h1 : MeasurableSet {ρ : CycRec I d | ((Nat.unpair n).1 : ℕ∞) < ρ.num} := by
    have hS : MeasurableSet {m : ℕ∞ | ((Nat.unpair n).1 : ℕ∞) < m} :=
      (Set.to_countable _).measurableSet
    exact CycRec.measurable_num hS
  have h2 : MeasurableSet {ρ : CycRec I d |
      ringValid (ρ.coord junk (Nat.unpair n).1) (Nat.unpair n).2} :=
    (CycRec.measurable_coord junk _) (measurableSet_ringValid _)
  exact h1.inter h2

omit [Nonempty (CycEntry I d)] in
omit [Fact (0 < β)] in
theorem measurableSet_ringFirst (e0 : Edge d) (junk : CycEntry I d) (n : ℕ) :
    MeasurableSet {ρ : CycRec I d | ρ.ringFirst (β := β) e0 junk n} := by
  have : {ρ : CycRec I d | ρ.ringFirst (β := β) e0 junk n} =
      {ρ : CycRec I d | ρ.ringIdx junk n} ∩
      ⋂ m ∈ Finset.range n, ({ρ : CycRec I d | ρ.ringIdx junk m} ∩
        {ρ | ρ.ringAt (β := β) e0 junk m = ρ.ringAt (β := β) e0 junk n})ᶜ := by
    ext ρ
    simp [CycRec.ringFirst]
  rw [this]
  refine (measurableSet_ringIdx junk n).inter ?_
  refine Finset.measurableSet_biInter _ fun m _ => ?_
  exact ((measurableSet_ringIdx junk m).inter
    (measurableSet_eq_fun (measurable_ringAt e0 junk m) (measurable_ringAt e0 junk n))).compl

omit [Nonempty (CycEntry I d)] in
omit [Fact (0 < β)] in
/-- Measurability of record functionals (a): `ρ ↦ RM(ρ)` is measurable. -/
theorem measurable_rm_aux (e0 : Edge d) (junk : CycEntry I d) :
    Measurable fun ρ : CycRec I d => ρ.rm β := by
  refine Measure.measurable_of_measurable_coe _ fun B hB => ?_
  classical
  have : (fun ρ : CycRec I d => ρ.rm β B) = fun ρ => ∑' n,
      if ρ.ringFirst (β := β) e0 junk n ∧ ρ.ringAt e0 junk n ∈ B then (1 : ℝ≥0∞) else 0 := by
    funext ρ
    exact CycRec.rm_apply_eq_tsum e0 junk ρ hB
  rw [this]
  refine Measurable.tsum fun n => ?_
  refine Measurable.ite ?_ measurable_const measurable_const
  exact (measurableSet_ringFirst e0 junk n).inter (measurable_ringAt e0 junk n hB)

omit [Nonempty (CycEntry I d)] in
omit [Fact (0 < β)] in
/-- Measurability of record functionals (a): `ρ ↦ #Ring(ρ)` (as an extended natural number). -/
theorem measurable_ringCard (e0 : Edge d) (junk : CycEntry I d) :
    Measurable fun ρ : CycRec I d => (ρ.ringSet β).encard := by
  have hm : Measurable fun ρ : CycRec I d => ρ.rm β Set.univ :=
    (Measure.measurable_coe MeasurableSet.univ).comp (measurable_rm_aux e0 junk)
  have heq : ∀ ρ : CycRec I d, ρ.rm β Set.univ = ((ρ.ringSet β).encard : ℝ≥0∞) := by
    intro ρ
    have hcount : (ρ.ringSet β).Countable := CycRec.ringSet_countable e0 junk ρ
    rw [CycRec.rm, Measure.restrict_apply MeasurableSet.univ, Set.univ_inter,
      Measure.count_apply hcount.measurableSet]
  refine measurable_to_countable' fun n => ?_
  have : (fun ρ : CycRec I d => (ρ.ringSet β).encard) ⁻¹' {n} =
      (fun ρ : CycRec I d => ρ.rm β Set.univ) ⁻¹' {(n : ℝ≥0∞)} := by
    ext ρ
    simp only [mem_preimage, mem_singleton_iff, heq]
    exact ENat.toENNReal_inj.symm
  rw [this]
  exact hm (measurableSet_singleton _)

omit [Nonempty (CycEntry I d)] in
omit [Fact (0 < β)] in
/-- Measurability of record functionals (a): `ρ ↦ #Ring(ρ)` as a natural number (junk `0` if infinite). -/
theorem measurable_ringNcard (e0 : Edge d) (junk : CycEntry I d) :
    Measurable fun ρ : CycRec I d => (ρ.ringSet β).ncard := by
  have h1 : Measurable fun n : ℕ∞ => n.toNat := measurable_of_countable _
  have h2 := measurable_ringCard (β := β) e0 junk
  exact h1.comp h2

end ElboimSly.Cyclic

end

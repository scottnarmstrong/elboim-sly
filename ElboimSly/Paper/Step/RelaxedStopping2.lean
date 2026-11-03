/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Paper.Step.RelaxedStopping
public import Mathlib

/-!
# First entrance into a locally-`[l, r)` adapted set is a stopping time

Structure of relaxed times; stopping times (d), second sentence (the part for `inf {t > R : t ∈ U}`).
-/

@[expose] public section

open MeasureTheory Set Filter Topology ElboimSly.SRW
open scoped ENNReal NNReal

namespace ElboimSly.Paper

variable {Ω : Type*} {m : MeasurableSpace Ω} (f : Filtration ℝ≥0 m)

/-- `{R < ∞, R ∈ U}` intersected with `{R ≤ t}` is `𝒢_t`-measurable. -/
theorem measurableSet_stopped_mem {U : Ω → Set ℝ}
    (hU : ∀ t : ℝ≥0, MeasurableSet[f t] {ω | (t : ℝ) ∈ U ω}) (hloc : ∀ ω, IsLocIco (U ω))
    {R : Ω → WithTop ℝ≥0} (hR : IsStoppingTime f R) (t : ℝ≥0) :
    MeasurableSet[f t] ({ω | R ω ≠ ⊤ ∧ (stopReal R ω : ℝ) ∈ U ω} ∩ {ω | R ω ≤ t}) := by
  classical
  have hprog := Base.isStronglyProgressive_of_rc f (stepIndProc U) (stepIndProc_adapted f hU)
    (fun ω s => stepIndProc_rc hloc ω s)
  have hm := measurable_stoppedValue hprog hR
  have h1 : MeasurableSet[hR.measurableSpace] {ω | R ω ≠ ⊤} :=
    (hR.measurable (measurableSet_singleton (⊤ : WithTop ℝ≥0))).compl
  have h2 : MeasurableSet[hR.measurableSpace] (stoppedValue (stepIndProc U) R ⁻¹' {1}) :=
    hm (measurableSet_singleton 1)
  have heq : {ω | R ω ≠ ⊤ ∧ (stopReal R ω : ℝ) ∈ U ω} =
      {ω | R ω ≠ ⊤} ∩ stoppedValue (stepIndProc U) R ⁻¹' {1} := by
    ext ω
    simp only [mem_ofPred_eq, mem_inter_iff, mem_preimage, mem_singleton_iff, stoppedValue]
    refine and_congr_right fun hne => ?_
    obtain ⟨a, ha⟩ := WithTop.ne_top_iff_exists.1 hne
    simp only [stopReal, ← ha, WithTop.untopD_coe, stepIndProc]
    split_ifs with h <;> simp [h]
  rw [heq]
  exact ((hR.measurableSet _).1 (h1.inter h2)).2 t

theorem isStoppingTime_stepNextIn {U : Ω → Set ℝ}
    (hU : ∀ t : ℝ≥0, MeasurableSet[f t] {ω | (t : ℝ) ∈ U ω}) (hloc : ∀ ω, IsLocIco (U ω))
    {R : Ω → WithTop ℝ≥0} (hR : IsStoppingTime f R) : IsStoppingTime f (stepNextIn U R) := by
  classical
  intro t
  have key : {ω | stepNextIn U R ω ≤ t} =
      ({ω | R ω ≠ ⊤ ∧ (stopReal R ω : ℝ) ∈ U ω} ∩ {ω | R ω ≤ t}) ∪
      ({ω | R ω < t} ∩ {ω | (t : ℝ) ∈ U ω}) ∪
      ⋃ (q : ℚ) (_ : 0 ≤ q ∧ (q : ℝ) < t),
        ({ω | R ω < ((q : ℝ).toNNReal : WithTop ℝ≥0)} ∩ {ω | ((q : ℝ).toNNReal : ℝ) ∈ U ω}) := by
    ext ω
    simp only [mem_ofPred_eq, mem_union, mem_inter_iff, mem_iUnion, exists_prop]
    unfold stepNextIn
    rw [stepNextIn_le_iff (hloc ω)]
    constructor
    · rintro ⟨u, huU, hRu, hut⟩
      rcases hRu.lt_or_eq with hlt | heq
      · rcases hut.lt_or_eq with hut' | hut'
        · right
          obtain ⟨ε, hε, hsub⟩ := (hloc ω).exists_Ico u.2 huU
          have hutR : (u : ℝ) < t := by exact_mod_cast hut'
          obtain ⟨q, hq1, hq2⟩ := exists_rat_btwn (show (u : ℝ) < min (u + ε) t from
            lt_min (by linarith) hutR)
          have hq0 : 0 ≤ (q : ℝ) := u.2.trans hq1.le
          have hq0' : 0 ≤ q := by exact_mod_cast hq0
          refine ⟨q, ⟨hq0', lt_of_lt_of_le hq2 (min_le_right _ _)⟩, ?_, ?_⟩
          · refine lt_of_lt_of_le hlt (WithTop.coe_le_coe.2 ?_)
            rw [← NNReal.coe_le_coe, Real.coe_toNNReal _ hq0]; exact hq1.le
          · rw [Real.coe_toNNReal _ hq0]
            exact hsub ⟨hq1.le, lt_of_lt_of_le hq2 (min_le_left _ _)⟩
        · left; right
          subst hut'
          exact ⟨lt_of_lt_of_le hlt (WithTop.coe_le_coe.2 le_rfl), huU⟩
      · left; left
        have hsr : stopReal R ω = u := by simp only [stopReal, heq, WithTop.untopD_coe]
        refine ⟨⟨by rw [heq]; exact WithTop.coe_ne_top, by rw [hsr]; exact huU⟩, ?_⟩
        rw [heq]; exact WithTop.coe_le_coe.2 hut
    · rintro ((⟨⟨hne, hmem⟩, hle⟩ | ⟨hlt, hmem⟩) | ⟨q, ⟨hq0, hqt⟩, hlt, hmem⟩)
      · obtain ⟨a, ha⟩ := WithTop.ne_top_iff_exists.1 hne
        refine ⟨a, ?_, ha.symm.le, ?_⟩
        · have hsr : stopReal R ω = a := by simp only [stopReal, ← ha, WithTop.untopD_coe]
          rw [hsr] at hmem; exact hmem
        · rw [← ha] at hle; exact WithTop.coe_le_coe.1 hle
      · exact ⟨t, hmem, hlt.le, le_rfl⟩
      · refine ⟨(q : ℝ).toNNReal, hmem, hlt.le, ?_⟩
        rw [← NNReal.coe_le_coe, Real.coe_toNNReal _ (by exact_mod_cast hq0)]
        exact hqt.le
  rw [key]
  refine ((measurableSet_stopped_mem f hU hloc hR t).union
    ((f.mono le_rfl _ ((hR.measurableSet_lt t).inter (hU t))))).union ?_
  refine MeasurableSet.iUnion fun q => MeasurableSet.iUnion fun hq => ?_
  have hq0 : 0 ≤ (q : ℝ) := by exact_mod_cast hq.1
  have hle : (q : ℝ).toNNReal ≤ t := by
    rw [← NNReal.coe_le_coe, Real.coe_toNNReal _ hq0]; exact hq.2.le
  exact f.mono hle _ ((hR.measurableSet_lt _).inter (hU _))

end ElboimSly.Paper

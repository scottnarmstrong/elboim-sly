/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Foundations.SRW.AdmissibleSRW
public import ElboimSly.Foundations.SRW.Eval
public import Mathlib

/-!
# Stopping times and stopped positions

Hitting times and stopped positions.

Stopping times are Mathlib's `IsStoppingTime` for the filtration `Filtration ℝ≥0 mΩ` obtained from an
admissible family (`IsAdmissible.filtration`), with values in `WithTop ℝ≥0`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology

namespace ElboimSly
namespace SRW

variable {d : ℕ} {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} {Z : Ω → PathSpace d}
  {F : ℝ≥0 → MeasurableSpace Ω}

/-- The filtration of an admissible family. -/
def IsAdmissible.filtration (h : IsAdmissible P Z F) : Filtration ℝ≥0 mΩ := ⟨F, h.mono, h.le⟩

/-- The finite part of a random time. -/
def stopReal (T : Ω → WithTop ℝ≥0) (ω : Ω) : ℝ≥0 := (T ω).untopD 0

section

variable {f : Filtration ℝ≥0 mΩ} {T : Ω → WithTop ℝ≥0}

theorem _root_.MeasureTheory.IsStoppingTime.measurableSet_top (hT : IsStoppingTime f T) :
    MeasurableSet {ω | T ω = ⊤} := by
  have : {ω | T ω = ⊤} = (⋃ n : ℕ, {ω | T ω ≤ ((n : ℝ≥0) : WithTop ℝ≥0)})ᶜ := by
    ext ω
    simp only [mem_ofPred_eq, mem_compl_iff, mem_iUnion, not_exists, not_le]
    constructor
    · intro h n; rw [h]; exact WithTop.coe_lt_top _
    · intro h
      by_contra hne
      obtain ⟨a, ha⟩ := WithTop.ne_top_iff_exists.1 hne
      obtain ⟨n, hn⟩ := exists_nat_ge a
      have := h n
      rw [← ha] at this
      exact absurd (WithTop.coe_le_coe.2 hn) (not_le.2 this)
  rw [this]
  exact (MeasurableSet.iUnion fun n : ℕ => f.le _ _ (hT n)).compl

theorem _root_.MeasureTheory.IsStoppingTime.measurable_stopReal (hT : IsStoppingTime f T) :
    Measurable (stopReal T) := by
  refine measurable_of_Iic fun c => ?_
  have : stopReal T ⁻¹' Iic c = {ω | T ω ≤ (c : WithTop ℝ≥0)} ∪ {ω | T ω = ⊤} := by
    ext ω
    simp only [stopReal, mem_preimage, mem_Iic, mem_union, mem_ofPred_eq]
    cases hh : T ω using WithTop.recTopCoe with
    | top => simp
    | coe a =>
      change a ≤ c ↔ (a : WithTop ℝ≥0) ≤ (c : WithTop ℝ≥0) ∨ (a : WithTop ℝ≥0) = ⊤
      exact ⟨fun h => Or.inl (WithTop.coe_le_coe.2 h),
        fun h => h.elim WithTop.coe_le_coe.1 (fun h => absurd h WithTop.coe_ne_top)⟩
  rw [this]
  exact (f.le _ _ (hT c)).union hT.measurableSet_top

/-- `T ∧ i` (with `⊤ ↦ i`) as a real. -/
def stopMin (T : Ω → WithTop ℝ≥0) (i : ℝ≥0) (ω : Ω) : ℝ≥0 := min ((T ω).untopD i) i

theorem _root_.MeasureTheory.IsStoppingTime.measurable_stopMin (hT : IsStoppingTime f T)
    (i : ℝ≥0) : Measurable[f i] (stopMin T i) := by
  let : MeasurableSpace Ω := f i
  refine measurable_of_Iic fun c => ?_
  rcases le_or_gt i c with hc | hc
  · have : stopMin T i ⁻¹' Iic c = univ := by
      ext ω; simp [stopMin, min_le_iff, hc]
    rw [this]; exact MeasurableSet.univ
  · have : stopMin T i ⁻¹' Iic c = {ω | T ω ≤ (c : WithTop ℝ≥0)} := by
      ext ω
      change stopMin T i ω ≤ c ↔ T ω ≤ (c : WithTop ℝ≥0)
      cases hh : T ω using WithTop.recTopCoe with
      | top =>
        have h1 : ¬ ((⊤ : WithTop ℝ≥0) ≤ (c : WithTop ℝ≥0)) := fun h =>
          WithTop.coe_ne_top (top_le_iff.1 h)
        have h2 : ¬ (stopMin T i ω ≤ c) := by
          have : stopMin T i ω = i := by simp [stopMin, hh]
          rw [this]; exact hc.not_ge
        exact ⟨fun h => absurd h h2, fun h => absurd h h1⟩
      | coe a =>
        have e : stopMin T i ω = min a i := by unfold stopMin; rw [hh]; rfl
        rw [e, WithTop.coe_le_coe, min_le_iff]
        exact ⟨fun h => h.elim id (fun h => absurd h hc.not_ge), fun h => Or.inl h⟩
    rw [this]
    exact f.mono hc.le _ (hT c)

end

end SRW
end ElboimSly

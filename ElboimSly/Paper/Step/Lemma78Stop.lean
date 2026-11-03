/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Paper.Step.Lemma78Setting
public import ElboimSly.Paper.Step.WeakEvents
public import ElboimSly.Paper.Step.WeakThit

/-!
# Generic stopping-time facts for Lemma 7.8

Measurability (ES22 §7), generic parts: entrance times
`inf {r ≥ R : r ∈ U}` for sets `U` locally of type `[l, r)`, shifts by constants, and sets
defined by a predicate of the value of a piecewise constant path.
-/

@[expose] public section

open MeasureTheory Set Filter Topology
open scoped ENNReal NNReal

namespace ElboimSly.Paper.Step

open ElboimSly.Paper

variable {d : ℕ} {Ω : Type*} {m : MeasurableSpace Ω}

/-- For a set locally of type `[l, r)`, the non-strict entrance time is the strict one. -/
theorem step78FirstGe_eq_stepNextIn {U : Ω → Set ℝ} (hloc : ∀ ω, IsLocIco (U ω))
    (R : Ω → WithTop ℝ≥0) : step78FirstGe U R = stepNextIn U R := by
  funext ω
  unfold step78FirstGe stepNextIn
  apply le_antisymm
  · exact iInf₂_mono' fun u hu => ⟨u, ⟨hu.1, hu.2.le⟩, le_rfl⟩
  · refine le_iInf₂ fun u hu => ?_
    have := (stepNextIn_le_iff (hloc ω) (R ω) u).2 ⟨u, hu.1, hu.2, le_rfl⟩
    exact this

/-- Structure of relaxed times; stopping times (d), non-strict form. -/
theorem isStoppingTime_step78FirstGe (f : Filtration ℝ≥0 m) {U : Ω → Set ℝ}
    (hU : ∀ t : ℝ≥0, MeasurableSet[f t] {ω | (t : ℝ) ∈ U ω}) (hloc : ∀ ω, IsLocIco (U ω))
    {R : Ω → WithTop ℝ≥0} (hR : IsStoppingTime f R) : IsStoppingTime f (step78FirstGe U R) := by
  rw [step78FirstGe_eq_stepNextIn hloc]
  exact isStoppingTime_stepNextIn f hU hloc hR

/-- Adding a constant to a stopping time. -/
theorem isStoppingTime_add_nnreal (f : Filtration ℝ≥0 m) {R : Ω → WithTop ℝ≥0}
    (hR : IsStoppingTime f R) (c : ℝ≥0) :
    IsStoppingTime f (fun ω => R ω + (c : WithTop ℝ≥0)) := by
  intro j
  by_cases hcj : c ≤ j
  · have : {ω | R ω + (c : WithTop ℝ≥0) ≤ (j : WithTop ℝ≥0)} = {ω | R ω ≤ ((j - c : ℝ≥0) : WithTop ℝ≥0)} := by
      ext ω
      simp only [mem_ofPred_eq]
      cases hr : R ω with
      | top =>
        rw [WithTop.top_add]
        exact ⟨fun h => absurd h (WithTop.not_top_le_coe _),
          fun h => absurd h (WithTop.not_top_le_coe _)⟩
      | coe a =>
        rw [← WithTop.coe_add, WithTop.coe_le_coe, WithTop.coe_le_coe]
        rw [le_tsub_iff_right hcj]
    rw [this]
    exact f.mono (tsub_le_self) _ (hR (j - c))
  · have : {ω | R ω + (c : WithTop ℝ≥0) ≤ (j : WithTop ℝ≥0)} = ∅ := by
      ext ω
      simp only [mem_ofPred_eq, mem_empty_iff_false, iff_false, not_le]
      refine lt_of_lt_of_le ?_ le_add_self
      exact WithTop.coe_lt_coe.2 (not_le.1 hcj)
    rw [this]
    exact @MeasurableSet.empty _ (f j)

/-- A set defined by a predicate of the value of a path with finitely many events (in the
truncated form) is locally of type `[l, r)`. -/
theorem isLocIco_path_pred_fin {w : ℝ → Fin d → ℤ} {α : ℝ → ℝ} (h : StepEventsFinite w α)
    (P : (Fin d → ℤ) → Prop) : IsLocIco {r | P (w r)} := by
  refine isLocIco_of_pieces fun M => ?_
  obtain ⟨E, h0, hpos, htop, hc⟩ := h.const_form M
  exact ⟨E, h0, hpos, htop, fun a b ha hab hno => by
    simp only [mem_ofPred_eq]
    rw [(hc a b ha hab hno).1]⟩

/-- A set defined by a predicate of the value of a path with locally finite events is locally
of type `[l, r)`. -/
theorem isLocIco_path_pred {w : ℝ → Fin d → ℤ} {α : ℝ → ℝ} (h : StepEventsFiniteW w α)
    (P : (Fin d → ℤ) → Prop) : IsLocIco {r | P (w r)} := by
  intro M
  have ht := h.trunc (max M 0) (le_max_right _ _)
  obtain ⟨L, hL, hLe⟩ := isLocIco_path_pred_fin ht P M
  refine ⟨L, hL, ?_⟩
  rw [← hLe]
  ext r
  simp only [mem_inter_iff, mem_Icc, mem_ofPred_eq]
  constructor
  · rintro ⟨hr, h1, h2⟩
    exact ⟨by rwa [min_eq_left (h2.trans (le_max_left _ _))], h1, h2⟩
  · rintro ⟨hr, h1, h2⟩
    exact ⟨by rwa [min_eq_left (h2.trans (le_max_left _ _))] at hr, h1, h2⟩

end ElboimSly.Paper.Step

end

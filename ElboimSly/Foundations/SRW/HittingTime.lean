/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Foundations.SRW.StoppedPosition
public import ElboimSly.Foundations.SRW.CountableReduction
public import Mathlib

/-!
# Hitting times are stopping times

Hitting times and stopped positions (a).
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology

namespace ElboimSly
namespace SRW

variable {d : ℕ} {Ω : Type*} [mΩ : MeasurableSpace Ω] {Z : Ω → PathSpace d}

open Classical in
/-- `τ = inf {s ≥ a : Z(s) ∈ K}` with `inf ∅ = ∞`. -/
noncomputable def hitTime (Z : Ω → PathSpace d) (a : ℝ≥0) (K : Set (Fin d → ℤ)) (ω : Ω) :
    WithTop ℝ≥0 :=
  if ∃ s, a ≤ s ∧ Z ω s ∈ K then ((sInf {s | a ≤ s ∧ Z ω s ∈ K} : ℝ≥0) : WithTop ℝ≥0) else ⊤

theorem hitTime_attained {γ : PathSpace d} (hγ : IsRegularPath γ) {a : ℝ≥0}
    {K : Set (Fin d → ℤ)} (h : ∃ s, a ≤ s ∧ γ s ∈ K) :
    a ≤ sInf {s | a ≤ s ∧ γ s ∈ K} ∧ γ (sInf {s | a ≤ s ∧ γ s ∈ K}) ∈ K := by
  set S : Set ℝ≥0 := {s | a ≤ s ∧ γ s ∈ K} with hS
  have hne : S.Nonempty := h
  have ha : a ≤ sInf S := le_csInf hne fun s hs => hs.1
  refine ⟨ha, ?_⟩
  obtain ⟨δ, hδ, hconst⟩ := hγ (sInf S)
  obtain ⟨s, hs, hlt⟩ := exists_lt_of_csInf_lt hne (lt_add_of_pos_right (sInf S) hδ)
  have := hconst s (csInf_le (OrderBot.bddBelow S) hs) hlt
  rw [← this]
  exact hs.2

omit mΩ in
theorem hitTime_le_iff {a : ℝ≥0} {K : Set (Fin d → ℤ)} (hreg : ∀ ω, IsRegularPath (Z ω)) (ω : Ω)
    (t : ℝ≥0) : hitTime Z a K ω ≤ (t : WithTop ℝ≥0) ↔ ∃ s, a ≤ s ∧ s ≤ t ∧ Z ω s ∈ K := by
  unfold hitTime
  by_cases h : ∃ s, a ≤ s ∧ Z ω s ∈ K
  · rw [ite_eq_left h, WithTop.coe_le_coe]
    obtain ⟨h1, h2⟩ := hitTime_attained (hreg ω) h
    constructor
    · intro hle; exact ⟨_, h1, hle, h2⟩
    · rintro ⟨s, hs1, hs2, hs3⟩
      exact (csInf_le (OrderBot.bddBelow _) (show s ∈ {s | a ≤ s ∧ Z ω s ∈ K} from ⟨hs1, hs3⟩)).trans hs2
  · rw [ite_eq_right h]
    simp only [top_le_iff, WithTop.coe_ne_top, false_iff, not_exists, not_and]
    exact fun s hs1 _ hs3 => h ⟨s, hs1, hs3⟩

/-- Hitting times and stopped positions (a): a hitting time is a stopping time for every filtration to
which `Z` is adapted. -/
theorem isStoppingTime_hitTime {f : Filtration ℝ≥0 mΩ}
    (hadapt : ∀ s t, s ≤ t → Measurable[f t] (fun ω => Z ω s))
    (hreg : ∀ ω, IsRegularPath (Z ω)) (a : ℝ≥0) (K : Set (Fin d → ℤ)) :
    IsStoppingTime f (hitTime Z a K) := by
  intro t
  have e : {ω | hitTime Z a K ω ≤ (t : WithTop ℝ≥0)} = {ω | ∃ s, a ≤ s ∧ s ≤ t ∧ Z ω s ∈ K} := by
    ext ω; exact hitTime_le_iff hreg ω t
  rw [e]
  rcases le_or_gt a t with hat | hat
  · have hcoord : ∀ s, Measurable[f t] fun ω => Z ω (min s t) := fun s =>
      hadapt (min s t) t (min_le_right _ _)
    have := @measurableSet_exists_Icc d Ω (f t) (fun ω s => Z ω (min s t)) hcoord
      (fun ω => (hreg ω).stop t) K a t hat
    have e2 : {ω | ∃ s, a ≤ s ∧ s ≤ t ∧ Z ω s ∈ K} =
        {ω | ∃ s, a ≤ s ∧ s ≤ t ∧ Z ω (min s t) ∈ K} := by
      ext ω
      constructor
      · rintro ⟨s, h1, h2, h3⟩; exact ⟨s, h1, h2, by simpa [min_eq_left h2] using h3⟩
      · rintro ⟨s, h1, h2, h3⟩; exact ⟨s, h1, h2, by simpa [min_eq_left h2] using h3⟩
    rw [e2]; exact this
  · have : {ω | ∃ s, a ≤ s ∧ s ≤ t ∧ Z ω s ∈ K} = ∅ := by
      ext ω
      simp only [mem_ofPred_eq, mem_empty_iff_false, iff_false, not_exists, not_and]
      exact fun s h1 h2 _ => absurd (h1.trans h2) (not_le.2 hat)
    rw [this]; exact @MeasurableSet.empty _ (f t)

end SRW
end ElboimSly

/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Foundations.PPP.Exploration.ProbeRC
import Mathlib

/-!
# Deterministic cell lemmas for the first-point law

First-point law of a deterministic probe, Claims A and B of the proof of (c).

For a regular configuration `ν`, the cell `Δ = D b \ D a` and the event "`D a` is empty and `Δ` carries
exactly one point, lying in `B`" is exactly the event "the first point is in `Δ ∩ B`", up to the event
that `Δ` carries at least two points.
-/

@[expose] public section

open MeasureTheory
open scoped ENNReal NNReal

namespace ElboimSly

variable {S : Type*} [MeasurableSpace S] {μ : Measure S} [SigmaFinite μ] {R : S → ℝ≥0∞} {h : ℝ≥0}
  {ν : Measure S}

theorem measure_region_cell (hR : Measurable R) {a b : ℝ≥0∞} (hab : a ≤ b) :
    ν (probeRegion R b) = ν (probeRegion R a) + ν (probeRegion R b \ probeRegion R a) := by
  have := measure_inter_add_sdiff (μ := ν) (probeRegion R b) (measurableSet_probeRegion hR a)
  rw [Set.inter_eq_right.2 (probeRegion_mono hab)] at this
  exact this.symm

/-- Claim A: the cell event forces `ρ` into the cell. -/
theorem cell_event_imp (hR : Measurable R) (hν : ν ∈ lfSet μ) (hreg : Reg R h Set.univ ν)
    {a b : ℝ≥0} (hah : a < h) (hab : a ≤ b) (hbh : b ≤ h) {B : Set S} (hB : MeasurableSet B)
    (h0 : ν (probeRegion R a) = 0)
    (h1 : ν ((probeRegion R b \ probeRegion R a) ∩ B) = 1)
    (h2 : ν ((probeRegion R b \ probeRegion R a) \ B) = 0) :
    1 ≤ ν (probeRegion R h) ∧ ν (probeRegion R (probeRho μ R h ν)) = 1 ∧
      ν (probeRegion R (probeRho μ R h ν) ∩ B) = 1 ∧ (a : ℝ≥0∞) < probeRho μ R h ν ∧
      probeRho μ R h ν ≤ b := by
  have hab' : (a : ℝ≥0∞) ≤ b := by exact_mod_cast hab
  have hΔ : ν (probeRegion R b \ probeRegion R a) = 1 := by
    have := measure_inter_add_sdiff (μ := ν) (probeRegion R b \ probeRegion R a) hB
    rw [h1, h2, add_zero] at this
    exact this.symm
  have hDb : ν (probeRegion R b) = 1 := by
    rw [measure_region_cell hR hab', h0, hΔ, zero_add]
  have hρb : probeRho μ R h ν ≤ b := by
    rcases lt_or_eq_of_le hbh with hlt | heq
    · exact (probeRho_le_iff hR hν hreg (by exact_mod_cast hlt)).2 hDb.ge
    · exact (probeRho_le_h (μ := μ) (R := R) (h := h) (ν := ν)).trans (by rw [heq])
  have hρa : (a : ℝ≥0∞) < probeRho μ R h ν := by
    by_contra hcon
    push Not at hcon
    have := (probeRho_le_iff hR hν hreg (r := a) (by exact_mod_cast hah)).1 hcon
    rw [h0] at this
    exact absurd this (by simp)
  have hsucc : 1 ≤ ν (probeRegion R h) :=
    hDb.ge.trans (measure_mono (probeRegion_mono (by exact_mod_cast hbh)))
  have hDρ1 : 1 ≤ ν (probeRegion R (probeRho μ R h ν)) := one_le_measure_region hR hν hreg hsucc
  have hDρ : ν (probeRegion R (probeRho μ R h ν)) = 1 :=
    le_antisymm (hDb ▸ measure_mono (probeRegion_mono hρb)) hDρ1
  refine ⟨hsucc, hDρ, ?_, hρa, hρb⟩
  have hsub : probeRegion R (probeRho μ R h ν) \ B ⊆
      probeRegion R a ∪ ((probeRegion R b \ probeRegion R a) \ B) := by
    intro x hx
    by_cases hxa : x ∈ probeRegion R a
    · exact Or.inl hxa
    · exact Or.inr ⟨⟨probeRegion_mono hρb hx.1, hxa⟩, hx.2⟩
  have hz : ν (probeRegion R (probeRho μ R h ν) \ B) = 0 := by
    refine le_antisymm ?_ zero_le
    calc ν _ ≤ ν (probeRegion R a ∪ ((probeRegion R b \ probeRegion R a) \ B)) := measure_mono hsub
      _ ≤ ν (probeRegion R a) + ν ((probeRegion R b \ probeRegion R a) \ B) := measure_union_le _ _
      _ = 0 := by rw [h0, h2, add_zero]
  have := measure_inter_add_sdiff (μ := ν) (probeRegion R (probeRho μ R h ν)) hB
  rw [hz, add_zero, hDρ] at this
  exact this

/-- Claim B: if `ρ` is in the cell and the cell carries fewer than two points, the cell event
holds. -/
theorem cell_event_of_imp (hR : Measurable R) (hν : ν ∈ lfSet μ) (hreg : Reg R h Set.univ ν)
    {a b : ℝ≥0} (hab : a ≤ b) {B : Set S} (hB : MeasurableSet B)
    (hρ1 : ν (probeRegion R (probeRho μ R h ν)) = 1)
    (hρB : ν (probeRegion R (probeRho μ R h ν) ∩ B) = 1)
    (hρa : (a : ℝ≥0∞) < probeRho μ R h ν) (hρb : probeRho μ R h ν ≤ b)
    (hb : ∃ n : ℕ, ν (probeRegion R b) = n)
    (hlt : ν (probeRegion R b \ probeRegion R a) < 2) :
    ν (probeRegion R a) = 0 ∧ ν ((probeRegion R b \ probeRegion R a) ∩ B) = 1 ∧
      ν ((probeRegion R b \ probeRegion R a) \ B) = 0 := by
  have hab' : (a : ℝ≥0∞) ≤ b := by exact_mod_cast hab
  have h0 : ν (probeRegion R a) = 0 := measure_region_eq_zero_of_lt hν hreg hρa
  have hDb : ν (probeRegion R b) = ν (probeRegion R b \ probeRegion R a) := by
    rw [measure_region_cell hR hab', h0, zero_add]
  have hge : 1 ≤ ν (probeRegion R b) :=
    hρ1.symm.le.trans (measure_mono (probeRegion_mono hρb))
  have hΔ : ν (probeRegion R b \ probeRegion R a) = 1 := by
    obtain ⟨n, hn⟩ := hb
    rw [← hDb, hn] at hlt ⊢
    rw [hn] at hge
    have h1 : 1 ≤ n := by exact_mod_cast hge
    have h2 : n < 2 := by exact_mod_cast hlt
    have : n = 1 := by omega
    rw [this]; simp
  have hsub : probeRegion R (probeRho μ R h ν) ∩ B ⊆
      probeRegion R a ∪ ((probeRegion R b \ probeRegion R a) ∩ B) := by
    intro x hx
    by_cases hxa : x ∈ probeRegion R a
    · exact Or.inl hxa
    · exact Or.inr ⟨⟨probeRegion_mono hρb hx.1, hxa⟩, hx.2⟩
  have hge1 : 1 ≤ ν ((probeRegion R b \ probeRegion R a) ∩ B) := by
    calc (1 : ℝ≥0∞) = ν (probeRegion R (probeRho μ R h ν) ∩ B) := hρB.symm
      _ ≤ ν (probeRegion R a ∪ ((probeRegion R b \ probeRegion R a) ∩ B)) := measure_mono hsub
      _ ≤ ν (probeRegion R a) + ν ((probeRegion R b \ probeRegion R a) ∩ B) :=
        measure_union_le _ _
      _ = ν ((probeRegion R b \ probeRegion R a) ∩ B) := by rw [h0, zero_add]
  have hle1 : ν ((probeRegion R b \ probeRegion R a) ∩ B) ≤ 1 :=
    hΔ ▸ measure_mono Set.inter_subset_left
  have hone : ν ((probeRegion R b \ probeRegion R a) ∩ B) = 1 := le_antisymm hle1 hge1
  refine ⟨h0, hone, ?_⟩
  have := measure_inter_add_sdiff (μ := ν) (probeRegion R b \ probeRegion R a) hB
  rw [hone, hΔ] at this
  exact (ENNReal.add_right_inj ENNReal.one_ne_top).1 (this.trans (add_zero 1).symm)

/-- If the first point is in the cell and there are at least two points in `D ρ`, the cell has at
least two points. -/
theorem two_le_cell_of_two_le (hR : Measurable R) (hν : ν ∈ lfSet μ)
    (hreg : Reg R h Set.univ ν) {a b : ℝ≥0}
    (hab : a ≤ b) (hρa : (a : ℝ≥0∞) < probeRho μ R h ν) (hρb : probeRho μ R h ν ≤ b)
    (h2 : 2 ≤ ν (probeRegion R (probeRho μ R h ν))) :
    2 ≤ ν (probeRegion R b \ probeRegion R a) := by
  have hab' : (a : ℝ≥0∞) ≤ b := by exact_mod_cast hab
  have h0 : ν (probeRegion R a) = 0 := measure_region_eq_zero_of_lt hν hreg hρa
  rw [← zero_add (ν (probeRegion R b \ probeRegion R a)), ← h0, ← measure_region_cell hR hab']
  exact h2.trans (measure_mono (probeRegion_mono hρb))

end ElboimSly

/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Foundations.PPP.Finite
public import Mathlib

/-!
# Separating partition sequences and dissecting systems

Separating partition sequences; dissecting systems.

A countable measurable partition of `S` is represented by a measurable map `S → ℕ` (its cells are
the fibres; empty cells are allowed, as in the written proof). A *separating partition sequence* is a
sequence of such maps, each refining the previous one, which separates points. A *dissecting
system* for `(S, μ)` additionally has `μ(Q) < ∞` for every level-`0` cell `Q`.
-/

@[expose] public section

open MeasureTheory
open scoped ENNReal

namespace ElboimSly

variable {S : Type*} [MeasurableSpace S]

/-- Separating partition sequences; dissecting systems: a separating partition sequence (cells are the fibres of
`idx m`). -/
structure SepPartSeq (S : Type*) [MeasurableSpace S] where
  /-- The cell index at level `m`. -/
  idx : ℕ → S → ℕ
  measurable_idx : ∀ m, Measurable (idx m)
  /-- Level `m+1` refines level `m`. -/
  refine : ∀ m x y, idx (m + 1) x = idx (m + 1) y → idx m x = idx m y
  /-- Distinct points are separated at some level. -/
  separate : ∀ x y, x ≠ y → ∃ m, idx m x ≠ idx m y

namespace SepPartSeq

variable (P : SepPartSeq S)

/-- The `i`-th cell of level `m`. -/
def cell (m i : ℕ) : Set S := P.idx m ⁻¹' {i}

/-- The cell of level `m` containing `x`. -/
def cellOf (m : ℕ) (x : S) : Set S := P.idx m ⁻¹' {P.idx m x}

theorem measurableSet_cell (m i : ℕ) : MeasurableSet (P.cell m i) :=
  P.measurable_idx m (measurableSet_singleton i)

theorem measurableSet_cellOf (m : ℕ) (x : S) : MeasurableSet (P.cellOf m x) :=
  P.measurable_idx m (measurableSet_singleton _)

theorem mem_cellOf_self (m : ℕ) (x : S) : x ∈ P.cellOf m x := rfl

theorem idx_eq_of_le {m m' : ℕ} (h : m' ≤ m) {x y : S} (hxy : P.idx m x = P.idx m y) :
    P.idx m' x = P.idx m' y := by
  induction h with
  | refl => exact hxy
  | step _ ih => exact ih (P.refine _ _ _ hxy)

theorem cellOf_antitone (x : S) : Antitone fun m => P.cellOf m x := by
  intro m m' h y hy
  exact P.idx_eq_of_le h hy

theorem iInter_cellOf (P : SepPartSeq S) (x : S) : ⋂ m, P.cellOf m x = {x} := by
  ext y
  simp only [Set.mem_iInter, Set.mem_singleton_iff]
  constructor
  · intro h
    by_contra hne
    obtain ⟨m, hm⟩ := P.separate y x hne
    exact hm (h m)
  · rintro rfl m; rfl

theorem measurableSet_singleton' (P : SepPartSeq S) (x : S) : MeasurableSet ({x} : Set S) := by
  rw [← P.iInter_cellOf x]
  exact MeasurableSet.iInter fun m => P.measurableSet_cellOf m x

theorem cell_eq_cellOf {m i : ℕ} {x : S} (hx : x ∈ P.cell m i) : P.cell m i = P.cellOf m x := by
  have : P.idx m x = i := hx
  simp [cell, cellOf, this]

/-- Every cell of level `m` is contained in a cell of level `0`. -/
theorem cell_subset_cell_zero {m i : ℕ} {x : S} (hx : x ∈ P.cell m i) :
    P.cell m i ⊆ P.cell 0 (P.idx 0 x) := by
  intro y hy
  have h1 : P.idx m y = P.idx m x := by
    have : P.idx m y = i := hy
    have : P.idx m x = i := hx
    simp_all
  exact (P.idx_eq_of_le (Nat.zero_le m) h1)

/-- A dissecting system for `(S, μ)`: every level-`0` cell has finite mass. -/
def IsDissecting (μ : Measure S) : Prop := ∀ i, μ (P.cell 0 i) < ∞

theorem IsDissecting.measure_cell_lt_top {μ : Measure S} (h : P.IsDissecting μ) (m i : ℕ) :
    μ (P.cell m i) < ∞ := by
  by_cases hne : (P.cell m i).Nonempty
  · obtain ⟨x, hx⟩ := hne
    exact lt_of_le_of_lt (measure_mono (P.cell_subset_cell_zero hx)) (h _)
  · rw [Set.not_nonempty_iff_eq_empty.1 hne, measure_empty]; exact ENNReal.zero_lt_top

end SepPartSeq

end ElboimSly

/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Foundations.Interchange.RingSplit
import Mathlib

/-!
# Symmetries preserve good configurations

Symmetries preserve good configurations.

Lattice automorphisms, rotations of the circle and the reflection of the circle map good
configurations to good configurations.
-/

@[expose] public section

open MeasureTheory

namespace ElboimSly.Interchange

variable {d : ℕ} {β : ℝ} [Fact (0 < β)] {ν : Measure (RingSpace d β)}

omit [Fact (0 < β)] in
theorem goodG3_iff {μ : Measure (RingSpace d β)} :
    GoodG3 μ ↔ ∀ (j : ℤ) (y : Fin d → ℤ),
      StartFree μ (ringWindow β j) y ∧ EndFree μ (ringWindow β j) y := by
  constructor
  · intro h j y
    obtain ⟨n, h1, h2⟩ := h y j
    exact ⟨⟨n, noPathFrom_iff.mpr h1⟩, ⟨n, noPathTo_iff.mpr h2⟩⟩
  · intro h y j
    obtain ⟨⟨n, h1⟩, ⟨n', h2⟩⟩ := h j y
    refine ⟨max n n', noPathFrom_iff.mp ?_, noPathTo_iff.mp ?_⟩
    · exact fun ⟨v, t, hv, hp⟩ => h1 ⟨v, t, hv, hp.truncate (le_max_left _ _)⟩
    · rintro ⟨v, t, hv, hp⟩
      have hs := hp.suffix (max n n' - n')
      rw [show max n n' - (max n n' - n') = n' by omega] at hs
      refine h2 ⟨fun i => v (i + (max n n' - n')), fun i => t (i + (max n n' - n')), ?_, hs⟩
      simp only []
      rw [show n' + (max n n' - n') = max n n' by omega]
      exact hv

omit [Fact (0 < β)] in
/-- Lattice automorphisms preserve good configurations. Symmetries preserve good configurations. -/
theorem good_latticeMeasure (g : LatticeAut d) (hν : Good ν) : Good (latticeMeasure g ν) := by
  refine good_ringPush_of_g3 _ _ hν ?_
  have h3 := goodG3_iff.mp hν.2.2.2
  refine goodG3_iff.mpr fun j y => ?_
  obtain ⟨⟨n, h1⟩, ⟨n', h2⟩⟩ := h3 j (g.toEquiv.symm y)
  refine ⟨⟨n, ?_⟩, ⟨n', ?_⟩⟩
  · rintro ⟨v, t, hv, hp⟩
    exact h1 ⟨_, t, by simp [hv], hp.lattice g⟩
  · rintro ⟨v, t, hv, hp⟩
    exact h2 ⟨_, t, by simp [hv], hp.lattice g⟩

omit [Fact (0 < β)] in
/-- The reflection of the circle preserves good configurations. Symmetries preserve good configurations. -/
theorem good_reflectMeasure (hν : Good ν) : Good (reflectMeasure β ν) := by
  refine good_ringPush_of_g3 _ _ hν ?_
  have h3 := goodG3_iff.mp hν.2.2.2
  refine goodG3_iff.mpr fun j y => ?_
  obtain ⟨⟨n, h1⟩, ⟨n', h2⟩⟩ := h3 (-j - 2) y
  refine ⟨⟨n', noPathFrom_reflect ?_⟩, ⟨n, noPathTo_reflect ?_⟩⟩
  · rw [neg_ringWindow]; exact h2
  · rw [neg_ringWindow]; exact h1

/-- Rotations of the circle preserve good configurations. Symmetries preserve good configurations. -/
theorem good_rotateMeasure (r : ℝ) (hν : Good ν) : Good (rotateMeasure r ν) := by
  refine good_ringPush_of_g3 _ _ hν ?_
  have h3 := goodG3_iff.mp hν.2.2.2
  have hS := fun j y => (h3 j y).1
  have hE := fun j y => (h3 j y).2
  refine goodG3_iff.mpr fun j y => ?_
  have hsub : ∀ u, u + r ∈ ringWindow β j →
      u ∈ Set.Icc ((j : ℝ) * β / 4 - r) ((j : ℝ) * β / 4 - r + β / 2) := fun u hu => by
    unfold ringWindow at hu
    constructor <;> linarith [hu.1, hu.2]
  obtain ⟨n, hn⟩ := startFree_Icc hS ((j : ℝ) * β / 4 - r) y
  obtain ⟨n', hn'⟩ := endFree_Icc hE ((j : ℝ) * β / 4 - r) y
  refine ⟨⟨n, ?_⟩, ⟨n', ?_⟩⟩
  · rintro ⟨v, t, hv, hp⟩
    exact hn ⟨v, _, hv, (hp.rotate r).mono fun i _ hi => hsub _ hi⟩
  · rintro ⟨v, t, hv, hp⟩
    exact hn' ⟨v, _, hv, (hp.rotate r).mono fun i _ hi => hsub _ hi⟩

end ElboimSly.Interchange

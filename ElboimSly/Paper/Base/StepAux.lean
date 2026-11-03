/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Paper.Base.Progressive
public import ElboimSly.Paper.Base.StepPath
public import Mathlib

/-!
# Elementary facts about step paths

Supports regular functionals of pairs of paths.  For a step path `g : ℝ≥0 → V`:

* `measurable_of_rc`: `g` is measurable (for countable discrete `V`);
* `finite_image_Iic`: `g` takes finitely many values on `[0, L]`;
* `discCount`, `discCount_eq_iff`: the number of discontinuities in `(0, s]` is monotone and
  `g` is constant on its fibres.
-/

@[expose] public section

open MeasureTheory Set Filter Topology
open scoped ENNReal NNReal

namespace ElboimSly.Paper.Base

open ElboimSly.Cyclic

variable {V : Type*}

/-- A right-continuous function into a countable discrete space is measurable. -/
theorem measurable_of_rc [MeasurableSpace V] [Countable V] [MeasurableSingletonClass V]
    {g : ℝ≥0 → V} (hrc : ∀ s, ∀ᶠ u in 𝓝[≥] s, g u = g s) : Measurable g := by
  have hm : ∀ m : ℕ, Measurable fun s : ℝ≥0 => g (dyUp m s) := by
    intro m
    have h1 : Measurable fun s : ℝ≥0 => ⌈s * 2 ^ m⌉₊ :=
      Nat.measurable_ceil.comp (measurable_id.mul_const _)
    have h2 : Measurable fun j : ℕ => g ((j : ℝ≥0) / 2 ^ m) := measurable_from_nat
    exact h2.comp h1
  refine measurable_to_countable' fun v => ?_
  have : g ⁻¹' {v} = ⋃ M : ℕ, ⋂ m : ℕ, ⋂ (_ : M ≤ m), (fun s => g (dyUp m s)) ⁻¹' {v} := by
    ext s
    simp only [mem_preimage, mem_singleton_iff, mem_iUnion, mem_iInter]
    obtain ⟨m0, hm0⟩ := exists_plateau hrc s
    have key : ∀ m, m0 ≤ m → g (dyUp m s) = g s := fun m hm =>
      hm0 m hm _ (le_dyUp m s) le_rfl
    constructor
    · intro hv
      exact ⟨m0, fun m hm => (key m hm).trans hv⟩
    · rintro ⟨M, hM⟩
      rw [← key (max M m0) (le_max_right _ _)]
      exact hM _ (le_max_left _ _)
  rw [this]
  exact MeasurableSet.iUnion fun M => MeasurableSet.iInter fun m => MeasurableSet.iInter fun _ =>
    hm m (measurableSet_singleton v)

/-- The number of discontinuities in `(0, s]`. -/
noncomputable def discCount (g : ℝ≥0 → V) (s : ℝ≥0) : ℕ := (CDisc g ∩ Iic s).ncard

/-- A step path takes finitely many values on `[0, L]`. -/
theorem finite_image_Iic {g : ℝ≥0 → V} (hg : IsStepPath g) (L : ℝ≥0) : (g '' Iic L).Finite := by
  have hfin : (g '' (CDisc g ∩ Iic L)).Finite := (hg.fin L).image g
  refine ((hfin.insert (g 0))).subset ?_
  rintro _ ⟨s, hs, rfl⟩
  by_cases hne : (CDisc g ∩ Iic s).Nonempty
  · right
    classical
    have hF : (CDisc g ∩ Iic s).Finite := hg.fin s
    set r := hF.toFinset.max' (by simpa using hne) with hr
    have hrmem : r ∈ CDisc g ∩ Iic s := by
      simpa using hF.toFinset.max'_mem (by simpa using hne)
    refine ⟨r, ⟨hrmem.1, hrmem.2.trans hs⟩, ?_⟩
    refine (eq_of_no_disc hg.rc hrmem.2 fun x hx hd => ?_).symm
    have : x ∈ hF.toFinset := by simpa using ⟨hd, hx.2⟩
    exact absurd (hF.toFinset.le_max' x this) (not_le.mpr hx.1)
  · left
    refine eq_of_no_disc hg.rc bot_le fun x hx hd => hne ⟨x, hd, hx.2⟩

end ElboimSly.Paper.Base

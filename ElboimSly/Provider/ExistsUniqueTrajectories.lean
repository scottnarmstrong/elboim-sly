/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Foundations.Interchange.ForwardExistence
public import ElboimSly.Foundations.Interchange.BackwardExistence
public import ElboimSly.Foundations.Interchange.Uniqueness
public import ElboimSly.Frozen.Defs.EdgeInstMeasurableSpace
public import ElboimSly.Frozen.Defs.Good
public import ElboimSly.Frozen.Defs.IsBackwardTrajectory
public import ElboimSly.Frozen.Defs.IsForwardTrajectory
public import ElboimSly.Frozen.Defs.RingSpace

/-!
# Provider for `ExistsUniqueTrajectories`

Proof of the main theorem `ElboimSly.existsUnique_trajectories` (Existence and uniqueness of trajectories).
The binder `ν` is implicit and `hν` is an `autoParam`, so that the statement file proves the theorem
by `by exact ElboimSly.Provider.existsUniqueTrajectories` (its `ν` and `hν` are in context there).
The proposition is the one stated there.
Assembly only: existence from `ElboimSly.Interchange.exists_forwardTrajectory` and
`exists_backwardTrajectory`, uniqueness from `IsForwardTrajectory.unique` and
`IsBackwardTrajectory.unique`.
-/

public section

open MeasureTheory Filter Topology
open scoped ENNReal NNReal

namespace ElboimSly.Provider

variable (d : ℕ) (β : ℝ)
variable [Fact (0 < β)]
variable {d β}

theorem existsUniqueTrajectories {ν : Measure (RingSpace d β)} (hν : Good ν := by assumption) :
    (∀ (x : Fin d → ℤ) (a : ℝ), ∃! γ : ℝ≥0 → Fin d → ℤ, IsForwardTrajectory ν x a γ) ∧
    (∀ (y : Fin d → ℤ) (b : ℝ), ∃! η : ℝ≥0 → Fin d → ℤ, IsBackwardTrajectory ν y b η) :=
  ⟨fun x a => by
    obtain ⟨γ, hγ⟩ := Interchange.exists_forwardTrajectory hν x a
    exact ⟨γ, hγ, fun γ' hγ' => Interchange.IsForwardTrajectory.unique hγ' hγ⟩,
   fun y b => by
    obtain ⟨η, hη⟩ := Interchange.exists_backwardTrajectory hν y b
    exact ⟨η, hη, fun η' hη' => Interchange.IsBackwardTrajectory.unique hν hη' hη⟩⟩

end ElboimSly.Provider

end

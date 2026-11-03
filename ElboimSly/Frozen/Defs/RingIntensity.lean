/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Frozen.Defs.EdgeInstMeasurableSpace
public import ElboimSly.Frozen.Defs.RingSpace
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic
public import Mathlib.MeasureTheory.Measure.Count
public import Mathlib.Data.Sym.Sym2
public import Mathlib.Topology.Algebra.Order.Group
public import Mathlib.Order.Filter.AtTopBot.Basic

/-!
# RingIntensity

Ring configurations.
-/

public section

open MeasureTheory Filter Topology
open scoped ENNReal NNReal

namespace ElboimSly

variable (d : ℕ) (β : ℝ)
variable [Fact (0 < β)]

/-- The intensity `μ_β = # ⊗ Leb_β` on `S_β`; `volume` on `AddCircle β` is Haar measure of total
mass `β`. Ring configurations. -/
@[expose] noncomputable def ringIntensity : Measure (RingSpace d β) :=
  Measure.count.prod (volume : Measure (AddCircle β))

end ElboimSly

end

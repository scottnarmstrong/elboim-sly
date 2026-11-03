/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Frozen.Defs.Edge
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic
public import Mathlib.MeasureTheory.Measure.Count
public import Mathlib.Data.Sym.Sym2
public import Mathlib.Topology.Algebra.Order.Group
public import Mathlib.Order.Filter.AtTopBot.Basic

/-!
# EdgeInstMeasurableSpace

Lattice, norms, edges, boxes, blocks.
-/

public section

open MeasureTheory Filter Topology
open scoped ENNReal NNReal

namespace ElboimSly

namespace Edge

variable {d : ℕ}

/-- All subsets of `Edge d` are measurable (the edge set is countable and discrete). -/
@[instance_reducible, instance, expose] def instMeasurableSpace : MeasurableSpace (Edge d) := ⊤

end Edge

end ElboimSly

end
